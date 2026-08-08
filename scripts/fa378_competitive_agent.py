from __future__ import annotations

import hashlib
import importlib.util
import json
import os
import re
import shutil
import subprocess
import sys
import time
import urllib.error
import urllib.request
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
STATE_DIR = ROOT / "build-logs" / "fa378-agent"
TOKEN = os.environ.get("GITHUB_TOKEN", "")
MODELS = [
    item.strip()
    for item in os.environ.get(
        "FA378_MODELS", "openai/gpt-5,openai/gpt-4.1,openai/gpt-4o"
    ).split(",")
    if item.strip()
]
MAX_ROUNDS = int(os.environ.get("FA378_MAX_ROUNDS", "10"))
ERROR_HEADER = re.compile(
    r"(?P<file>[^\n:]*Mock2_FunctionalAnalysis[^\n:]*\.lean):"
    r"(?P<line>\d+):(?P<col>\d+):\s*error:\s*(?P<message>.*)"
)
FORBIDDEN_ADDITION = re.compile(
    r"(?m)^\+.*\b(?:sorry|admit|native_decide|Lean\.ofReduceBool)\b"
    r"|^\+\s*(?:public\s+)?axiom\b|^\+\s*unsafe\b"
)
IMPORT_CHANGE = re.compile(r"(?m)^[+-]\s*(?:public\s+)?import\b")


def load_base_module():
    path = ROOT / "scripts" / "fa377_iterative_agent.py"
    spec = importlib.util.spec_from_file_location("fa377_base", path)
    if spec is None or spec.loader is None:
        raise RuntimeError("cannot import fa377 agent")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


BASE = load_base_module()


@dataclass(frozen=True)
class Metric:
    exit_code: int
    errors: int
    first_line: int | None
    source_sha256: str

    def score(self) -> tuple[int, int, int]:
        return (
            1 if self.exit_code == 0 and self.errors == 0 else 0,
            -self.errors,
            self.first_line if self.first_line is not None else 10**9,
        )

    def better_than(self, other: "Metric") -> bool:
        return self.score() > other.score()


def run(args: list[str], *, input_text: str | None = None, timeout: int | None = None):
    return subprocess.run(
        args,
        cwd=ROOT,
        input=input_text,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=timeout,
        check=False,
    )


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def metric_from_log(exit_code: int, log: str, source: bytes) -> Metric:
    matches = list(ERROR_HEADER.finditer(log))
    return Metric(
        exit_code=exit_code,
        errors=len(matches),
        first_line=int(matches[0].group("line")) if matches else None,
        source_sha256=sha256_bytes(source),
    )


def compile_current(label: str, max_errors: int = 100) -> tuple[Metric, str]:
    proc = run(
        [
            "lake",
            "env",
            "lean",
            f"-DmaxErrors={max_errors}",
            str(TARGET.relative_to(ROOT)),
        ],
        timeout=2100,
    )
    log_path = STATE_DIR / f"{label}.log"
    log_path.write_text(proc.stdout, encoding="utf-8")
    metric = metric_from_log(proc.returncode, proc.stdout, TARGET.read_bytes())
    (STATE_DIR / f"{label}-metric.json").write_text(
        json.dumps(metric.__dict__, indent=2), encoding="utf-8"
    )
    return metric, proc.stdout


def strip_comments_and_strings(text: str) -> str:
    out: list[str] = []
    i = 0
    depth = 0
    in_string = False
    escaped = False
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1
                out.extend("  ")
                i += 2
                continue
            if text.startswith("-/", i):
                depth -= 1
                out.extend("  ")
                i += 2
                continue
            out.append("\n" if text[i] == "\n" else " ")
            i += 1
            continue
        if in_string:
            ch = text[i]
            out.append("\n" if ch == "\n" else " ")
            if escaped:
                escaped = False
            elif ch == "\\":
                escaped = True
            elif ch == '"':
                in_string = False
            i += 1
            continue
        if text.startswith("/-", i):
            depth = 1
            out.extend("  ")
            i += 2
            continue
        if text.startswith("--", i):
            while i < len(text) and text[i] != "\n":
                out.append(" ")
                i += 1
            continue
        if text[i] == '"':
            in_string = True
            out.append(" ")
            i += 1
            continue
        out.append(text[i])
        i += 1
    return "".join(out)


def declaration_headers(text: str) -> dict[str, str]:
    """Fingerprint existing public theorem/lemma/corollary statements up to top-level `:=`."""
    code = strip_comments_and_strings(text)
    start_pattern = re.compile(
        r"(?m)^(?P<indent>\s*)(?P<prefix>(?:(?:public|protected|noncomputable)\s+)*)"
        r"(?P<kind>theorem|lemma|corollary)\s+(?P<name>[^\s(:{\[]+)"
    )
    result: dict[str, str] = {}
    for match in start_pattern.finditer(code):
        prefix = match.group("prefix")
        line_start = code.rfind("\n", 0, match.start()) + 1
        raw_line = code[line_start : code.find("\n", match.start()) if "\n" in code[match.start():] else len(code)]
        is_private = "private" in prefix.split() or raw_line.lstrip().startswith("private ")
        if is_private:
            continue
        i = match.end()
        paren = bracket = brace = 0
        delimiter = None
        while i < len(code):
            ch = code[i]
            if ch == "(": paren += 1
            elif ch == ")": paren = max(0, paren - 1)
            elif ch == "[": bracket += 1
            elif ch == "]": bracket = max(0, bracket - 1)
            elif ch == "{": brace += 1
            elif ch == "}": brace = max(0, brace - 1)
            elif ch == ":" and i + 1 < len(code) and code[i + 1] == "=" and paren == bracket == brace == 0:
                delimiter = i
                break
            i += 1
        if delimiter is None:
            continue
        header = re.sub(r"\s+", " ", code[match.start() : delimiter].strip())
        result[match.group("name")] = header
    return result


def headers_preserved(before: str, after: str) -> tuple[bool, str]:
    old = declaration_headers(before)
    new = declaration_headers(after)
    missing = sorted(set(old) - set(new))
    changed = sorted(name for name in old.keys() & new.keys() if old[name] != new[name])
    if missing or changed:
        return False, f"public statement change: missing={missing[:8]} changed={changed[:8]}"
    return True, "ok"


def source_context(lines: list[str], line: int, before: int = 18, after: int = 28) -> str:
    start = max(1, line - before)
    end = min(len(lines), line + after)
    return "\n".join(f"{i}: {lines[i - 1]}" for i in range(start, end + 1))


def compiler_block(log: str, match: re.Match[str]) -> str:
    tail = log[match.start() :]
    next_match = re.search(
        r"\n[^\n:]*Mock2_FunctionalAnalysis[^\n:]*\.lean:\d+:\d+:\s*error:",
        tail[1:],
    )
    return tail[: next_match.start() + 1 if next_match else 12000]


def relevant_api_search(log: str) -> str:
    tokens: list[str] = []
    for pattern in [
        r"unknown identifier ['`]?([A-Za-z0-9_\.]+)",
        r"invalid field notation.*?([A-Za-z0-9_\.]+)",
        r"has no field ['`]?([A-Za-z0-9_\.]+)",
        r"\b([A-Z][A-Za-z0-9_]+\.[A-Za-z0-9_]+)\b",
    ]:
        tokens.extend(re.findall(pattern, log))
    seen: set[str] = set()
    snippets: list[str] = []
    for token in tokens:
        leaf = token.rsplit(".", 1)[-1]
        if len(leaf) < 4 or leaf in seen:
            continue
        seen.add(leaf)
        proc = run(["rg", "-n", "-m", "8", rf"\b{re.escape(leaf)}\b", "Mathlib", "PrimalitySheafVerification"], timeout=40)
        if proc.stdout.strip():
            snippets.append(f"### Search for `{leaf}`\n```text\n{proc.stdout[:6000]}\n```")
        if len(snippets) >= 8:
            break
    return "\n\n".join(snippets)


def build_prompt(metric: Metric, log: str, round_number: int, previous: str) -> str:
    lines = TARGET.read_text(encoding="utf-8").splitlines()
    matches = []
    seen: set[tuple[int, int, str]] = set()
    for match in ERROR_HEADER.finditer(log):
        key = (int(match.group("line")), int(match.group("col")), match.group("message"))
        if key in seen:
            continue
        seen.add(key)
        matches.append(match)
        if len(matches) >= 10:
            break
    sections = [
        "Return ONLY a unified diff for PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean.",
        "No prose and no Markdown fences.",
        "",
        "The candidate is compiled by Lean 4.33.0-rc1 against the pinned current Mathlib cache.",
        "Existing public theorem/lemma/corollary statement fingerprints are kernel-guarded and must remain byte-equivalent after whitespace normalization.",
        "You may rewrite proof bodies and introduce private helper lemmas, but must not change public names, binders, assumptions, conclusions, or imports.",
        "Never add sorry, admit, native_decide, Lean.ofReduceBool, global axiom, or unsafe.",
        "Fix only common roots represented by the first error clusters. Prefer explicit current APIs, typed calc blocks, extensionality, and small private bridge lemmas.",
        "",
        f"Competitive round: {round_number}",
        f"Source SHA-256: {metric.source_sha256}",
        f"Errors: {metric.errors}; first error line: {metric.first_line}",
    ]
    if previous:
        sections += ["", "Previous agent diagnosis (do not repeat rejected strategies):", "```text", previous[-12000:], "```"]
    for index, match in enumerate(matches, 1):
        line = int(match.group("line"))
        sections += [
            "",
            f"## Error {index} at {line}:{match.group('col')}",
            "```text",
            compiler_block(log, match),
            "```",
            "```lean",
            source_context(lines, line),
            "```",
        ]
    api = relevant_api_search(log)
    if api:
        sections += ["", "Relevant declarations found in this exact checkout:", api]
    return "\n".join(sections)


def query_one(model: str, prompt: str, round_number: int) -> str:
    if not TOKEN:
        raise RuntimeError("GITHUB_TOKEN missing")
    payload = {
        "model": model,
        "temperature": 0.05,
        "max_tokens": 14000,
        "messages": [
            {"role": "system", "content": "Act as a senior Lean/mathlib maintainer. Output a minimal unified diff only."},
            {"role": "user", "content": prompt},
        ],
    }
    req = urllib.request.Request(
        "https://models.github.ai/inference/chat/completions",
        data=json.dumps(payload).encode(),
        headers={
            "Authorization": f"Bearer {TOKEN}",
            "Content-Type": "application/json",
            "Accept": "application/vnd.github+json",
            "X-GitHub-Api-Version": "2022-11-28",
            "User-Agent": "primality-sheaf-fa378-agent",
        },
        method="POST",
    )
    with urllib.request.urlopen(req, timeout=360) as response:
        data = json.load(response)
    content = data["choices"][0]["message"]["content"]
    (STATE_DIR / f"round-{round_number:02d}-{model.replace('/', '-')}.txt").write_text(content, encoding="utf-8")
    return content


def extract_patch(response: str) -> str:
    starts = [pos for pos in (response.find("diff --git "), response.find("--- a/")) if pos >= 0]
    if not starts:
        raise ValueError("no unified diff")
    patch = response[min(starts):]
    fence = patch.find("\n```")
    if fence >= 0:
        patch = patch[:fence] + "\n"
    patch = re.sub(
        r"(?m)^(---|\+\+\+) [ab]/[^\n]*Mock2_FunctionalAnalysis\.lean$",
        lambda m: f"{m.group(1)} {'a' if m.group(1) == '---' else 'b'}/PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean",
        patch,
    )
    return patch


def candidate_from_patch(original: bytes, patch: str, tag: str) -> tuple[bytes, Metric, str]:
    if FORBIDDEN_ADDITION.search(patch):
        raise ValueError("forbidden proof escape")
    if IMPORT_CHANGE.search(patch):
        raise ValueError("import change")
    TARGET.write_bytes(original)
    patch_path = STATE_DIR / f"{tag}.patch"
    patch_path.write_text(patch, encoding="utf-8")
    check = run(["git", "apply", "--check", str(patch_path)])
    if check.returncode != 0:
        raise ValueError("git apply check failed: " + check.stdout[-2500:])
    apply = run(["git", "apply", "--whitespace=nowarn", str(patch_path)])
    if apply.returncode != 0:
        raise ValueError("git apply failed: " + apply.stdout[-2500:])
    after_text = TARGET.read_text(encoding="utf-8")
    preserved, reason = headers_preserved(original.decode("utf-8"), after_text)
    if not preserved:
        raise ValueError(reason)
    metric, log = compile_current(tag)
    return TARGET.read_bytes(), metric, log


def previous_diagnosis() -> str:
    candidates = [
        ROOT / "build-logs" / "fa377-agent" / "persistent-summary.txt",
        ROOT / "build-logs" / "fa377-agent" / "console.log",
    ]
    return "\n".join(path.read_text(encoding="utf-8", errors="replace")[-12000:] for path in candidates if path.exists())


def main() -> int:
    STATE_DIR.mkdir(parents=True, exist_ok=True)
    inherited_marker = ROOT / "build-logs" / "fa377-agent" / "ALL_REQUIRED_TARGETS_2X_PASS"
    if inherited_marker.exists():
        shutil.copy2(inherited_marker, STATE_DIR / "ALL_REQUIRED_TARGETS_2X_PASS")
        return 0
    materialized = ROOT / "build-logs" / "fa377-agent" / "materialized-pass376"
    if not materialized.exists():
        BASE.STATE_DIR.mkdir(parents=True, exist_ok=True)
        BASE.reconstruct_pass376_source()
        materialized.parent.mkdir(parents=True, exist_ok=True)
        materialized.write_text(hashlib.sha256(TARGET.read_bytes()).hexdigest(), encoding="utf-8")
    current_metric, current_log = compile_current("baseline")
    previous = previous_diagnosis()
    accepted = 0
    history: list[dict[str, object]] = []
    if current_metric.exit_code == 0 and current_metric.errors == 0:
        BASE.verify_required_order()
        marker = BASE.STATE_DIR / "ALL_REQUIRED_TARGETS_2X_PASS"
        shutil.copy2(marker, STATE_DIR / "ALL_REQUIRED_TARGETS_2X_PASS")
        return 0
    for round_number in range(1, MAX_ROUNDS + 1):
        original = TARGET.read_bytes()
        prompt = build_prompt(current_metric, current_log, round_number, previous)
        (STATE_DIR / f"round-{round_number:02d}-prompt.md").write_text(prompt, encoding="utf-8")
        candidates: list[tuple[Metric, bytes, str, str]] = []
        outcomes: list[dict[str, object]] = []
        for model in MODELS:
            TARGET.write_bytes(original)
            try:
                response = query_one(model, prompt, round_number)
                patch = extract_patch(response)
                source, metric, log = candidate_from_patch(original, patch, f"round-{round_number:02d}-{model.replace('/', '-')}")
                candidates.append((metric, source, log, model))
                outcomes.append({"model": model, "metric": metric.__dict__, "accepted_for_ranking": True})
            except Exception as exc:
                outcomes.append({"model": model, "exception": repr(exc), "accepted_for_ranking": False})
            finally:
                TARGET.write_bytes(original)
        improving = [item for item in candidates if item[0].better_than(current_metric)]
        record: dict[str, object] = {
            "round": round_number,
            "baseline": current_metric.__dict__,
            "outcomes": outcomes,
        }
        if not improving:
            record["result"] = "no improving candidate"
            history.append(record)
            (STATE_DIR / "history.json").write_text(json.dumps(history, indent=2), encoding="utf-8")
            previous += "\n" + json.dumps(record)[-8000:]
            continue
        best_metric, best_source, best_log, best_model = max(improving, key=lambda item: item[0].score())
        TARGET.write_bytes(best_source)
        current_metric = best_metric
        current_log = best_log
        accepted += 1
        shutil.copy2(TARGET, STATE_DIR / "best-source.lean")
        (STATE_DIR / "best-metric.json").write_text(json.dumps(best_metric.__dict__, indent=2), encoding="utf-8")
        record.update({"result": "accepted", "model": best_model, "metric": best_metric.__dict__})
        history.append(record)
        (STATE_DIR / "history.json").write_text(json.dumps(history, indent=2), encoding="utf-8")
        print(f"[fa378] accepted round {round_number} model={best_model} metric={best_metric}")
        if current_metric.exit_code == 0 and current_metric.errors == 0:
            BASE.verify_required_order()
            marker = BASE.STATE_DIR / "ALL_REQUIRED_TARGETS_2X_PASS"
            shutil.copy2(marker, STATE_DIR / "ALL_REQUIRED_TARGETS_2X_PASS")
            (STATE_DIR / "state.json").write_text(json.dumps({"complete": True, "accepted": accepted, "metric": current_metric.__dict__}, indent=2), encoding="utf-8")
            return 0
    (STATE_DIR / "state.json").write_text(json.dumps({"complete": False, "accepted": accepted, "metric": current_metric.__dict__, "history": history[-3:]}, indent=2), encoding="utf-8")
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
