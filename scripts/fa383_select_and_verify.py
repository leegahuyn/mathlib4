from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import time
import urllib.error
import urllib.request
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PSV = ROOT / "PrimalitySheafVerification"
FA = PSV / "Mock2_FunctionalAnalysis.lean"
TOKEN = os.environ.get("GITHUB_TOKEN", "")
MODELS = [
    item.strip()
    for item in os.environ.get(
        "FA383_VERIFY_MODELS",
        "openai/gpt-5,openai/gpt-4.1,openai/gpt-4o,xai/grok-3,deepseek/DeepSeek-V3-0324",
    ).split(",")
    if item.strip()
]
FORBIDDEN = {
    "sorry": re.compile(r"\bsorry\b"),
    "admit": re.compile(r"\badmit\b"),
    "global_axiom": re.compile(r"(?m)^\s*(?:public\s+)?axiom\b"),
    "unsafe": re.compile(r"(?m)^\s*unsafe\b"),
    "native_decide": re.compile(r"\bnative_decide\b"),
    "Lean.ofReduceBool": re.compile(r"\bLean\.ofReduceBool\b"),
}
FORBIDDEN_ADDITION = re.compile(
    r"(?m)^\+.*\b(?:sorry|admit|native_decide|Lean\.ofReduceBool)\b"
    r"|^\+\s*(?:public\s+)?axiom\b|^\+\s*unsafe\b"
)
IMPORT_CHANGE = re.compile(r"(?m)^[+-]\s*(?:public\s+)?import\b")


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


def run(
    args: list[str],
    *,
    timeout: int | None = None,
) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        args,
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=timeout,
        check=False,
    )


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


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
    code = strip_comments_and_strings(text)
    pattern = re.compile(
        r"(?m)^(?P<indent>\s*)"
        r"(?P<prefix>(?:(?:private|public|protected|noncomputable)\s+)*)"
        r"(?P<kind>theorem|lemma|corollary)\s+(?P<name>[^\s(:{\[]+)"
    )
    result: dict[str, str] = {}
    for match in pattern.finditer(code):
        if "private" in match.group("prefix").split():
            continue
        i = match.end()
        paren = bracket = brace = 0
        delimiter: int | None = None
        while i < len(code):
            ch = code[i]
            if ch == "(":
                paren += 1
            elif ch == ")":
                paren = max(0, paren - 1)
            elif ch == "[":
                bracket += 1
            elif ch == "]":
                bracket = max(0, bracket - 1)
            elif ch == "{":
                brace += 1
            elif ch == "}":
                brace = max(0, brace - 1)
            elif (
                ch == ":"
                and i + 1 < len(code)
                and code[i + 1] == "="
                and paren == bracket == brace == 0
            ):
                delimiter = i
                break
            i += 1
        if delimiter is None:
            continue
        result[match.group("name")] = re.sub(
            r"\s+", " ", code[match.start() : delimiter].strip()
        )
    return result


def headers_preserved(before: str, after: str) -> tuple[bool, str]:
    old = declaration_headers(before)
    new = declaration_headers(after)
    missing = sorted(set(old) - set(new))
    changed = sorted(name for name in old.keys() & new.keys() if old[name] != new[name])
    if missing or changed:
        return False, f"missing={missing[:10]} changed={changed[:10]}"
    return True, "ok"


def audit_forbidden(path: Path) -> dict[str, int]:
    code = strip_comments_and_strings(path.read_text(encoding="utf-8"))
    return {name: len(pattern.findall(code)) for name, pattern in FORBIDDEN.items()}


def remove_artifacts(path: Path) -> None:
    stem = path.stem
    for candidate in [
        path.with_suffix(".olean"),
        path.with_suffix(".ilean"),
        ROOT
        / ".lake"
        / "build"
        / "lib"
        / "lean"
        / "PrimalitySheafVerification"
        / f"{stem}.olean",
        ROOT
        / ".lake"
        / "build"
        / "lib"
        / "lean"
        / "PrimalitySheafVerification"
        / f"{stem}.ilean",
    ]:
        candidate.unlink(missing_ok=True)


def error_pattern(path: Path) -> re.Pattern[str]:
    return re.compile(
        rf"(?P<file>[^\n:]*{re.escape(path.stem)}[^\n:]*\.lean):"
        r"(?P<line>\d+):(?P<col>\d+):\s*error:\s*(?P<message>.*)"
    )


def metric_from_log(path: Path, exit_code: int, log: str) -> Metric:
    matches = list(error_pattern(path).finditer(log))
    return Metric(
        exit_code=exit_code,
        errors=len(matches),
        first_line=int(matches[0].group("line")) if matches else None,
        source_sha256=sha256_bytes(path.read_bytes()),
    )


def compile_module(
    path: Path,
    evidence: Path,
    label: str,
    max_errors: int = 150,
    clean_target: bool = True,
) -> tuple[Metric, str]:
    if clean_target:
        remove_artifacts(path)
    proc = run(
        [
            "lake",
            "env",
            "lean",
            f"-DmaxErrors={max_errors}",
            str(path.relative_to(ROOT)),
        ],
        timeout=2700,
    )
    evidence.mkdir(parents=True, exist_ok=True)
    (evidence / f"{label}.log").write_text(proc.stdout, encoding="utf-8")
    metric = metric_from_log(path, proc.returncode, proc.stdout)
    (evidence / f"{label}-metric.json").write_text(
        json.dumps(metric.__dict__, indent=2), encoding="utf-8"
    )
    return metric, proc.stdout


def compile_twice(path: Path, evidence: Path, label: str) -> None:
    for run_number in (1, 2):
        metric, log = compile_module(
            path,
            evidence,
            f"{label}-run{run_number}",
            max_errors=200,
            clean_target=True,
        )
        if metric.exit_code != 0 or metric.errors != 0 or "error:" in log:
            raise RuntimeError(
                f"{path.name} direct run {run_number} failed: {metric.__dict__}"
            )


def compiler_block(log: str, pattern: re.Pattern[str]) -> tuple[re.Match[str], str]:
    match = next(pattern.finditer(log), None)
    if match is None:
        raise RuntimeError("no parsable Lean error header")
    tail = log[match.start() :]
    next_match = re.search(
        rf"\n[^\n:]*{re.escape(Path(match.group('file')).stem)}[^\n:]*\.lean:\d+:\d+:\s*error:",
        tail[1:],
    )
    return match, tail[: next_match.start() + 1 if next_match else 14000]


def declaration_context(path: Path, error_line: int) -> str:
    lines = path.read_text(encoding="utf-8").splitlines()
    decl = re.compile(
        r"^\s*(?:(?:private|public|protected|noncomputable)\s+)*"
        r"(?:theorem|lemma|corollary|def|abbrev|instance|example)\b"
    )
    start = max(1, error_line - 45)
    for index in range(error_line, max(1, error_line - 700), -1):
        if decl.match(lines[index - 1]):
            start = max(1, index - 10)
            break
    end = min(len(lines), error_line + 180)
    for index in range(error_line + 1, min(len(lines), error_line + 700) + 1):
        if decl.match(lines[index - 1]):
            end = min(len(lines), index + 8)
            break
    return "\n".join(f"{index}: {lines[index - 1]}" for index in range(start, end + 1))


def api_search(block: str) -> str:
    tokens: list[str] = []
    for regex in [
        r"unknown identifier ['`]?([A-Za-z0-9_\.]+)",
        r"invalid field notation.*?['`]?([A-Za-z0-9_\.]+)",
        r"has no field ['`]?([A-Za-z0-9_\.]+)",
        r"\b([A-Z][A-Za-z0-9_]+\.[A-Za-z0-9_]+)\b",
    ]:
        tokens.extend(re.findall(regex, block))
    snippets: list[str] = []
    seen: set[str] = set()
    for token in tokens:
        leaf = token.rsplit(".", 1)[-1]
        if len(leaf) < 4 or leaf in seen:
            continue
        seen.add(leaf)
        proc = run(
            [
                "rg",
                "-n",
                "-m",
                "10",
                rf"\b{re.escape(leaf)}\b",
                "Mathlib",
                "PrimalitySheafVerification",
            ],
            timeout=45,
        )
        if proc.stdout.strip():
            snippets.append(f"### `{leaf}`\n```text\n{proc.stdout[:8000]}\n```")
        if len(snippets) >= 10:
            break
    return "\n\n".join(snippets)


def query_model(messages: list[dict[str, str]], evidence: Path, tag: str) -> tuple[str, str]:
    if not TOKEN:
        raise RuntimeError("GITHUB_TOKEN is unavailable")
    failures: list[str] = []
    for model in MODELS:
        payload = {
            "model": model,
            "temperature": 0.08,
            "max_tokens": 15000,
            "messages": messages,
        }
        request = urllib.request.Request(
            "https://models.github.ai/inference/chat/completions",
            data=json.dumps(payload).encode("utf-8"),
            headers={
                "Authorization": f"Bearer {TOKEN}",
                "Content-Type": "application/json",
                "Accept": "application/vnd.github+json",
                "X-GitHub-Api-Version": "2022-11-28",
                "User-Agent": "primality-sheaf-fa383-verifier",
            },
            method="POST",
        )
        try:
            with urllib.request.urlopen(request, timeout=420) as response:
                body = json.load(response)
            content = body["choices"][0]["message"]["content"]
            (evidence / f"{tag}-{model.replace('/', '-')}.txt").write_text(
                content, encoding="utf-8"
            )
            return model, content
        except Exception as exc:
            detail = b""
            if isinstance(exc, urllib.error.HTTPError):
                try:
                    detail = exc.read()[:2000]
                except Exception:
                    pass
            failures.append(f"{model}: {exc!r} {detail!r}")
            time.sleep(2)
    raise RuntimeError("all downstream repair models failed: " + " | ".join(failures))


def extract_patch(response: str, path: Path) -> str:
    starts = [
        position
        for position in (response.find("diff --git "), response.find("--- a/"))
        if position >= 0
    ]
    if not starts:
        raise ValueError("no unified diff")
    patch = response[min(starts) :]
    fence = patch.find("\n```")
    if fence >= 0:
        patch = patch[:fence] + "\n"
    relative = str(path.relative_to(ROOT))
    patch = re.sub(
        rf"(?m)^(---|\+\+\+) [ab]/[^\n]*{re.escape(path.name)}$",
        lambda match: (
            f"{match.group(1)} "
            f"{'a' if match.group(1) == '---' else 'b'}/{relative}"
        ),
        patch,
    )
    return patch


def repair_module(path: Path, evidence: Path, max_frontiers: int = 10) -> Metric:
    baseline_headers = declaration_headers(path.read_text(encoding="utf-8"))
    current_metric, current_log = compile_module(
        path, evidence, "repair-baseline", max_errors=120, clean_target=True
    )
    if current_metric.exit_code == 0 and current_metric.errors == 0:
        return current_metric
    history: list[dict[str, object]] = []
    feedback_history = ""
    for frontier in range(1, max_frontiers + 1):
        original = path.read_bytes()
        match, block = compiler_block(current_log, error_pattern(path))
        prompt = "\n".join(
            [
                f"Return ONLY a unified diff for {path.relative_to(ROOT)}.",
                "No prose and no Markdown fences.",
                "",
                "Preserve every existing public theorem/lemma/corollary name, binder, assumption, and conclusion.",
                "Do not change imports. You may rewrite proof bodies and add private helper lemmas.",
                "Never add sorry, admit, global axiom, unsafe, native_decide, or Lean.ofReduceBool.",
                "Repair exactly the first independent Lean error using current Mathlib APIs.",
                "The candidate is compiled immediately; revise from compiler feedback.",
                "",
                f"Module: {path.name}",
                f"Metric: {current_metric.__dict__}",
                "Compiler block:",
                "```text",
                block,
                "```",
                "Containing declaration:",
                "```lean",
                declaration_context(path, int(match.group("line"))),
                "```",
                "Exact checkout API search:",
                api_search(block) or "(no additional hits)",
                "Earlier feedback:",
                "```text",
                feedback_history[-12000:],
                "```",
            ]
        )
        messages = [
            {
                "role": "system",
                "content": "You are a senior Lean/mathlib maintainer. Return a minimal unified diff only.",
            },
            {"role": "user", "content": prompt},
        ]
        accepted: tuple[bytes, Metric, str, str, int] | None = None
        outcomes: list[dict[str, object]] = []
        for revision in range(1, 5):
            tag = f"frontier-{frontier:02d}-revision-{revision:02d}"
            model, response = query_model(messages, evidence, tag)
            path.write_bytes(original)
            try:
                patch = extract_patch(response, path)
                patch_path = evidence / f"{tag}-{model.replace('/', '-')}.patch"
                patch_path.write_text(patch, encoding="utf-8")
                if FORBIDDEN_ADDITION.search(patch):
                    feedback = "Rejected: forbidden proof escape in added lines."
                elif IMPORT_CHANGE.search(patch):
                    feedback = "Rejected: imports may not change."
                else:
                    check = run(["git", "apply", "--check", str(patch_path)], timeout=90)
                    if check.returncode != 0:
                        feedback = "git apply --check failed:\n" + check.stdout[-6000:]
                    else:
                        apply = run(
                            ["git", "apply", "--whitespace=nowarn", str(patch_path)],
                            timeout=90,
                        )
                        if apply.returncode != 0:
                            feedback = "git apply failed:\n" + apply.stdout[-6000:]
                        else:
                            preserved, reason = headers_preserved(
                                original.decode("utf-8"), path.read_text(encoding="utf-8")
                            )
                            if not preserved:
                                feedback = "Rejected by public-statement guard: " + reason
                            else:
                                metric, log = compile_module(
                                    path,
                                    evidence,
                                    f"{tag}-{model.replace('/', '-')}",
                                    max_errors=120,
                                    clean_target=True,
                                )
                                if metric.better_than(current_metric):
                                    accepted = (path.read_bytes(), metric, log, model, revision)
                                    feedback = "IMPROVED"
                                else:
                                    _, candidate_block = compiler_block(
                                        log, error_pattern(path)
                                    )
                                    feedback = (
                                        "Candidate did not improve. Return a corrected full diff against the original baseline.\n"
                                        f"Baseline={current_metric.__dict__}\nCandidate={metric.__dict__}\n"
                                        "Compiler feedback:\n```text\n"
                                        + candidate_block
                                        + "\n```"
                                    )
            except Exception as exc:
                feedback = "Patch evaluation exception: " + repr(exc)
            finally:
                path.write_bytes(original)
            outcomes.append(
                {
                    "revision": revision,
                    "model": model,
                    "feedback": feedback[-7000:],
                }
            )
            if accepted is not None:
                break
            messages.append({"role": "assistant", "content": response})
            messages.append({"role": "user", "content": feedback})
            feedback_history += "\n" + feedback[-9000:]
        record: dict[str, object] = {
            "frontier": frontier,
            "baseline": current_metric.__dict__,
            "outcomes": outcomes,
        }
        if accepted is None:
            record["result"] = "no improving candidate"
            history.append(record)
            (evidence / "repair-history.json").write_text(
                json.dumps(history, indent=2), encoding="utf-8"
            )
            continue
        source, metric, log, model, revision = accepted
        path.write_bytes(source)
        current_metric = metric
        current_log = log
        record.update(
            {
                "result": "accepted",
                "model": model,
                "revision": revision,
                "metric": metric.__dict__,
            }
        )
        history.append(record)
        shutil.copy2(path, evidence / "best-source.lean")
        (evidence / "best-metric.json").write_text(
            json.dumps(metric.__dict__, indent=2), encoding="utf-8"
        )
        (evidence / "repair-history.json").write_text(
            json.dumps(history, indent=2), encoding="utf-8"
        )
        if current_metric.exit_code == 0 and current_metric.errors == 0:
            break
    preserved_final = declaration_headers(path.read_text(encoding="utf-8"))
    missing = sorted(set(baseline_headers) - set(preserved_final))
    changed = sorted(
        name
        for name in baseline_headers.keys() & preserved_final.keys()
        if baseline_headers[name] != preserved_final[name]
    )
    if missing or changed:
        raise RuntimeError(
            f"final statement fingerprint failure for {path.name}: missing={missing[:10]} changed={changed[:10]}"
        )
    return current_metric


def select_fa_candidate(candidates_root: Path, evidence: Path) -> tuple[Path, Metric]:
    baseline_source = FA.read_bytes()
    baseline_metric, _ = compile_module(
        FA, evidence / "baseline", "baseline-fa", max_errors=120, clean_target=True
    )
    options: list[tuple[Metric, Path, str]] = [
        (baseline_metric, FA, "checked-in-baseline")
    ]
    for metric_path in candidates_root.rglob("best-metric.json"):
        source_path = metric_path.with_name("best-source.lean")
        if not source_path.exists():
            continue
        try:
            data = json.loads(metric_path.read_text(encoding="utf-8"))
            metric = Metric(
                exit_code=int(data["exit_code"]),
                errors=int(data["errors"]),
                first_line=(
                    int(data["first_line"])
                    if data.get("first_line") is not None
                    else None
                ),
                source_sha256=str(data["source_sha256"]),
            )
            if sha256_bytes(source_path.read_bytes()) != metric.source_sha256:
                continue
            options.append((metric, source_path, str(metric_path.parent)))
        except Exception:
            continue
    selected_metric, selected_path, selected_label = max(options, key=lambda item: item[0].score())
    if selected_path != FA:
        preserved, reason = headers_preserved(
            baseline_source.decode("utf-8"), selected_path.read_text(encoding="utf-8")
        )
        if not preserved:
            raise RuntimeError(
                f"selected FA candidate changes a public statement: {reason}"
            )
        shutil.copy2(selected_path, FA)
    selection = {
        "selected": selected_label,
        "metric": selected_metric.__dict__,
        "candidate_count": len(options),
        "source_sha256": sha256_bytes(FA.read_bytes()),
    }
    (evidence / "fa-selection.json").write_text(
        json.dumps(selection, indent=2), encoding="utf-8"
    )
    return FA, selected_metric


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--candidates-root", required=True)
    parser.add_argument("--evidence-dir", required=True)
    args = parser.parse_args()
    candidates_root = Path(args.candidates_root)
    evidence = Path(args.evidence_dir)
    evidence.mkdir(parents=True, exist_ok=True)

    select_fa_candidate(candidates_root, evidence)
    fa_counts = audit_forbidden(FA)
    if any(fa_counts.values()):
        raise RuntimeError(f"FA forbidden token audit failed: {fa_counts}")

    try:
        compile_twice(FA, evidence / "fa-2x", "Mock2_FunctionalAnalysis")
    except Exception as exc:
        metric, log = compile_module(
            FA, evidence / "fa-final", "fa-final", max_errors=200, clean_target=True
        )
        (evidence / "FINAL_STATUS.json").write_text(
            json.dumps(
                {
                    "complete": False,
                    "stage": "Mock2_FunctionalAnalysis",
                    "reason": repr(exc),
                    "metric": metric.__dict__,
                },
                indent=2,
            ),
            encoding="utf-8",
        )
        return 2

    downstream: list[Path] = []
    integrated = PSV / "Mock2_FunctionalAnalysis_Integrated.lean"
    if not integrated.exists():
        raise RuntimeError("Mock2_FunctionalAnalysis_Integrated.lean is missing")
    downstream.append(integrated)
    downstream.extend(sorted(PSV.glob("Mock3*.lean")))
    qym = PSV / "QYM.lean"
    if not qym.exists():
        raise RuntimeError("QYM.lean is missing")
    downstream.append(qym)

    module_results: list[dict[str, object]] = []
    for path in downstream:
        module_evidence = evidence / path.stem
        metric, _ = compile_module(
            path,
            module_evidence,
            "initial",
            max_errors=150,
            clean_target=True,
        )
        if metric.exit_code != 0 or metric.errors != 0:
            metric = repair_module(path, module_evidence, max_frontiers=10)
        if metric.exit_code != 0 or metric.errors != 0:
            (evidence / "FINAL_STATUS.json").write_text(
                json.dumps(
                    {
                        "complete": False,
                        "stage": path.name,
                        "metric": metric.__dict__,
                        "completed_modules": module_results,
                    },
                    indent=2,
                ),
                encoding="utf-8",
            )
            return 2
        counts = audit_forbidden(path)
        if any(counts.values()):
            raise RuntimeError(f"{path.name} forbidden token audit failed: {counts}")
        compile_twice(path, module_evidence / "2x", path.stem)
        module_results.append(
            {
                "module": path.name,
                "source_sha256": sha256_bytes(path.read_bytes()),
                "status": "PASSx2",
            }
        )

    marker_text = (
        "Mock2_FunctionalAnalysis=PASSx2\n"
        + "".join(f"{item['module'].removesuffix('.lean')}=PASSx2\n" for item in module_results)
    )
    (evidence / "ALL_REQUIRED_TARGETS_2X_PASS").write_text(
        marker_text, encoding="utf-8"
    )
    final = {
        "complete": True,
        "stage": "ALL_REQUIRED_TARGETS_2X_PASS",
        "fa_source_sha256": sha256_bytes(FA.read_bytes()),
        "modules": module_results,
    }
    (evidence / "FINAL_STATUS.json").write_text(
        json.dumps(final, indent=2), encoding="utf-8"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
