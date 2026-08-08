from __future__ import annotations

import argparse
import hashlib
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
TOKEN = os.environ.get("GITHUB_TOKEN", "")
ERROR_HEADER = re.compile(
    r"(?P<file>[^\n:]*Mock2_FunctionalAnalysis[^\n:]*\.lean):"
    r"(?P<line>\d+):(?P<col>\d+):\s*error:\s*(?P<message>.*)"
)
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
    input_text: str | None = None,
    timeout: int | None = None,
) -> subprocess.CompletedProcess[str]:
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


def compile_source(
    out_dir: Path,
    label: str,
    max_errors: int = 120,
) -> tuple[Metric, str]:
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
    out_dir.mkdir(parents=True, exist_ok=True)
    (out_dir / f"{label}.log").write_text(proc.stdout, encoding="utf-8")
    metric = metric_from_log(proc.returncode, proc.stdout, TARGET.read_bytes())
    (out_dir / f"{label}-metric.json").write_text(
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
    code = strip_comments_and_strings(text)
    start_pattern = re.compile(
        r"(?m)^(?P<indent>\s*)"
        r"(?P<prefix>(?:(?:private|public|protected|noncomputable)\s+)*)"
        r"(?P<kind>theorem|lemma|corollary)\s+(?P<name>[^\s(:{\[]+)"
    )
    result: dict[str, str] = {}
    for match in start_pattern.finditer(code):
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


def declaration_context(lines: list[str], error_line: int) -> str:
    declaration = re.compile(
        r"^\s*(?:(?:private|public|protected|noncomputable)\s+)*"
        r"(?:theorem|lemma|corollary|def|abbrev|instance|example)\b"
    )
    start = max(1, error_line - 45)
    for index in range(error_line, max(1, error_line - 800), -1):
        if declaration.match(lines[index - 1]):
            start = max(1, index - 10)
            break
    end = min(len(lines), error_line + 180)
    for index in range(error_line + 1, min(len(lines), error_line + 800) + 1):
        if declaration.match(lines[index - 1]):
            end = min(len(lines), index + 8)
            break
    return "\n".join(f"{index}: {lines[index - 1]}" for index in range(start, end + 1))


def compiler_block(log: str, match: re.Match[str], limit: int = 14000) -> str:
    tail = log[match.start() :]
    next_match = re.search(
        r"\n[^\n:]*Mock2_FunctionalAnalysis[^\n:]*\.lean:\d+:\d+:\s*error:",
        tail[1:],
    )
    if next_match:
        return tail[: next_match.start() + 1]
    return tail[:limit]


def exact_api_search(block: str) -> str:
    tokens: list[str] = []
    patterns = [
        r"unknown identifier ['`]?([A-Za-z0-9_\.]+)",
        r"invalid field notation.*?['`]?([A-Za-z0-9_\.]+)",
        r"has no field ['`]?([A-Za-z0-9_\.]+)",
        r"\b([A-Z][A-Za-z0-9_]+\.[A-Za-z0-9_]+)\b",
    ]
    for pattern in patterns:
        tokens.extend(re.findall(pattern, block))
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


def previous_diagnosis() -> str:
    paths = [
        ROOT / "build-logs" / "fa377-agent" / "persistent-summary.txt",
        ROOT / "build-logs" / "fa378-agent" / "persistent-summary.txt",
        ROOT / "build-logs" / "fa379-agent" / "persistent-summary.txt",
        ROOT / "build-logs" / "fa380-agent" / "persistent-summary.txt",
        ROOT / "build-logs" / "fa381-agent" / "persistent-summary.txt",
        ROOT / "build-logs" / "fa382-agent" / "persistent-summary.txt",
    ]
    chunks = []
    for path in paths:
        if path.exists():
            chunks.append(f"===== {path} =====\n{path.read_text(errors='replace')[-7000:]}")
    return "\n".join(chunks)[-20000:]


def strategy_instruction(strategy: str) -> str:
    if strategy == "api":
        return (
            "Prioritize exact current-Mathlib declarations from the API search. Avoid broad simp. "
            "Use explicit named arguments, namespace qualification, change, and extensionality."
        )
    if strategy == "calc":
        return (
            "Prefer a small typed calc proof, explicit coercions, congrArg, ext, or a private bridge lemma. "
            "Normalize only the local expression and avoid changing surrounding abstractions."
        )
    return (
        "Treat this as an interactive compiler dialogue. Repair the common root of the shown goal, "
        "and revise the same patch from exact Lean feedback rather than switching to unrelated tactics."
    )


def build_prompt(
    metric: Metric,
    log: str,
    strategy: str,
    frontier_number: int,
    feedback_history: str,
) -> str:
    match = next(ERROR_HEADER.finditer(log), None)
    if match is None:
        raise RuntimeError("no parsable Lean error header")
    line = int(match.group("line"))
    lines = TARGET.read_text(encoding="utf-8").splitlines()
    block = compiler_block(log, match)
    return "\n".join(
        [
            "Return ONLY a unified diff for PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean.",
            "Do not use Markdown fences and do not add prose.",
            "",
            "Hard constraints:",
            "- Preserve every existing public theorem, lemma, and corollary name, binder, assumption, and conclusion.",
            "- Do not modify imports.",
            "- Do not add sorry, admit, global axiom, unsafe, native_decide, or Lean.ofReduceBool.",
            "- You may rewrite proof bodies and add small private helper lemmas immediately before use.",
            "- The candidate is compiled with Lean 4.33.0-rc1 and the pinned current Mathlib cache.",
            "- Fix exactly the first independent error and any immediate cascade inside the same declaration.",
            "",
            strategy_instruction(strategy),
            "",
            f"Strategy: {strategy}",
            f"Frontier: {frontier_number}",
            f"Source SHA-256: {metric.source_sha256}",
            f"Current metric: exit={metric.exit_code}, errors={metric.errors}, first_line={metric.first_line}",
            "",
            "Compiler block:",
            "```text",
            block,
            "```",
            "",
            "Containing declaration and local source context:",
            "```lean",
            declaration_context(lines, line),
            "```",
            "",
            "Exact checkout API search:",
            exact_api_search(block) or "(no additional exact-name hits)",
            "",
            "Earlier stalled summaries:",
            "```text",
            previous_diagnosis(),
            "```",
            "",
            "Feedback from earlier revisions of this same patch:",
            "```text",
            feedback_history[-16000:],
            "```",
        ]
    )


def query_model(
    models: list[str],
    messages: list[dict[str, str]],
    out_dir: Path,
    tag: str,
) -> tuple[str, str]:
    if not TOKEN:
        raise RuntimeError("GITHUB_TOKEN is unavailable")
    failures: list[str] = []
    for model in models:
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
                "User-Agent": "primality-sheaf-fa383-solver",
            },
            method="POST",
        )
        try:
            with urllib.request.urlopen(request, timeout=420) as response:
                body = json.load(response)
            content = body["choices"][0]["message"]["content"]
            (out_dir / f"{tag}-{model.replace('/', '-')}.txt").write_text(
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
    raise RuntimeError("all models failed: " + " | ".join(failures))


def extract_patch(response: str) -> str:
    starts = [
        position
        for position in (response.find("diff --git "), response.find("--- a/"))
        if position >= 0
    ]
    if not starts:
        raise ValueError("response contains no unified diff")
    patch = response[min(starts) :]
    fence = patch.find("\n```")
    if fence >= 0:
        patch = patch[:fence] + "\n"
    patch = re.sub(
        r"(?m)^(---|\+\+\+) [ab]/[^\n]*Mock2_FunctionalAnalysis\.lean$",
        lambda match: (
            f"{match.group(1)} "
            f"{'a' if match.group(1) == '---' else 'b'}"
            "/PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean"
        ),
        patch,
    )
    return patch


def evaluate_response(
    original: bytes,
    response: str,
    out_dir: Path,
    label: str,
    baseline_metric: Metric,
) -> tuple[bytes | None, Metric | None, str, str]:
    TARGET.write_bytes(original)
    try:
        patch = extract_patch(response)
        patch_path = out_dir / f"{label}.patch"
        patch_path.write_text(patch, encoding="utf-8")
        if FORBIDDEN_ADDITION.search(patch):
            return None, None, "forbidden proof escape in added lines", ""
        if IMPORT_CHANGE.search(patch):
            return None, None, "imports may not be changed", ""
        check = run(["git", "apply", "--check", str(patch_path)], timeout=90)
        if check.returncode != 0:
            return None, None, "git apply --check failed:\n" + check.stdout[-6000:], ""
        apply = run(
            ["git", "apply", "--whitespace=nowarn", str(patch_path)], timeout=90
        )
        if apply.returncode != 0:
            return None, None, "git apply failed:\n" + apply.stdout[-6000:], ""
        after_text = TARGET.read_text(encoding="utf-8")
        preserved, reason = headers_preserved(original.decode("utf-8"), after_text)
        if not preserved:
            return None, None, "public statement fingerprint changed: " + reason, ""
        metric, log = compile_source(out_dir, label, max_errors=120)
        source = TARGET.read_bytes()
        if metric.better_than(baseline_metric):
            return source, metric, "IMPROVED", log
        first = next(ERROR_HEADER.finditer(log), None)
        block = compiler_block(log, first) if first is not None else log[-12000:]
        feedback = (
            "The patch was accepted syntactically but did not improve the guarded Lean metric. "
            "Return a corrected full unified diff against the original baseline source.\n"
            f"Baseline metric: {baseline_metric.__dict__}\n"
            f"Candidate metric: {metric.__dict__}\n"
            "Candidate compiler feedback:\n```text\n"
            + block
            + "\n```"
        )
        return None, metric, feedback, log
    except Exception as exc:
        return None, None, "patch evaluation exception: " + repr(exc), ""
    finally:
        TARGET.write_bytes(original)


def model_order(primary: str) -> list[str]:
    configured = [
        primary,
        "openai/gpt-5",
        "openai/gpt-4.1",
        "openai/gpt-4o",
        "xai/grok-3",
        "deepseek/DeepSeek-V3-0324",
        "mistral-ai/Mistral-Large-2411",
    ]
    result: list[str] = []
    for model in configured:
        if model and model not in result:
            result.append(model)
    return result


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--strategy", required=True, choices=["dialogue", "api", "calc"])
    parser.add_argument("--primary-model", required=True)
    parser.add_argument("--output-dir", required=True)
    parser.add_argument("--max-frontiers", type=int, default=12)
    parser.add_argument("--max-revisions", type=int, default=4)
    args = parser.parse_args()

    out_dir = Path(args.output_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    baseline_headers = declaration_headers(TARGET.read_text(encoding="utf-8"))
    (out_dir / "baseline-public-headers.json").write_text(
        json.dumps(baseline_headers, indent=2, sort_keys=True), encoding="utf-8"
    )

    current_metric, current_log = compile_source(out_dir, "baseline", max_errors=120)
    history: list[dict[str, object]] = []
    accepted = 0
    feedback_history = ""

    if current_metric.exit_code == 0 and current_metric.errors == 0:
        shutil.copy2(TARGET, out_dir / "best-source.lean")
        (out_dir / "best-metric.json").write_text(
            json.dumps(current_metric.__dict__, indent=2), encoding="utf-8"
        )
        (out_dir / "state.json").write_text(
            json.dumps({"complete_fa": True, "accepted": 0}, indent=2),
            encoding="utf-8",
        )
        return 0

    models = model_order(args.primary_model)
    for frontier in range(1, args.max_frontiers + 1):
        original = TARGET.read_bytes()
        prompt = build_prompt(
            current_metric,
            current_log,
            args.strategy,
            frontier,
            feedback_history,
        )
        (out_dir / f"frontier-{frontier:02d}-prompt.md").write_text(
            prompt, encoding="utf-8"
        )
        messages = [
            {
                "role": "system",
                "content": (
                    "You are a senior Lean/mathlib maintainer. "
                    "Return a minimal kernel-checkable unified diff only."
                ),
            },
            {"role": "user", "content": prompt},
        ]
        improved: tuple[bytes, Metric, str, str, int] | None = None
        outcomes: list[dict[str, object]] = []
        for revision in range(1, args.max_revisions + 1):
            tag = f"frontier-{frontier:02d}-revision-{revision:02d}"
            try:
                model, response = query_model(models, messages, out_dir, tag)
            except Exception as exc:
                outcomes.append({"revision": revision, "exception": repr(exc)})
                break
            source, metric, feedback, log = evaluate_response(
                original,
                response,
                out_dir,
                f"{tag}-{model.replace('/', '-')}",
                current_metric,
            )
            outcomes.append(
                {
                    "revision": revision,
                    "model": model,
                    "metric": metric.__dict__ if metric is not None else None,
                    "feedback": feedback[-7000:],
                }
            )
            if source is not None and metric is not None:
                improved = (source, metric, log, model, revision)
                break
            messages.append({"role": "assistant", "content": response})
            messages.append({"role": "user", "content": feedback})
            feedback_history += "\n" + feedback[-9000:]
        record: dict[str, object] = {
            "frontier": frontier,
            "baseline": current_metric.__dict__,
            "outcomes": outcomes,
        }
        if improved is None:
            record["result"] = "no improving dialogue candidate"
            history.append(record)
            (out_dir / "history.json").write_text(
                json.dumps(history, indent=2), encoding="utf-8"
            )
            continue
        source, metric, log, model, revision = improved
        TARGET.write_bytes(source)
        current_metric = metric
        current_log = log
        accepted += 1
        record.update(
            {
                "result": "accepted",
                "model": model,
                "revision": revision,
                "metric": metric.__dict__,
            }
        )
        history.append(record)
        shutil.copy2(TARGET, out_dir / "best-source.lean")
        (out_dir / "best-metric.json").write_text(
            json.dumps(metric.__dict__, indent=2), encoding="utf-8"
        )
        (out_dir / "history.json").write_text(
            json.dumps(history, indent=2), encoding="utf-8"
        )
        print(
            f"[fa383:{args.strategy}] accepted frontier={frontier} "
            f"model={model} revision={revision} metric={metric}"
        )
        if current_metric.exit_code == 0 and current_metric.errors == 0:
            break

    preserved, reason = headers_preserved(
        "\n".join(baseline_headers.values()),
        "\n".join(declaration_headers(TARGET.read_text(encoding="utf-8")).values()),
    )
    # The final source itself is independently checked by the aggregator; this field is diagnostic.
    state = {
        "strategy": args.strategy,
        "primary_model": args.primary_model,
        "accepted": accepted,
        "complete_fa": current_metric.exit_code == 0 and current_metric.errors == 0,
        "metric": current_metric.__dict__,
        "diagnostic_header_guard": {"preserved": preserved, "reason": reason},
    }
    (out_dir / "state.json").write_text(
        json.dumps(state, indent=2), encoding="utf-8"
    )
    if not (out_dir / "best-source.lean").exists():
        shutil.copy2(TARGET, out_dir / "best-source.lean")
    if not (out_dir / "best-metric.json").exists():
        (out_dir / "best-metric.json").write_text(
            json.dumps(current_metric.__dict__, indent=2), encoding="utf-8"
        )
    return 0 if state["complete_fa"] else 2


if __name__ == "__main__":
    raise SystemExit(main())
