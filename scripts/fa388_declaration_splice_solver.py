from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import os
import re
import shutil
import sys
import time
import urllib.error
import urllib.request
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
TOKEN = os.environ.get("GITHUB_TOKEN", "")


def import_base():
    path = ROOT / "scripts" / "fa383_parallel_solver.py"
    spec = importlib.util.spec_from_file_location("fa383_splice_base", path)
    if spec is None or spec.loader is None:
        raise RuntimeError("cannot import fa383_parallel_solver")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


B = import_base()
ERROR_HEADER = B.ERROR_HEADER
DECL_START = re.compile(
    r"^\s*(?:(?:private|public|protected|noncomputable)\s+)*"
    r"(?:theorem|lemma|corollary|def|abbrev|instance|example)\b"
)
TOP_COMMAND = re.compile(
    r"^(?:namespace|section|end|open|attribute|local|scoped|variable|include|omit|"
    r"set_option|theorem|lemma|corollary|def|abbrev|instance|example|structure|class|inductive)\b"
)
FORBIDDEN = {
    "sorry": re.compile(r"\bsorry\b"),
    "admit": re.compile(r"\badmit\b"),
    "axiom": re.compile(r"(?m)^\s*(?:public\s+)?axiom\b"),
    "unsafe": re.compile(r"(?m)^\s*unsafe\b"),
    "native_decide": re.compile(r"\bnative_decide\b"),
    "Lean.ofReduceBool": re.compile(r"\bLean\.ofReduceBool\b"),
}


def model_order(primary: str) -> list[str]:
    candidates = [
        primary,
        "openai/gpt-5",
        "openai/o3",
        "openai/gpt-4.1",
        "openai/gpt-4o",
        "xai/grok-3",
        "deepseek/DeepSeek-V3-0324",
        "mistral-ai/Mistral-Large-2411",
    ]
    result: list[str] = []
    for model in candidates:
        if model and model not in result:
            result.append(model)
    return result


def locate_declaration(lines: list[str], error_line: int) -> tuple[int, int]:
    start = None
    for index in range(error_line, max(0, error_line - 1000), -1):
        if DECL_START.match(lines[index - 1]):
            start = index
            break
    if start is None:
        raise RuntimeError(f"could not locate declaration before line {error_line}")
    end = len(lines)
    for index in range(start + 1, len(lines) + 1):
        line = lines[index - 1]
        if line and not line[0].isspace() and TOP_COMMAND.match(line):
            end = index - 1
            break
    while end >= start and lines[end - 1].strip() == "":
        end -= 1
    return start, end


def extract_first_error(metric, log: str):
    match = next(ERROR_HEADER.finditer(log), None)
    if match is None:
        raise RuntimeError("no parsable Lean error header")
    return match, int(match.group("line"))


def api_search(block: str) -> str:
    return B.exact_api_search(block)


def previous_summaries() -> str:
    chunks = []
    for name in [
        "fa383-aggregate",
        "fa384-aggregate",
        "fa385-aggregate",
        "fa386-aggregate",
        "fa387-aggregate",
    ]:
        for filename in ["AUTHORITATIVE_STATUS.txt", "FINAL_STATUS.json"]:
            path = ROOT / "build-logs" / name / filename
            if path.exists():
                chunks.append(f"===== {path} =====\n{path.read_text(errors='replace')[-6000:]}")
    return "\n".join(chunks)[-18000:]


def prompt_for_declaration(
    metric,
    log: str,
    start: int,
    end: int,
    declaration: str,
    frontier: int,
    feedback: str,
) -> str:
    match, error_line = extract_first_error(metric, log)
    block = B.compiler_block(log, match)
    before = max(1, start - 25)
    after = min(len(TARGET.read_text().splitlines()), end + 25)
    source_lines = TARGET.read_text(encoding="utf-8").splitlines()
    surrounding = "\n".join(
        f"{index}: {source_lines[index - 1]}" for index in range(before, after + 1)
    )
    decl_sha = hashlib.sha256(declaration.encode("utf-8")).hexdigest()
    return "\n".join(
        [
            "Return exactly one JSON object and no Markdown fences or prose.",
            "The JSON schema is:",
            '{"declaration_sha256":"<same hash>","replacement":"<complete Lean declaration text>"}',
            "",
            "You must replace the complete failing declaration while preserving its existing public declaration header exactly.",
            "The declaration name, binders, assumptions, result type, attributes, and mathematical conclusion must not change.",
            "Only its proof/definition body may be repaired; small private helper lemmas are not allowed in this mode because the replacement span is one declaration.",
            "Do not add sorry, admit, axiom, unsafe, native_decide, or Lean.ofReduceBool.",
            "Do not add imports or surrounding namespace commands.",
            "Use Lean 4.33.0-rc1 and the exact current Mathlib APIs shown by compiler/API search.",
            "",
            f"Frontier: {frontier}",
            f"Current source SHA-256: {metric.source_sha256}",
            f"Current metric: exit={metric.exit_code}, errors={metric.errors}, first_line={metric.first_line}",
            f"Declaration SHA-256: {decl_sha}",
            f"Declaration source lines: {start}-{end}",
            f"First error line: {error_line}",
            "",
            "Current complete declaration:",
            "```lean",
            declaration,
            "```",
            "",
            "Exact compiler block:",
            "```text",
            block,
            "```",
            "",
            "Surrounding source context:",
            "```lean",
            surrounding,
            "```",
            "",
            "Exact-checkout API search:",
            api_search(block) or "(no additional exact-name hits)",
            "",
            "Earlier revision feedback for this same declaration:",
            "```text",
            feedback[-16000:],
            "```",
            "",
            "Earlier pass status summaries to avoid repeating:",
            "```text",
            previous_summaries(),
            "```",
        ]
    )


def query(models: list[str], messages: list[dict[str, str]], output: Path, tag: str):
    if not TOKEN:
        raise RuntimeError("GITHUB_TOKEN unavailable")
    failures = []
    for model in models:
        payload = {
            "model": model,
            "temperature": 0.06,
            "max_tokens": 16000,
            "messages": messages,
        }
        req = urllib.request.Request(
            "https://models.github.ai/inference/chat/completions",
            data=json.dumps(payload).encode("utf-8"),
            headers={
                "Authorization": f"Bearer {TOKEN}",
                "Content-Type": "application/json",
                "Accept": "application/vnd.github+json",
                "X-GitHub-Api-Version": "2022-11-28",
                "User-Agent": "primality-sheaf-fa388-splice",
            },
            method="POST",
        )
        try:
            with urllib.request.urlopen(req, timeout=420) as response:
                body = json.load(response)
            content = body["choices"][0]["message"]["content"]
            (output / f"{tag}-{model.replace('/', '-')}.txt").write_text(
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


def parse_json_response(text: str) -> dict[str, str]:
    text = text.strip()
    if text.startswith("```"):
        lines = text.splitlines()
        if lines:
            lines = lines[1:]
        if lines and lines[-1].strip() == "```":
            lines = lines[:-1]
        text = "\n".join(lines)
    start = text.find("{")
    end = text.rfind("}")
    if start < 0 or end < start:
        raise ValueError("model response contains no JSON object")
    data = json.loads(text[start : end + 1])
    if not isinstance(data, dict):
        raise ValueError("response JSON is not an object")
    if not isinstance(data.get("declaration_sha256"), str):
        raise ValueError("missing declaration_sha256")
    if not isinstance(data.get("replacement"), str):
        raise ValueError("missing replacement")
    return data


def replacement_is_safe(old: str, replacement: str) -> tuple[bool, str]:
    old_headers = B.declaration_headers(old)
    new_headers = B.declaration_headers(replacement)
    if old_headers != new_headers:
        return False, f"public declaration header changed: old={old_headers} new={new_headers}"
    code = B.strip_comments_and_strings(replacement)
    counts = {name: len(pattern.findall(code)) for name, pattern in FORBIDDEN.items()}
    if any(counts.values()):
        return False, f"forbidden executable tokens: {counts}"
    if re.search(r"(?m)^\s*(?:public\s+)?import\b", replacement):
        return False, "replacement contains an import"
    return True, "ok"


def splice(lines: list[str], start: int, end: int, replacement: str) -> str:
    replacement_lines = replacement.rstrip("\n").splitlines()
    return "\n".join(lines[: start - 1] + replacement_lines + lines[end:]) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--primary-model", required=True)
    parser.add_argument("--output-dir", required=True)
    parser.add_argument("--max-frontiers", type=int, default=12)
    parser.add_argument("--max-revisions", type=int, default=5)
    args = parser.parse_args()
    output = Path(args.output_dir)
    output.mkdir(parents=True, exist_ok=True)
    models = model_order(args.primary_model)
    metric, log = B.compile_source(output, "baseline", max_errors=120)
    accepted = 0
    history = []

    if metric.exit_code == 0 and metric.errors == 0:
        shutil.copy2(TARGET, output / "best-source.lean")
        (output / "best-metric.json").write_text(json.dumps(metric.__dict__, indent=2))
        (output / "state.json").write_text(json.dumps({"complete_fa": True, "accepted": 0}, indent=2))
        return 0

    for frontier in range(1, args.max_frontiers + 1):
        source_text = TARGET.read_text(encoding="utf-8")
        source_lines = source_text.splitlines()
        _, error_line = extract_first_error(metric, log)
        start, end = locate_declaration(source_lines, error_line)
        declaration = "\n".join(source_lines[start - 1 : end]) + "\n"
        declaration_sha = hashlib.sha256(declaration.encode("utf-8")).hexdigest()
        feedback = ""
        messages = [
            {
                "role": "system",
                "content": "You are a senior Lean/mathlib maintainer. Return one valid JSON object only.",
            },
            {
                "role": "user",
                "content": prompt_for_declaration(
                    metric, log, start, end, declaration, frontier, feedback
                ),
            },
        ]
        improved = None
        outcomes = []
        for revision in range(1, args.max_revisions + 1):
            tag = f"frontier-{frontier:02d}-revision-{revision:02d}"
            try:
                model, response = query(models, messages, output, tag)
                data = parse_json_response(response)
                if data["declaration_sha256"] != declaration_sha:
                    raise ValueError(
                        f"declaration hash mismatch: got {data['declaration_sha256']} expected {declaration_sha}"
                    )
                replacement = data["replacement"]
                safe, reason = replacement_is_safe(declaration, replacement)
                if not safe:
                    raise ValueError(reason)
                candidate_text = splice(source_lines, start, end, replacement)
                original = TARGET.read_bytes()
                TARGET.write_text(candidate_text, encoding="utf-8")
                try:
                    preserved, reason = B.headers_preserved(source_text, candidate_text)
                    if not preserved:
                        raise ValueError("full-file public statement guard: " + reason)
                    candidate_metric, candidate_log = B.compile_source(
                        output,
                        f"{tag}-{model.replace('/', '-')}",
                        max_errors=120,
                    )
                    if candidate_metric.better_than(metric):
                        improved = (
                            TARGET.read_bytes(),
                            candidate_metric,
                            candidate_log,
                            model,
                            revision,
                            start,
                            end,
                        )
                        outcome_feedback = "IMPROVED"
                    else:
                        first = next(ERROR_HEADER.finditer(candidate_log), None)
                        block = (
                            B.compiler_block(candidate_log, first)
                            if first is not None
                            else candidate_log[-12000:]
                        )
                        outcome_feedback = (
                            "The declaration replacement compiled but did not improve the guarded metric. "
                            "Return a corrected complete replacement for the original declaration and preserve the same declaration_sha256.\n"
                            f"Baseline metric: {metric.__dict__}\n"
                            f"Candidate metric: {candidate_metric.__dict__}\n"
                            "Compiler feedback:\n```text\n"
                            + block
                            + "\n```"
                        )
                finally:
                    TARGET.write_bytes(original)
            except Exception as exc:
                model = locals().get("model", args.primary_model)
                outcome_feedback = "Replacement processing failed: " + repr(exc)
            outcomes.append(
                {
                    "revision": revision,
                    "model": model,
                    "feedback": outcome_feedback[-9000:],
                }
            )
            if improved is not None:
                break
            messages.append({"role": "assistant", "content": response if 'response' in locals() else ""})
            messages.append({"role": "user", "content": outcome_feedback})
            feedback += "\n" + outcome_feedback[-10000:]
        record = {
            "frontier": frontier,
            "baseline": metric.__dict__,
            "declaration_lines": [start, end],
            "declaration_sha256": declaration_sha,
            "outcomes": outcomes,
        }
        if improved is None:
            record["result"] = "no improving replacement"
            history.append(record)
            (output / "history.json").write_text(json.dumps(history, indent=2))
            continue
        source, metric, log, model, revision, start, end = improved
        TARGET.write_bytes(source)
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
        shutil.copy2(TARGET, output / "best-source.lean")
        (output / "best-metric.json").write_text(json.dumps(metric.__dict__, indent=2))
        (output / "history.json").write_text(json.dumps(history, indent=2))
        print(
            f"[fa388] accepted frontier={frontier} lines={start}-{end} "
            f"model={model} revision={revision} metric={metric}"
        )
        if metric.exit_code == 0 and metric.errors == 0:
            break

    if not (output / "best-source.lean").exists():
        shutil.copy2(TARGET, output / "best-source.lean")
    if not (output / "best-metric.json").exists():
        (output / "best-metric.json").write_text(json.dumps(metric.__dict__, indent=2))
    state = {
        "primary_model": args.primary_model,
        "accepted": accepted,
        "complete_fa": metric.exit_code == 0 and metric.errors == 0,
        "metric": metric.__dict__,
    }
    (output / "state.json").write_text(json.dumps(state, indent=2))
    return 0 if state["complete_fa"] else 2


if __name__ == "__main__":
    raise SystemExit(main())
