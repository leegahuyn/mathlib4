from __future__ import annotations

import argparse
import concurrent.futures
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
TOKEN = os.environ.get("GITHUB_TOKEN", "")


def import_base():
    path = ROOT / "scripts" / "fa383_parallel_solver.py"
    spec = importlib.util.spec_from_file_location("fa383_beam_base", path)
    if spec is None or spec.loader is None:
        raise RuntimeError("cannot import fa383_parallel_solver")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


B = import_base()
DECL_START = re.compile(
    r"^\s*(?:(?:private|public|protected|noncomputable)\s+)*"
    r"(?:theorem|lemma|corollary|def|abbrev|instance|example)\b"
)
TOP_COMMAND = re.compile(
    r"^(?:namespace|section|end|open|attribute|local|scoped|variable|include|omit|"
    r"set_option|theorem|lemma|corollary|def|abbrev|instance|example|structure|class|inductive)\b"
)
GENERIC_ERROR = re.compile(r"[^\n:]*\.lean:(?P<line>\d+):(?P<col>\d+):\s*error:")
FORBIDDEN = {
    "sorry": re.compile(r"\bsorry\b"),
    "admit": re.compile(r"\badmit\b"),
    "axiom": re.compile(r"(?m)^\s*(?:public\s+)?axiom\b"),
    "unsafe": re.compile(r"(?m)^\s*unsafe\b"),
    "native_decide": re.compile(r"\bnative_decide\b"),
    "Lean.ofReduceBool": re.compile(r"\bLean\.ofReduceBool\b"),
}
MODELS = [
    item.strip()
    for item in os.environ.get(
        "FA389_MODELS",
        "openai/gpt-5,openai/o3,openai/gpt-4.1,openai/gpt-4o,xai/grok-3,"
        "deepseek/DeepSeek-V3-0324,mistral-ai/Mistral-Large-2411,"
        "qwen/Qwen3-235B-A22B,microsoft/MAI-DS-R1",
    ).split(",")
    if item.strip()
]
TEMPERATURES = [0.0, 0.08, 0.2]


@dataclass(frozen=True)
class Metric:
    exit_code: int
    errors: int
    first_line: int | None
    normalized_first_line: int | None
    source_sha256: str

    def score(self) -> tuple[int, int, int]:
        return (
            1 if self.exit_code == 0 and self.errors == 0 else 0,
            -self.errors,
            self.normalized_first_line
            if self.normalized_first_line is not None
            else 10**9,
        )

    def better_than(self, old: "Metric") -> bool:
        if self.exit_code == 0 and self.errors == 0:
            return True
        if self.errors < old.errors:
            return True
        return (
            self.errors == old.errors
            and self.normalized_first_line is not None
            and old.normalized_first_line is not None
            and self.normalized_first_line > old.normalized_first_line
        )


def run(args: list[str], *, timeout: int | None = None):
    return subprocess.run(
        args,
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=timeout,
        check=False,
    )


def locate_declaration(lines: list[str], error_line: int) -> tuple[int, int]:
    start = None
    for index in range(error_line, max(0, error_line - 1200), -1):
        if DECL_START.match(lines[index - 1]):
            start = index
            break
    if start is None:
        raise RuntimeError(f"cannot locate declaration before line {error_line}")
    end = len(lines)
    for index in range(start + 1, len(lines) + 1):
        line = lines[index - 1]
        if line and not line[0].isspace() and TOP_COMMAND.match(line):
            end = index - 1
            break
    while end >= start and lines[end - 1].strip() == "":
        end -= 1
    return start, end


def metric_from_log(
    exit_code: int,
    log: str,
    source: bytes,
    start: int = 0,
    delta: int = 0,
) -> Metric:
    matches = list(GENERIC_ERROR.finditer(log))
    first_line = int(matches[0].group("line")) if matches else None
    normalized = first_line
    if first_line is not None and start and first_line > start:
        normalized = first_line - delta
    return Metric(
        exit_code=exit_code,
        errors=len(matches),
        first_line=first_line,
        normalized_first_line=normalized,
        source_sha256=hashlib.sha256(source).hexdigest(),
    )


def compile_file(
    source_path: Path,
    output: Path,
    label: str,
    start: int = 0,
    delta: int = 0,
) -> tuple[Metric, str]:
    proc = run(
        [
            "lake",
            "env",
            "lean",
            "-DmaxErrors=400",
            str(source_path.relative_to(ROOT)),
        ],
        timeout=2700,
    )
    output.mkdir(parents=True, exist_ok=True)
    (output / f"{label}.log").write_text(proc.stdout, encoding="utf-8")
    metric = metric_from_log(proc.returncode, proc.stdout, source_path.read_bytes(), start, delta)
    (output / f"{label}-metric.json").write_text(
        json.dumps(metric.__dict__, indent=2), encoding="utf-8"
    )
    return metric, proc.stdout


def first_error(log: str) -> tuple[re.Match[str], int]:
    match = next(GENERIC_ERROR.finditer(log), None)
    if match is None:
        raise RuntimeError("no parsable Lean error header")
    return match, int(match.group("line"))


def compiler_block(log: str, match: re.Match[str]) -> str:
    tail = log[match.start() :]
    next_match = re.search(r"\n[^\n:]*\.lean:\d+:\d+:\s*error:", tail[1:])
    return tail[: next_match.start() + 1 if next_match else 16000]


def prompt(
    metric: Metric,
    log: str,
    declaration: str,
    start: int,
    end: int,
    frontier: int,
    seed: int,
) -> str:
    match, error_line = first_error(log)
    lines = TARGET.read_text(encoding="utf-8").splitlines()
    around_start = max(1, start - 30)
    around_end = min(len(lines), end + 35)
    surrounding = "\n".join(
        f"{i}: {lines[i - 1]}" for i in range(around_start, around_end + 1)
    )
    block = compiler_block(log, match)
    decl_sha = hashlib.sha256(declaration.encode()).hexdigest()
    return "\n".join(
        [
            "Return only the complete replacement Lean declaration. No prose, no JSON, and no Markdown fences.",
            "",
            "The replacement must preserve the existing declaration header exactly: name, attributes, binders, assumptions, result type, and conclusion.",
            "Only the proof or definition body may change.",
            "Do not add imports, namespaces, sections, sorry, admit, global axiom, unsafe, native_decide, or Lean.ofReduceBool.",
            "Use Lean 4.33.0-rc1 and current Mathlib APIs.",
            "Prefer explicit typed calc/change/ext/simpa proofs and avoid broad simp when it caused the current failure.",
            "",
            f"Beam frontier: {frontier}",
            f"Diversity seed: {seed}",
            f"Current metric: {metric.__dict__}",
            f"Declaration SHA-256: {decl_sha}",
            f"Declaration lines: {start}-{end}",
            f"First error line: {error_line}",
            "",
            "Complete failing declaration:",
            "```lean",
            declaration,
            "```",
            "",
            "Compiler error block:",
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
            B.exact_api_search(block) or "(no additional exact-name hits)",
            "",
            "Earlier pass summaries:",
            "```text",
            B.previous_diagnosis(),
            "```",
        ]
    )


def query_one(model: str, temperature: float, text: str, output: Path, tag: str):
    if not TOKEN:
        raise RuntimeError("GITHUB_TOKEN unavailable")
    payload = {
        "model": model,
        "temperature": temperature,
        "max_tokens": 18000,
        "messages": [
            {
                "role": "system",
                "content": "You are a senior Lean/mathlib maintainer. Return a complete Lean declaration only.",
            },
            {"role": "user", "content": text},
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
            "User-Agent": "primality-sheaf-fa389-beam",
        },
        method="POST",
    )
    with urllib.request.urlopen(req, timeout=480) as response:
        data = json.load(response)
    content = data["choices"][0]["message"]["content"]
    (output / f"{tag}-{model.replace('/', '-')}-t{temperature}.txt").write_text(
        content, encoding="utf-8"
    )
    return model, temperature, content


def clean_response(text: str) -> str:
    text = text.strip()
    if text.startswith("```"):
        lines = text.splitlines()
        lines = lines[1:]
        if lines and lines[-1].strip() == "```":
            lines = lines[:-1]
        text = "\n".join(lines).strip()
    if text.startswith("{") and text.endswith("}"):
        try:
            data = json.loads(text)
            if isinstance(data, dict) and isinstance(data.get("replacement"), str):
                text = data["replacement"].strip()
        except Exception:
            pass
    lines = text.splitlines()
    start = next((i for i, line in enumerate(lines) if DECL_START.match(line)), None)
    if start is not None:
        lines = lines[start:]
    return "\n".join(lines).rstrip() + "\n"


def safe_replacement(old: str, replacement: str) -> tuple[bool, str]:
    old_headers = B.declaration_headers(old)
    new_headers = B.declaration_headers(replacement)
    if old_headers != new_headers:
        return False, f"header mismatch: old={old_headers} new={new_headers}"
    code = B.strip_comments_and_strings(replacement)
    counts = {name: len(pattern.findall(code)) for name, pattern in FORBIDDEN.items()}
    if any(counts.values()):
        return False, f"forbidden tokens: {counts}"
    if re.search(r"(?m)^\s*(?:public\s+)?import\b", replacement):
        return False, "replacement contains import"
    return True, "ok"


def splice(source_lines: list[str], start: int, end: int, replacement: str) -> str:
    return "\n".join(
        source_lines[: start - 1]
        + replacement.rstrip("\n").splitlines()
        + source_lines[end:]
    ) + "\n"


def evaluate_candidate(
    candidate_id: int,
    full_source: str,
    replacement: str,
    old_declaration: str,
    start: int,
    end: int,
    output: Path,
):
    safe, reason = safe_replacement(old_declaration, replacement)
    if not safe:
        return {"candidate_id": candidate_id, "accepted": False, "reason": reason}
    lines = full_source.splitlines()
    candidate_text = splice(lines, start, end, replacement)
    preserved, reason = B.headers_preserved(full_source, candidate_text)
    if not preserved:
        return {
            "candidate_id": candidate_id,
            "accepted": False,
            "reason": "full-file statement guard: " + reason,
        }
    digest = hashlib.sha256(candidate_text.encode()).hexdigest()
    candidate_path = (
        ROOT
        / "PrimalitySheafVerification"
        / f"_FA389Candidate_{candidate_id:03d}_{digest[:12]}.lean"
    )
    candidate_path.write_text(candidate_text, encoding="utf-8")
    replacement_line_count = len(replacement.rstrip("\n").splitlines())
    old_line_count = end - start + 1
    delta = replacement_line_count - old_line_count
    try:
        metric, log = compile_file(
            candidate_path,
            output,
            f"candidate-{candidate_id:03d}",
            start=start,
            delta=delta,
        )
        source_copy = output / f"candidate-{candidate_id:03d}.lean"
        source_copy.write_text(candidate_text, encoding="utf-8")
        return {
            "candidate_id": candidate_id,
            "accepted": True,
            "metric": metric.__dict__,
            "source_path": str(source_copy),
            "replacement_path": str(output / f"replacement-{candidate_id:03d}.lean"),
        }
    except subprocess.TimeoutExpired as exc:
        return {
            "candidate_id": candidate_id,
            "accepted": True,
            "metric": {
                "exit_code": 124,
                "errors": 10**6,
                "first_line": None,
                "normalized_first_line": None,
                "source_sha256": digest,
            },
            "reason": "compile timeout",
        }
    finally:
        candidate_path.unlink(missing_ok=True)
        candidate_path.with_suffix(".olean").unlink(missing_ok=True)
        candidate_path.with_suffix(".ilean").unlink(missing_ok=True)


def result_metric(result: dict) -> Metric | None:
    data = result.get("metric")
    if not isinstance(data, dict):
        return None
    try:
        return Metric(
            exit_code=int(data["exit_code"]),
            errors=int(data["errors"]),
            first_line=int(data["first_line"]) if data.get("first_line") is not None else None,
            normalized_first_line=(
                int(data["normalized_first_line"])
                if data.get("normalized_first_line") is not None
                else None
            ),
            source_sha256=str(data["source_sha256"]),
        )
    except Exception:
        return None


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output-dir", required=True)
    parser.add_argument("--max-frontiers", type=int, default=8)
    parser.add_argument("--beam-size", type=int, default=12)
    parser.add_argument("--query-workers", type=int, default=6)
    parser.add_argument("--compile-workers", type=int, default=2)
    args = parser.parse_args()
    output = Path(args.output_dir)
    output.mkdir(parents=True, exist_ok=True)

    baseline_metric, baseline_log = compile_file(TARGET, output, "baseline")
    current_metric = baseline_metric
    current_log = baseline_log
    accepted_frontiers = 0
    history = []

    if current_metric.exit_code == 0 and current_metric.errors == 0:
        shutil.copy2(TARGET, output / "best-source.lean")
        (output / "best-metric.json").write_text(json.dumps(current_metric.__dict__, indent=2))
        (output / "state.json").write_text(json.dumps({"complete_fa": True, "accepted_frontiers": 0}, indent=2))
        return 0

    for frontier in range(1, args.max_frontiers + 1):
        full_source = TARGET.read_text(encoding="utf-8")
        lines = full_source.splitlines()
        _, error_line = first_error(current_log)
        start, end = locate_declaration(lines, error_line)
        declaration = "\n".join(lines[start - 1 : end]) + "\n"
        prompts = []
        for seed in range(1, args.beam_size + 1):
            prompts.append((seed, prompt(current_metric, current_log, declaration, start, end, frontier, seed)))
        responses = []
        failures = []
        combinations = []
        for index, (seed, prompt_text) in enumerate(prompts):
            model = MODELS[index % len(MODELS)]
            temperature = TEMPERATURES[(index // len(MODELS)) % len(TEMPERATURES)]
            combinations.append((seed, model, temperature, prompt_text))
        with concurrent.futures.ThreadPoolExecutor(max_workers=args.query_workers) as pool:
            future_map = {
                pool.submit(
                    query_one,
                    model,
                    temperature,
                    prompt_text,
                    output,
                    f"frontier-{frontier:02d}-seed-{seed:02d}",
                ): (seed, model, temperature)
                for seed, model, temperature, prompt_text in combinations
            }
            for future in concurrent.futures.as_completed(future_map):
                seed, model, temperature = future_map[future]
                try:
                    returned_model, returned_temp, text = future.result()
                    replacement = clean_response(text)
                    replacement_path = output / f"frontier-{frontier:02d}-seed-{seed:02d}-replacement.lean"
                    replacement_path.write_text(replacement, encoding="utf-8")
                    responses.append((seed, returned_model, returned_temp, replacement))
                except Exception as exc:
                    failures.append({"seed": seed, "model": model, "temperature": temperature, "exception": repr(exc)})
        (output / f"frontier-{frontier:02d}-query-failures.json").write_text(json.dumps(failures, indent=2))

        candidate_results = []
        with concurrent.futures.ThreadPoolExecutor(max_workers=args.compile_workers) as pool:
            future_map = {}
            for candidate_id, (seed, model, temperature, replacement) in enumerate(responses, 1):
                (output / f"replacement-{candidate_id:03d}.lean").write_text(replacement, encoding="utf-8")
                future = pool.submit(
                    evaluate_candidate,
                    candidate_id,
                    full_source,
                    replacement,
                    declaration,
                    start,
                    end,
                    output,
                )
                future_map[future] = (seed, model, temperature)
            for future in concurrent.futures.as_completed(future_map):
                seed, model, temperature = future_map[future]
                result = future.result()
                result.update({"seed": seed, "model": model, "temperature": temperature})
                candidate_results.append(result)
        (output / f"frontier-{frontier:02d}-results.json").write_text(json.dumps(candidate_results, indent=2))

        improving = []
        for result in candidate_results:
            metric = result_metric(result)
            if metric is not None and metric.better_than(current_metric) and result.get("source_path"):
                improving.append((metric, result))
        record = {
            "frontier": frontier,
            "baseline": current_metric.__dict__,
            "declaration_lines": [start, end],
            "query_failures": failures,
            "candidate_results": candidate_results,
        }
        if not improving:
            record["result"] = "no improving beam candidate"
            history.append(record)
            (output / "history.json").write_text(json.dumps(history, indent=2))
            continue
        best_metric, best_result = max(improving, key=lambda item: item[0].score())
        best_source_path = Path(str(best_result["source_path"]))
        shutil.copy2(best_source_path, TARGET)
        current_metric, current_log = compile_file(TARGET, output, f"frontier-{frontier:02d}-accepted")
        accepted_frontiers += 1
        record.update({"result": "accepted", "selected": best_result, "recompiled_metric": current_metric.__dict__})
        history.append(record)
        shutil.copy2(TARGET, output / "best-source.lean")
        (output / "best-metric.json").write_text(json.dumps(current_metric.__dict__, indent=2))
        (output / "history.json").write_text(json.dumps(history, indent=2))
        print(f"[fa389] accepted frontier={frontier} metric={current_metric}")
        if current_metric.exit_code == 0 and current_metric.errors == 0:
            break

    if not (output / "best-source.lean").exists():
        shutil.copy2(TARGET, output / "best-source.lean")
    if not (output / "best-metric.json").exists():
        (output / "best-metric.json").write_text(json.dumps(current_metric.__dict__, indent=2))
    state = {
        "accepted_frontiers": accepted_frontiers,
        "complete_fa": current_metric.exit_code == 0 and current_metric.errors == 0,
        "metric": current_metric.__dict__,
    }
    (output / "state.json").write_text(json.dumps(state, indent=2))
    return 0 if state["complete_fa"] else 2


if __name__ == "__main__":
    raise SystemExit(main())
