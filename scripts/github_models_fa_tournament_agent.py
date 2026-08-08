from __future__ import annotations

import argparse
import concurrent.futures
import dataclasses
import hashlib
import json
import os
import re
import shutil
import subprocess
import time
import urllib.error
import urllib.request
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
OUT = ROOT / "build-logs" / "fa-tournament-agent"
WORK = OUT / "working.lean"
STATE = OUT / "state.json"
ERR = re.compile(r"^(.*?\.lean):(\d+):(\d+):\s+(?:error[^:]*:|error:)\s*(.*)$")
DECL = re.compile(
    r"^(\s*)(?:(?:private|protected|noncomputable|local|scoped)\s+)*"
    r"(theorem|lemma|corollary|example|instance|def|abbrev|structure|class)\b"
)
FORBIDDEN = re.compile(
    r"(?m)^\s*(?:sorry|admit)\b|(?m)^\s*axiom\b|(?m)^\s*unsafe\b|"
    r"\bnative_decide\b|\bLean\.ofReduceBool\b"
)
IDENT = re.compile(r"\b[A-Za-z_][A-Za-z0-9_'.]{4,}\b")


@dataclasses.dataclass(frozen=True)
class Failure:
    line: int
    col: int
    message: str
    raw: str


@dataclasses.dataclass(frozen=True)
class CandidateResult:
    model: str
    response_file: str
    signature_ok: bool
    forbidden: str | None
    exit_code: int
    elapsed_seconds: float
    error_count: int
    first_error: Failure | None
    source_file: str | None
    signature_log: str
    compile_log: str


def digest(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def strip_comments(text: str) -> str:
    text = re.sub(r"/-.*?-\/", "", text, flags=re.S)
    return re.sub(r"--.*$", "", text, flags=re.M)


def compile_lean(path: Path, max_errors: int, timeout: int) -> tuple[int, str, float]:
    started = time.monotonic()
    try:
        proc = subprocess.run(
            ["lake", "env", "lean", f"-DmaxErrors={max_errors}", str(path)],
            cwd=ROOT,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=timeout,
            env={**os.environ, "LC_ALL": "C.UTF-8"},
        )
        return proc.returncode, proc.stdout, time.monotonic() - started
    except subprocess.TimeoutExpired as exc:
        output = exc.stdout or ""
        if isinstance(output, bytes):
            output = output.decode("utf-8", errors="replace")
        return 124, output + "\nFA_TOURNAMENT_COMPILE_TIMEOUT\n", time.monotonic() - started


def parse_failures(log: str) -> list[Failure]:
    result: list[Failure] = []
    for line in log.splitlines():
        match = ERR.match(line)
        if match:
            result.append(
                Failure(
                    line=int(match.group(2)),
                    col=int(match.group(3)),
                    message=match.group(4),
                    raw=line,
                )
            )
    return result


def declaration_bounds(lines: list[str], line_no: int) -> tuple[int, int] | None:
    starts = [i for i, line in enumerate(lines) if DECL.match(line)]
    preceding = [i for i in starts if i <= line_no - 1]
    if not preceding:
        return None
    start = preceding[-1]
    end = next((i for i in starts if i > start), len(lines))
    return start, end


def clean_response(raw: str) -> list[str]:
    text = raw.strip()
    fence = re.search(r"```(?:lean)?\s*(.*?)```", text, flags=re.S)
    if fence:
        text = fence.group(1).strip()
    # Drop common prose prefixes without touching valid Lean attributes/modifiers.
    lines = text.splitlines()
    while lines and not lines[0].strip():
        lines.pop(0)
    while lines and not lines[-1].strip():
        lines.pop()
    if lines and lines[0].lower().startswith(("here is", "replacement declaration")):
        lines.pop(0)
    return lines


def signature_ok(candidate: Path, baseline: Path) -> tuple[bool, str]:
    proc = subprocess.run(
        [
            "python3",
            str(ROOT / "scripts" / "fa_full_signature_fingerprint.py"),
            str(candidate),
            "--compare",
            str(baseline),
        ],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    return proc.returncode == 0, proc.stdout


def catalog(token: str) -> list[str]:
    request = urllib.request.Request(
        "https://models.github.ai/catalog/models",
        method="GET",
        headers={
            "Authorization": f"Bearer {token}",
            "Accept": "application/json",
            "X-GitHub-Api-Version": "2022-11-28",
        },
    )
    with urllib.request.urlopen(request, timeout=120) as response:
        payload = json.loads(response.read().decode("utf-8"))
    entries = payload if isinstance(payload, list) else payload.get("models", [])
    ids: list[str] = []
    for entry in entries:
        if isinstance(entry, dict):
            model_id = entry.get("id") or entry.get("name") or entry.get("model")
            if isinstance(model_id, str):
                ids.append(model_id)
    return ids


def model_score(model: str) -> tuple[int, str]:
    lower = model.lower()
    preferences = [
        ("gpt-5.2-codex", 1000),
        ("gpt-5.1-codex-max", 990),
        ("gpt-5.1-codex", 980),
        ("gpt-5.3", 975),
        ("gpt-5.2", 970),
        ("gpt-5.1", 960),
        ("gpt-5", 950),
        ("claude-opus-4.6", 945),
        ("claude-opus-4.5", 940),
        ("claude-opus-4.1", 935),
        ("claude-sonnet-4.6", 930),
        ("claude-sonnet-4.5", 925),
        ("gpt-4.1", 900),
        ("gpt-4o", 850),
    ]
    for needle, score in preferences:
        if needle in lower:
            return score, model
    if any(term in lower for term in ("coder", "code", "reason")):
        return 700, model
    return 0, model


def select_models(token: str, limit: int) -> list[str]:
    fallback = [
        "openai/gpt-5.2-codex",
        "openai/gpt-5.1-codex",
        "openai/gpt-5.2",
        "openai/gpt-5.1",
        "openai/gpt-5",
        "anthropic/claude-opus-4.1",
        "openai/gpt-4.1",
        "openai/gpt-4o",
    ]
    try:
        ids = catalog(token)
    except Exception:
        ids = []
    ranked = [model for score, model in sorted((model_score(model) for model in ids), reverse=True) if score > 0]
    selected: list[str] = []
    for model in ranked + fallback:
        if model not in selected:
            selected.append(model)
        if len(selected) >= limit:
            break
    return selected


def invoke(model: str, prompt: str, token: str) -> str:
    endpoint = "https://models.github.ai/inference/chat/completions"
    payload = json.dumps(
        {
            "model": model,
            "temperature": 0,
            "max_tokens": 14000,
            "messages": [
                {
                    "role": "system",
                    "content": (
                        "You are repairing one complete declaration in Lean 4.33.0-rc1 using the pinned current "
                        "Mathlib. Return only the complete replacement declaration, no markdown. Preserve its "
                        "signature exactly: same modifiers, name, binders, type, assumptions and conclusion. Change "
                        "only implementation/proof. Never use sorry, admit, axiom, unsafe, native_decide or "
                        "Lean.ofReduceBool. Do not weaken the result. Prefer explicit current-Mathlib APIs, fully "
                        "qualified lemmas, typed `show`/`change`, `calc`, `convert`, extensionality, and small helper "
                        "facts. Resolve the actual compiler error rather than hiding it with resource limits unless "
                        "the diagnostic itself is a heartbeat limit."
                    ),
                },
                {"role": "user", "content": prompt},
            ],
        }
    ).encode("utf-8")
    request = urllib.request.Request(
        endpoint,
        data=payload,
        method="POST",
        headers={
            "Authorization": f"Bearer {token}",
            "Content-Type": "application/json",
            "Accept": "application/json",
            "X-GitHub-Api-Version": "2022-11-28",
        },
    )
    with urllib.request.urlopen(request, timeout=360) as response:
        data = json.loads(response.read().decode("utf-8"))
    return data["choices"][0]["message"]["content"]


def api_search_context(error_text: str, declaration: str, limit: int = 80) -> str:
    identifiers = []
    for token in IDENT.findall(error_text + "\n" + declaration):
        if token in {"theorem", "lemma", "instance", "variable", "Type", "Prop", "where", "exact", "simp", "rw"}:
            continue
        if token not in identifiers:
            identifiers.append(token)
        if len(identifiers) >= 16:
            break
    snippets: list[str] = []
    roots = [ROOT / "Mathlib", ROOT / "PrimalitySheafVerification"]
    for identifier in identifiers:
        suffix = identifier.rsplit(".", 1)[-1]
        if len(suffix) < 5:
            continue
        try:
            proc = subprocess.run(
                ["rg", "-n", "--glob", "*.lean", "--fixed-strings", suffix, *map(str, roots)],
                cwd=ROOT,
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.DEVNULL,
                timeout=20,
            )
        except (subprocess.TimeoutExpired, FileNotFoundError):
            continue
        matches = proc.stdout.splitlines()[:5]
        if matches:
            snippets.append(f"## matches for {identifier}\n" + "\n".join(matches))
        if sum(item.count("\n") + 1 for item in snippets) >= limit:
            break
    return "\n\n".join(snippets)


def metric(rc: int, errors: list[Failure], cap: int) -> tuple[int, int, int, int]:
    if rc == 0 and not errors:
        return (-1, -10**9, -10**9, -10**9)
    first_line = errors[0].line if errors else 0
    distinct = len({error.line for error in errors})
    messages = len({error.message for error in errors})
    return (min(len(errors), cap), -first_line, -distinct, -messages)


def improves(old_rc: int, old: list[Failure], new_rc: int, new: list[Failure], cap: int) -> bool:
    if new_rc == 0 and not new:
        return True
    if not old or not new:
        return False
    if new[0].line > old[0].line + 2:
        return True
    return metric(new_rc, new, cap) < metric(old_rc, old, cap)


def candidate_score(result: CandidateResult, cap: int) -> tuple[int, int, int, int, float]:
    errors = [] if result.first_error is None else [result.first_error]
    # Prefer actual pass, then later first error, then fewer error headers, then faster compile.
    if result.exit_code == 0 and result.first_error is None:
        return (-1, -10**9, -result.error_count, 0, result.elapsed_seconds)
    line = result.first_error.line if result.first_error else 0
    return (min(result.error_count, cap), -line, 0, 0, result.elapsed_seconds)


def evaluate_candidate(
    index: int,
    model: str,
    raw: str,
    lines: list[str],
    start: int,
    end: int,
    baseline: Path,
    max_errors: int,
    timeout: int,
) -> CandidateResult:
    safe_model = re.sub(r"[^A-Za-z0-9_.-]+", "_", model)
    response_file = OUT / f"candidate-{index}-{safe_model}.response.txt"
    response_file.write_text(raw, encoding="utf-8")
    replacement = clean_response(raw)
    candidate_lines = lines[:start] + replacement + lines[end:]
    candidate_text = "\n".join(candidate_lines) + "\n"
    bad_match = FORBIDDEN.search(strip_comments(candidate_text))
    if bad_match:
        return CandidateResult(
            model=model,
            response_file=str(response_file),
            signature_ok=False,
            forbidden=bad_match.group(0),
            exit_code=98,
            elapsed_seconds=0,
            error_count=10**6,
            first_error=None,
            source_file=None,
            signature_log="",
            compile_log="",
        )
    candidate = OUT / f"candidate-{index}-{safe_model}.lean"
    candidate.write_text(candidate_text, encoding="utf-8")
    ok, guard_log = signature_ok(candidate, baseline)
    guard_path = OUT / f"candidate-{index}-{safe_model}.signature.log"
    guard_path.write_text(guard_log, encoding="utf-8")
    if not ok:
        return CandidateResult(
            model=model,
            response_file=str(response_file),
            signature_ok=False,
            forbidden=None,
            exit_code=97,
            elapsed_seconds=0,
            error_count=10**6,
            first_error=None,
            source_file=str(candidate),
            signature_log=str(guard_path),
            compile_log="",
        )
    rc, log, elapsed = compile_lean(candidate, max_errors, timeout)
    log_path = OUT / f"candidate-{index}-{safe_model}.log"
    log_path.write_text(log, encoding="utf-8")
    errs = parse_failures(log)
    return CandidateResult(
        model=model,
        response_file=str(response_file),
        signature_ok=True,
        forbidden=None,
        exit_code=rc,
        elapsed_seconds=elapsed,
        error_count=len(errs),
        first_error=errs[0] if errs else None,
        source_file=str(candidate),
        signature_log=str(guard_path),
        compile_log=str(log_path),
    )


def write_state(payload: dict[str, Any]) -> None:
    OUT.mkdir(parents=True, exist_ok=True)
    STATE.write_text(json.dumps(payload, indent=2, ensure_ascii=False), encoding="utf-8")


def result_json(result: CandidateResult) -> dict[str, Any]:
    payload = dataclasses.asdict(result)
    if result.first_error is not None:
        payload["first_error"] = dataclasses.asdict(result.first_error)
    return payload


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--seed", type=Path, default=TARGET)
    parser.add_argument("--baseline", type=Path, required=True)
    parser.add_argument("--rounds", type=int, default=10)
    parser.add_argument("--models", type=int, default=4)
    parser.add_argument("--max-errors", type=int, default=60)
    parser.add_argument("--compile-timeout", type=int, default=1500)
    parser.add_argument("--materialize-progress", action="store_true")
    args = parser.parse_args()

    token = os.environ.get("GITHUB_TOKEN") or os.environ.get("GH_TOKEN")
    if not token:
        raise SystemExit("GITHUB_TOKEN is required")
    OUT.mkdir(parents=True, exist_ok=True)
    shutil.copy2(args.seed, WORK)
    models = select_models(token, args.models)
    (OUT / "selected-models.json").write_text(json.dumps(models, indent=2), encoding="utf-8")
    history: list[dict[str, Any]] = []
    any_progress = False

    for round_no in range(1, args.rounds + 1):
        text = WORK.read_text(encoding="utf-8")
        rc, log, elapsed = compile_lean(WORK, args.max_errors, args.compile_timeout)
        (OUT / f"round-{round_no}-before.log").write_text(log, encoding="utf-8")
        current_errors = parse_failures(log)
        entry: dict[str, Any] = {
            "round": round_no,
            "input_sha256": digest(text),
            "input_exit": rc,
            "input_elapsed_seconds": elapsed,
            "input_error_count": len(current_errors),
            "input_first_error": dataclasses.asdict(current_errors[0]) if current_errors else None,
            "models": models,
        }
        history.append(entry)
        write_state({"status": "running", "history": history})
        print(json.dumps(entry, ensure_ascii=False), flush=True)

        if rc == 0 and not current_errors:
            rc2, log2, elapsed2 = compile_lean(WORK, 2000, args.compile_timeout)
            (OUT / "compile-second.log").write_text(log2, encoding="utf-8")
            second = parse_failures(log2)
            result = {
                "status": "pass" if rc2 == 0 and not second else "second-run-failed",
                "sha256": digest(text),
                "first_exit": rc,
                "second_exit": rc2,
                "second_elapsed_seconds": elapsed2,
                "second_first_error": dataclasses.asdict(second[0]) if second else None,
                "history": history,
            }
            write_state(result)
            if result["status"] == "pass":
                shutil.copy2(WORK, OUT / "Mock2_FunctionalAnalysis.PASS.lean")
                if args.materialize_progress:
                    shutil.copy2(WORK, TARGET)
                return 0
            return 2

        if not current_errors:
            entry["status"] = "nonstandard-failure"
            write_state({"status": "stuck", "history": history})
            break
        lines = text.splitlines()
        bounds = declaration_bounds(lines, current_errors[0].line)
        if bounds is None:
            entry["status"] = "no-declaration"
            write_state({"status": "stuck", "history": history})
            break
        start, end = bounds
        declaration = "\n".join(lines[start:end])
        context_start = max(0, start - 160)
        context_end = min(len(lines), end + 120)
        context = "\n".join(f"{i + 1}: {lines[i]}" for i in range(context_start, context_end))
        declaration_errors = [error for error in current_errors if start < error.line <= end]
        if not declaration_errors:
            declaration_errors = [current_errors[0]]
        diagnostics = "\n".join(error.raw for error in declaration_errors)
        api_context = api_search_context(diagnostics, declaration)
        prompt = f"""
Complete declaration to repair; preserve its signature exactly:

{declaration}

Lean compiler diagnostics:

{diagnostics}

Nearby project source context:

{context}

Search evidence from the pinned Mathlib/project tree:

{api_context or '(no additional grep matches)'}

Return only the complete replacement declaration. Do not change the signature.
""".strip()

        raw_responses: list[tuple[int, str, str]] = []
        errors_by_model: list[dict[str, str]] = []
        with concurrent.futures.ThreadPoolExecutor(max_workers=len(models)) as executor:
            futures = {executor.submit(invoke, model, prompt, token): (index, model) for index, model in enumerate(models, 1)}
            for future in concurrent.futures.as_completed(futures):
                index, model = futures[future]
                try:
                    raw_responses.append((index, model, future.result()))
                except Exception as exc:
                    errors_by_model.append({"model": model, "error": str(exc)})
        entry["model_call_errors"] = errors_by_model
        if not raw_responses:
            entry["status"] = "all-model-calls-failed"
            write_state({"status": "stuck", "history": history})
            break

        candidate_results: list[CandidateResult] = []
        # Compile candidates sequentially to avoid memory pressure from parallel Lean elaboration.
        for index, model, raw in raw_responses:
            candidate_results.append(
                evaluate_candidate(
                    index,
                    model,
                    raw,
                    lines,
                    start,
                    end,
                    args.baseline,
                    args.max_errors,
                    args.compile_timeout,
                )
            )
        entry["candidates"] = [result_json(result) for result in candidate_results]
        improving = [
            result for result in candidate_results
            if result.signature_ok
            and result.forbidden is None
            and result.source_file is not None
            and improves(
                rc,
                current_errors,
                result.exit_code,
                [] if result.first_error is None else [result.first_error],
                args.max_errors,
            )
        ]
        if not improving:
            entry["status"] = "no-kernel-improving-candidate"
            write_state({"status": "stuck", "history": history})
            break
        winner = min(improving, key=lambda result: candidate_score(result, args.max_errors))
        assert winner.source_file is not None
        shutil.copy2(winner.source_file, WORK)
        any_progress = True
        entry["winner"] = result_json(winner)
        write_state({"status": "running", "history": history})

    output = WORK.read_text(encoding="utf-8")
    if any_progress:
        if args.materialize_progress:
            shutil.copy2(WORK, TARGET)
        write_state({"status": "progress", "output_sha256": digest(output), "history": history})
        return 10
    write_state({"status": "stuck", "history": history})
    return 5


if __name__ == "__main__":
    raise SystemExit(main())
