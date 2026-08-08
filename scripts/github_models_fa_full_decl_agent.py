from __future__ import annotations

import argparse
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

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
OUT = ROOT / "build-logs" / "fa-full-decl-agent"
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


@dataclasses.dataclass(frozen=True)
class Failure:
    line: int
    col: int
    message: str
    raw: str


def digest(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def strip_comments(text: str) -> str:
    text = re.sub(r"/-.*?-\/", "", text, flags=re.S)
    return re.sub(r"--.*$", "", text, flags=re.M)


def compile_lean(path: Path, max_errors: int = 40, timeout: int = 1500) -> tuple[int, str, float]:
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
        return 124, output + "\nFA_FULL_DECL_TIMEOUT\n", time.monotonic() - started


def failures(log: str) -> list[Failure]:
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
    lines = text.splitlines()
    while lines and not lines[0].strip():
        lines.pop(0)
    while lines and not lines[-1].strip():
        lines.pop()
    return lines


def call_model(prompt: str, token: str) -> tuple[str, str]:
    endpoint = "https://models.github.ai/inference/chat/completions"
    models = ["openai/gpt-4.1", "openai/gpt-4o", "openai/gpt-4.1-mini"]
    errors: list[str] = []
    for model in models:
        payload = json.dumps(
            {
                "model": model,
                "temperature": 0,
                "max_tokens": 12000,
                "messages": [
                    {
                        "role": "system",
                        "content": (
                            "Repair exactly one complete Lean 4.33.0-rc1 declaration against the pinned Mathlib. "
                            "Return only the complete replacement declaration, without markdown fences. Preserve the "
                            "declaration signature byte-for-byte in meaning: same name, modifiers, binders, universe "
                            "parameters, type, assumptions, and conclusion. You may change only its implementation or "
                            "proof body. Never use sorry, admit, axiom, unsafe, native_decide, or Lean.ofReduceBool. "
                            "Do not add assumptions or weaken any result. Prefer explicit namespace-qualified APIs, "
                            "typed `change`/`show`, small helper `have`s, `calc`, `convert`, and extensionality."
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
        try:
            with urllib.request.urlopen(request, timeout=300) as response:
                data = json.loads(response.read().decode("utf-8"))
            return model, data["choices"][0]["message"]["content"]
        except (urllib.error.HTTPError, urllib.error.URLError, TimeoutError, KeyError, IndexError, json.JSONDecodeError) as exc:
            errors.append(f"{model}: {exc}")
    raise RuntimeError("all model calls failed: " + " | ".join(errors))


def metric(rc: int, errors: list[Failure], cap: int) -> tuple[int, int, int]:
    if rc == 0 and not errors:
        return (-1, -10**9, -10**9)
    first_line = errors[0].line if errors else 0
    return (min(len(errors), cap), -first_line, -len({err.line for err in errors}))


def improves(old_rc: int, old: list[Failure], new_rc: int, new: list[Failure], cap: int) -> bool:
    if new_rc == 0 and not new:
        return True
    if not old or not new:
        return False
    if new[0].line > old[0].line + 2:
        return True
    return metric(new_rc, new, cap) < metric(old_rc, old, cap)


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


def write_state(payload: dict) -> None:
    OUT.mkdir(parents=True, exist_ok=True)
    STATE.write_text(json.dumps(payload, indent=2, ensure_ascii=False), encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--seed", type=Path, default=TARGET)
    parser.add_argument("--baseline", type=Path, required=True)
    parser.add_argument("--rounds", type=int, default=8)
    parser.add_argument("--attempts", type=int, default=3)
    parser.add_argument("--max-errors", type=int, default=40)
    parser.add_argument("--materialize-progress", action="store_true")
    args = parser.parse_args()
    token = os.environ.get("GITHUB_TOKEN") or os.environ.get("GH_TOKEN")
    if not token:
        raise SystemExit("GITHUB_TOKEN is required")
    OUT.mkdir(parents=True, exist_ok=True)
    shutil.copy2(args.seed, WORK)
    history: list[dict] = []
    any_progress = False

    for round_no in range(1, args.rounds + 1):
        text = WORK.read_text(encoding="utf-8")
        rc, log, elapsed = compile_lean(WORK, args.max_errors)
        (OUT / f"round-{round_no}-before.log").write_text(log, encoding="utf-8")
        current_errors = failures(log)
        entry: dict = {
            "round": round_no,
            "input_sha256": digest(text),
            "input_exit": rc,
            "input_elapsed_seconds": elapsed,
            "input_error_count": len(current_errors),
            "input_first_error": dataclasses.asdict(current_errors[0]) if current_errors else None,
            "attempts": [],
        }
        history.append(entry)
        write_state({"status": "running", "history": history})
        print(json.dumps(entry, ensure_ascii=False), flush=True)

        if rc == 0 and not current_errors:
            rc2, log2, elapsed2 = compile_lean(WORK, 2000)
            (OUT / "compile-second.log").write_text(log2, encoding="utf-8")
            second = failures(log2)
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
            entry["status"] = "no-enclosing-declaration"
            write_state({"status": "stuck", "history": history})
            break
        start, end = bounds
        declaration = "\n".join(lines[start:end])
        context_start = max(0, start - 140)
        context_end = min(len(lines), end + 100)
        context = "\n".join(f"{i + 1}: {lines[i]}" for i in range(context_start, context_end))
        diagnostics = "\n".join(error.raw for error in current_errors if start < error.line <= end)
        if not diagnostics:
            diagnostics = current_errors[0].raw
        accepted = False
        for attempt in range(1, args.attempts + 1):
            prompt = f"""
Complete declaration to repair (its signature is immutable):

{declaration}

Compiler diagnostics:

{diagnostics}

Nearby source context:

{context}

Return only the complete replacement declaration. Keep its public signature unchanged.
This is attempt {attempt}.
""".strip()
            try:
                model, raw = call_model(prompt, token)
            except Exception as exc:
                entry["attempts"].append({"attempt": attempt, "model_error": str(exc)})
                continue
            (OUT / f"round-{round_no}-attempt-{attempt}.response.txt").write_text(raw, encoding="utf-8")
            replacement = clean_response(raw)
            candidate_lines = lines[:start] + replacement + lines[end:]
            candidate_text = "\n".join(candidate_lines) + "\n"
            bad = FORBIDDEN.search(strip_comments(candidate_text))
            if bad:
                entry["attempts"].append(
                    {"attempt": attempt, "model": model, "rejected": f"forbidden {bad.group(0)!r}"}
                )
                continue
            candidate = OUT / "candidate.lean"
            candidate.write_text(candidate_text, encoding="utf-8")
            ok, guard_log = signature_ok(candidate, args.baseline)
            (OUT / f"round-{round_no}-attempt-{attempt}.signature.log").write_text(
                guard_log, encoding="utf-8"
            )
            if not ok:
                entry["attempts"].append(
                    {"attempt": attempt, "model": model, "rejected": "signature changed"}
                )
                continue
            crc, clog, celapsed = compile_lean(candidate, args.max_errors)
            (OUT / f"round-{round_no}-attempt-{attempt}.log").write_text(clog, encoding="utf-8")
            candidate_errors = failures(clog)
            record = {
                "attempt": attempt,
                "model": model,
                "candidate_exit": crc,
                "candidate_elapsed_seconds": celapsed,
                "candidate_error_count": len(candidate_errors),
                "candidate_first_error": dataclasses.asdict(candidate_errors[0]) if candidate_errors else None,
            }
            entry["attempts"].append(record)
            if improves(rc, current_errors, crc, candidate_errors, args.max_errors):
                shutil.copy2(candidate, WORK)
                any_progress = True
                entry["accepted_attempt"] = attempt
                entry["accepted_model"] = model
                entry["output_sha256"] = digest(candidate_text)
                write_state({"status": "running", "history": history})
                accepted = True
                break
        if not accepted:
            entry["status"] = "no-kernel-improving-declaration"
            write_state({"status": "stuck", "history": history})
            break

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
