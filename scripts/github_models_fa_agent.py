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
EVIDENCE = ROOT / "build-logs" / "fa-model-agent"
LOG = EVIDENCE / "compile.log"
STATE = EVIDENCE / "state.json"
ERR_RE = re.compile(r"^(.*?\.lean):(\d+):(\d+):\s+(?:error[^:]*:|error:)\s*(.*)$")
DECL_RE = re.compile(
    r"^(?P<indent>\s*)(?:(?:private|protected|noncomputable|local)\s+)*"
    r"(?P<kind>theorem|lemma|corollary|example|instance|def|abbrev)\b"
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


def digest(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def run_lean(path: Path, max_errors: int = 5, timeout: int = 1200) -> tuple[int, str, float]:
    start = time.monotonic()
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
        return proc.returncode, proc.stdout, time.monotonic() - start
    except subprocess.TimeoutExpired as exc:
        output = exc.stdout or ""
        if isinstance(output, bytes):
            output = output.decode("utf-8", errors="replace")
        return 124, output + "\nMODEL_AGENT_COMPILE_TIMEOUT\n", time.monotonic() - start


def failures(log: str) -> list[Failure]:
    result: list[Failure] = []
    for line in log.splitlines():
        match = ERR_RE.match(line)
        if match:
            result.append(Failure(int(match.group(2)), int(match.group(3)), match.group(4)))
    return result


def declaration_bounds(lines: list[str], line_no: int) -> tuple[int, int] | None:
    index = max(0, min(len(lines) - 1, line_no - 1))
    starts = [i for i, line in enumerate(lines) if DECL_RE.match(line)]
    preceding = [i for i in starts if i <= index]
    if not preceding:
        return None
    start = preceding[-1]
    end = next((i for i in starts if i > start), len(lines))
    return start, end


def proof_header_and_body(decl_lines: list[str]) -> tuple[list[str], list[str]] | None:
    for i, line in enumerate(decl_lines):
        if ":= by" in line:
            left, right = line.split(":= by", 1)
            header = decl_lines[:i] + [left + ":= by"]
            body = ([right] if right.strip() else []) + decl_lines[i + 1 :]
            return header, body
    return None


def normalize_header(lines: list[str]) -> str:
    return "\n".join(line.rstrip() for line in lines).strip()


def strip_comments(text: str) -> str:
    text = re.sub(r"/-.*?-\/", "", text, flags=re.S)
    return re.sub(r"--.*$", "", text, flags=re.M)


def response_text(payload: dict) -> str:
    return payload["choices"][0]["message"]["content"]


def call_model(prompt: str, token: str) -> tuple[str, str]:
    endpoint = "https://models.github.ai/inference/chat/completions"
    models = ["openai/gpt-4.1", "openai/gpt-4o", "openai/gpt-4.1-mini"]
    errors: list[str] = []
    for model in models:
        body = json.dumps(
            {
                "model": model,
                "temperature": 0.1,
                "max_tokens": 6000,
                "messages": [
                    {
                        "role": "system",
                        "content": (
                            "You repair Lean 4.33.0-rc1 + current Mathlib proofs. "
                            "Return only the replacement proof body, without markdown fences. "
                            "Do not repeat or change the declaration statement. Never use sorry, admit, "
                            "axiom, unsafe, native_decide, or Lean.ofReduceBool. Existing assumptions and "
                            "conclusions are immutable. Prefer explicit current-Mathlib lemmas and small calc blocks."
                        ),
                    },
                    {"role": "user", "content": prompt},
                ],
            }
        ).encode("utf-8")
        request = urllib.request.Request(
            endpoint,
            data=body,
            method="POST",
            headers={
                "Authorization": f"Bearer {token}",
                "Content-Type": "application/json",
                "Accept": "application/json",
                "X-GitHub-Api-Version": "2022-11-28",
            },
        )
        try:
            with urllib.request.urlopen(request, timeout=180) as response:
                payload = json.loads(response.read().decode("utf-8"))
            return model, response_text(payload)
        except (urllib.error.URLError, urllib.error.HTTPError, KeyError, IndexError, json.JSONDecodeError) as exc:
            errors.append(f"{model}: {exc}")
    raise RuntimeError("all GitHub Models calls failed: " + " | ".join(errors))


def clean_body(raw: str) -> list[str]:
    text = raw.strip()
    fence = re.search(r"```(?:lean)?\s*(.*?)```", text, flags=re.S)
    if fence:
        text = fence.group(1).strip()
    if text.startswith(":= by"):
        text = text[len(":= by") :].lstrip("\n ")
    elif text.startswith("by\n") or text == "by":
        text = text[2:].lstrip("\n ")
    return text.splitlines()


def indent_body(body: list[str], header: list[str]) -> list[str]:
    indent = re.match(r"^\s*", header[-1]).group(0) + "  "
    # Preserve relative indentation while ensuring the body sits under `by`.
    nonempty = [len(line) - len(line.lstrip()) for line in body if line.strip()]
    minimum = min(nonempty) if nonempty else 0
    return [indent + line[minimum:] if line.strip() else "" for line in body]


def is_improvement(old: Failure, new: Failure | None, old_start: int,
                   new_lines: list[str]) -> bool:
    if new is None:
        return True
    if new.line > old.line + 2:
        return True
    bounds = declaration_bounds(new_lines, new.line)
    return bounds is not None and bounds[0] > old_start


def save_state(payload: dict) -> None:
    EVIDENCE.mkdir(parents=True, exist_ok=True)
    STATE.write_text(json.dumps(payload, indent=2, ensure_ascii=False), encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--seed", type=Path, required=True)
    parser.add_argument("--rounds", type=int, default=30)
    parser.add_argument("--attempts", type=int, default=3)
    parser.add_argument("--materialize-on-pass", action="store_true")
    args = parser.parse_args()

    token = os.environ.get("GITHUB_TOKEN") or os.environ.get("GH_TOKEN")
    if not token:
        raise SystemExit("GITHUB_TOKEN is required")
    EVIDENCE.mkdir(parents=True, exist_ok=True)
    work = EVIDENCE / "working.lean"
    shutil.copy2(args.seed, work)
    history: list[dict] = []

    for round_no in range(1, args.rounds + 1):
        text = work.read_text(encoding="utf-8")
        rc, log, elapsed = run_lean(work)
        LOG.write_text(log, encoding="utf-8")
        current_failures = failures(log)
        first = current_failures[0] if current_failures else None
        entry: dict = {
            "round": round_no,
            "sha256": digest(text),
            "exit_code": rc,
            "elapsed_seconds": elapsed,
            "failure": dataclasses.asdict(first) if first else None,
        }
        history.append(entry)
        save_state({"status": "running", "current": entry, "history": history})
        print(json.dumps(entry, ensure_ascii=False), flush=True)

        if rc == 0 and first is None:
            rc2, log2, elapsed2 = run_lean(work, max_errors=2000)
            (EVIDENCE / "compile-second.log").write_text(log2, encoding="utf-8")
            second = failures(log2)
            result = {
                "status": "pass" if rc2 == 0 and not second else "second-run-failed",
                "sha256": digest(text),
                "first_exit": rc,
                "second_exit": rc2,
                "second_elapsed_seconds": elapsed2,
                "second_failure": dataclasses.asdict(second[0]) if second else None,
                "history": history,
            }
            save_state(result)
            if result["status"] == "pass":
                shutil.copy2(work, EVIDENCE / "Mock2_FunctionalAnalysis.PASS.lean")
                if args.materialize_on_pass:
                    shutil.copy2(work, TARGET)
                print("FA_MODEL_AGENT_TWO_RUN_PASS", digest(text), flush=True)
                return 0
            return 2

        if first is None:
            save_state({"status": "nonstandard-failure", "history": history})
            return 3
        lines = text.splitlines()
        bounds = declaration_bounds(lines, first.line)
        if bounds is None:
            save_state({"status": "no-declaration", "history": history})
            return 4
        start, end = bounds
        declaration = lines[start:end]
        parsed = proof_header_and_body(declaration)
        if parsed is None:
            save_state({"status": "non-proof-declaration", "history": history})
            return 5
        header, old_body = parsed
        context_start = max(0, start - 100)
        context_end = min(len(lines), end + 80)
        context = "\n".join(f"{i + 1}: {lines[i]}" for i in range(context_start, context_end))
        compiler = "\n".join(log.splitlines()[-500:])
        accepted = False
        attempt_records: list[dict] = []
        for attempt in range(1, args.attempts + 1):
            prompt = f"""
The immutable declaration header is:

{normalize_header(header)}

Current proof body is:

{chr(10).join(old_body)}

The compiler diagnostics are:

{compiler}

Nearby source context with line numbers is:

{context}

Return only a corrected proof body to place after `:= by`. Keep the exact header immutable.
This is attempt {attempt}; use explicit type annotations and current namespace-qualified Mathlib APIs.
""".strip()
            try:
                model, raw = call_model(prompt, token)
            except Exception as exc:
                attempt_records.append({"attempt": attempt, "model_error": str(exc)})
                continue
            (EVIDENCE / f"round-{round_no}-attempt-{attempt}.response.txt").write_text(
                raw, encoding="utf-8"
            )
            body = clean_body(raw)
            replacement = header + indent_body(body, header)
            candidate_lines = lines[:start] + replacement + lines[end:]
            candidate_text = "\n".join(candidate_lines) + "\n"
            bad = FORBIDDEN.search(strip_comments(candidate_text))
            if bad:
                attempt_records.append({
                    "attempt": attempt,
                    "model": model,
                    "rejected": f"forbidden token {bad.group(0)!r}",
                })
                continue
            candidate = EVIDENCE / "candidate.lean"
            candidate.write_text(candidate_text, encoding="utf-8")
            crc, clog, celapsed = run_lean(candidate)
            (EVIDENCE / f"round-{round_no}-attempt-{attempt}.log").write_text(
                clog, encoding="utf-8"
            )
            candidate_failures = failures(clog)
            candidate_first = candidate_failures[0] if candidate_failures else None
            record = {
                "attempt": attempt,
                "model": model,
                "exit_code": crc,
                "elapsed_seconds": celapsed,
                "failure": dataclasses.asdict(candidate_first) if candidate_first else None,
            }
            attempt_records.append(record)
            if crc == 0 or is_improvement(first, candidate_first, start, candidate_lines):
                shutil.copy2(candidate, work)
                entry["accepted_attempt"] = attempt
                entry["accepted_model"] = model
                entry["attempts"] = attempt_records
                save_state({"status": "running", "current": entry, "history": history})
                accepted = True
                break
        if not accepted:
            entry["attempts"] = attempt_records
            save_state({"status": "stuck", "current": entry, "history": history})
            return 6
    save_state({"status": "round-limit", "history": history})
    return 7


if __name__ == "__main__":
    raise SystemExit(main())
