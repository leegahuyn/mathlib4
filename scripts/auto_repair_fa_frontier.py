from __future__ import annotations

import argparse
import dataclasses
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import time
from pathlib import Path
from typing import Iterable

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
STATE_DIR = ROOT / "build-logs" / "fa-auto-frontier"
WORK = STATE_DIR / "working.lean"
LOG = STATE_DIR / "compile.log"
STATE = STATE_DIR / "state.json"

DECL_RE = re.compile(
    r"^(?P<indent>\s*)(?:(?:noncomputable|private|protected|local)\s+)*"
    r"(?P<kind>theorem|lemma|corollary|example|instance|def|abbrev)\b"
)
ERR_RE = re.compile(r"^(?P<path>.*?\.lean):(?P<line>\d+):(?P<col>\d+):\s+(?:error[^:]*:|error:)\s*(?P<msg>.*)$")
FORBIDDEN_RE = re.compile(
    r"(?m)^\s*(?:sorry|admit)\b|(?m)^\s*axiom\b|(?m)^\s*unsafe\b|"
    r"\bnative_decide\b|\bLean\.ofReduceBool\b"
)


@dataclasses.dataclass(frozen=True)
class Failure:
    line: int
    col: int
    message: str


def sha(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def run_lean(path: Path, max_errors: int, timeout: int) -> tuple[int, str, float]:
    command = ["lake", "env", "lean", f"-DmaxErrors={max_errors}", str(path)]
    started = time.monotonic()
    try:
        proc = subprocess.run(
            command,
            cwd=ROOT,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=timeout,
            env={**os.environ, "LC_ALL": "C.UTF-8"},
        )
        return proc.returncode, proc.stdout, time.monotonic() - started
    except subprocess.TimeoutExpired as exc:
        out = exc.stdout or ""
        if isinstance(out, bytes):
            out = out.decode("utf-8", errors="replace")
        return 124, out + "\nAUTO_REPAIR_TIMEOUT\n", time.monotonic() - started


def first_failure(log: str) -> Failure | None:
    for raw in log.splitlines():
        match = ERR_RE.match(raw)
        if match:
            return Failure(int(match.group("line")), int(match.group("col")), match.group("msg"))
    return None


def declaration_starts(lines: list[str]) -> list[int]:
    return [i for i, line in enumerate(lines) if DECL_RE.match(line)]


def enclosing_decl(lines: list[str], line_no: int) -> tuple[int, int, str] | None:
    index = max(0, min(len(lines) - 1, line_no - 1))
    starts = declaration_starts(lines)
    previous = [s for s in starts if s <= index]
    if not previous:
        return None
    start = previous[-1]
    later = [s for s in starts if s > start]
    end = later[0] if later else len(lines)
    head = lines[start].strip()
    return start, end, head


def command_span(lines: list[str], line_no: int) -> tuple[int, int]:
    """Return a conservative tactic-command span containing line_no (0-based half-open)."""
    i = max(0, min(len(lines) - 1, line_no - 1))
    indent = len(lines[i]) - len(lines[i].lstrip())
    start = i
    while start > 0:
        prev = lines[start - 1]
        if not prev.strip():
            break
        prev_indent = len(prev) - len(prev.lstrip())
        if prev_indent < indent:
            break
        if prev.rstrip().endswith(("[", "(", "{", ",", "\\")):
            start -= 1
            indent = min(indent, prev_indent)
            continue
        if lines[start].lstrip().startswith(("]", ")", "}")):
            start -= 1
            indent = min(indent, prev_indent)
            continue
        break
    end = i + 1
    depth = 0
    for j in range(start, min(len(lines), i + 20)):
        text = re.sub(r"--.*$", "", lines[j])
        depth += text.count("[") + text.count("(") + text.count("{")
        depth -= text.count("]") + text.count(")") + text.count("}")
        end = j + 1
        if j >= i and depth <= 0 and not text.rstrip().endswith((",", "\\")):
            break
    return start, end


def replace_span(lines: list[str], start: int, end: int, replacement: list[str]) -> list[str]:
    return lines[:start] + replacement + lines[end:]


def proof_body_span(lines: list[str], decl_start: int, decl_end: int) -> tuple[int, int, str] | None:
    for i in range(decl_start, min(decl_end, decl_start + 80)):
        if ":= by" in lines[i]:
            prefix, _ = lines[i].split(":= by", 1)
            return i, decl_end, prefix + ":= by"
        if re.search(r"\bwhere\s*$", lines[i]):
            return None
    return None


def candidate_edits(lines: list[str], failure: Failure) -> Iterable[tuple[str, list[str]]]:
    line_i = failure.line - 1
    if not (0 <= line_i < len(lines)):
        return
    cmd_start, cmd_end = command_span(lines, failure.line)
    original = lines[cmd_start:cmd_end]
    base_indent = re.match(r"^\s*", lines[cmd_start]).group(0)
    msg = failure.message.lower()

    if "no goals to be solved" in msg or "made no progress" in msg or "tactic is never executed" in msg:
        yield "drop-redundant-command", replace_span(lines, cmd_start, cmd_end, [])

    command_portfolio = [
        "rfl",
        "assumption",
        "simp",
        "simpa",
        "simp_all",
        "aesop",
        "omega",
        "linarith",
        "nlinarith",
        "ring",
        "ring_nf",
        "norm_num",
        "positivity",
        "fun_prop",
        "continuity",
        "ext <;> simp",
        "apply Subtype.ext <;> simp",
        "first | rfl | assumption | simp_all | aesop | omega | ring | nlinarith",
    ]
    for tactic in command_portfolio:
        yield f"command:{tactic}", replace_span(lines, cmd_start, cmd_end, [base_indent + tactic])

    decl = enclosing_decl(lines, failure.line)
    if decl is None:
        return
    decl_start, decl_end, _ = decl
    body = proof_body_span(lines, decl_start, decl_end)
    if body is None:
        return
    body_start, body_end, header = body
    header_indent = re.match(r"^\s*", lines[body_start]).group(0)
    proof_indent = header_indent + "  "
    proof_portfolio = [
        ["classical", "simp_all"],
        ["classical", "aesop"],
        ["classical", "ext <;> simp_all"],
        ["classical", "constructor <;> simp_all"],
        ["classical", "first | rfl | assumption | simp_all | aesop | omega | ring | nlinarith"],
    ]
    for n, tactics in enumerate(proof_portfolio, 1):
        repl = [header] + [proof_indent + tactic for tactic in tactics]
        yield f"whole-proof-{n}", replace_span(lines, body_start, body_end, repl)


def forbidden(text: str) -> str | None:
    stripped = re.sub(r"/-.*?-\/", "", text, flags=re.S)
    stripped = re.sub(r"--.*$", "", stripped, flags=re.M)
    match = FORBIDDEN_RE.search(stripped)
    return match.group(0) if match else None


def improves(old: Failure, new: Failure | None, old_decl: tuple[int, int, str] | None,
             new_lines: list[str]) -> bool:
    if new is None:
        return True
    if new.line > old.line + 2:
        return True
    if old_decl is not None:
        new_decl = enclosing_decl(new_lines, new.line)
        if new_decl is not None and new_decl[0] > old_decl[0]:
            return True
    return False


def write_state(payload: dict) -> None:
    STATE_DIR.mkdir(parents=True, exist_ok=True)
    STATE.write_text(json.dumps(payload, indent=2, ensure_ascii=False), encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-rounds", type=int, default=40)
    parser.add_argument("--compile-timeout", type=int, default=900)
    parser.add_argument("--seed", type=Path, default=TARGET)
    parser.add_argument("--materialize-on-pass", action="store_true")
    args = parser.parse_args()

    STATE_DIR.mkdir(parents=True, exist_ok=True)
    seed = args.seed.resolve()
    if not seed.exists():
        raise SystemExit(f"missing seed: {seed}")
    shutil.copy2(seed, WORK)
    history: list[dict] = []

    for round_no in range(1, args.max_rounds + 1):
        text = WORK.read_text(encoding="utf-8")
        bad = forbidden(text)
        if bad:
            write_state({"status": "forbidden", "token": bad, "history": history})
            return 3
        rc, log, elapsed = run_lean(WORK, 1, args.compile_timeout)
        LOG.write_text(log, encoding="utf-8")
        failure = first_failure(log)
        step = {
            "round": round_no,
            "sha256": sha(text),
            "exit_code": rc,
            "elapsed_seconds": elapsed,
            "failure": dataclasses.asdict(failure) if failure else None,
        }
        history.append(step)
        write_state({"status": "running", "current": step, "history": history})
        print(json.dumps(step, ensure_ascii=False), flush=True)

        if rc == 0 and failure is None:
            # Independent second direct compile of identical bytes.
            rc2, log2, elapsed2 = run_lean(WORK, 2000, args.compile_timeout)
            (STATE_DIR / "compile-second.log").write_text(log2, encoding="utf-8")
            failure2 = first_failure(log2)
            result = {
                "status": "pass" if rc2 == 0 and failure2 is None else "second-run-failed",
                "sha256": sha(text),
                "first_exit": rc,
                "second_exit": rc2,
                "second_elapsed_seconds": elapsed2,
                "second_failure": dataclasses.asdict(failure2) if failure2 else None,
                "history": history,
            }
            write_state(result)
            if result["status"] == "pass":
                passed = STATE_DIR / "Mock2_FunctionalAnalysis.PASS.lean"
                shutil.copy2(WORK, passed)
                if args.materialize_on_pass:
                    shutil.copy2(WORK, TARGET)
                print("FA_AUTO_TWO_RUN_PASS", sha(text), flush=True)
                return 0
            return 2

        if failure is None:
            write_state({"status": "nonstandard-failure", "exit_code": rc, "history": history})
            return 4

        lines = text.splitlines()
        old_decl = enclosing_decl(lines, failure.line)
        accepted = False
        attempts: list[dict] = []
        for label, candidate_lines in candidate_edits(lines, failure):
            candidate_text = "\n".join(candidate_lines) + "\n"
            if forbidden(candidate_text):
                continue
            candidate = STATE_DIR / "candidate.lean"
            candidate.write_text(candidate_text, encoding="utf-8")
            crc, clog, celapsed = run_lean(candidate, 1, args.compile_timeout)
            cfailure = first_failure(clog)
            attempts.append({
                "label": label,
                "exit_code": crc,
                "elapsed_seconds": celapsed,
                "failure": dataclasses.asdict(cfailure) if cfailure else None,
            })
            if crc == 0 or improves(failure, cfailure, old_decl, candidate_lines):
                shutil.copy2(candidate, WORK)
                accepted = True
                history[-1]["accepted_edit"] = label
                history[-1]["attempts"] = attempts
                write_state({"status": "running", "current": history[-1], "history": history})
                print(f"ACCEPTED {label}", flush=True)
                break
        if not accepted:
            history[-1]["attempts"] = attempts
            write_state({
                "status": "stuck",
                "current": history[-1],
                "history": history,
                "source": str(WORK),
                "log": str(LOG),
            })
            print("FA_AUTO_STUCK", failure, flush=True)
            return 5

    write_state({"status": "round-limit", "history": history})
    return 6


if __name__ == "__main__":
    raise SystemExit(main())
