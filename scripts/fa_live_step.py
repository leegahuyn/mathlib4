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
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
OUT = ROOT / "build-logs" / "fa-live-step"
WORK = OUT / "working.lean"
LOG = OUT / "compile.log"
STATE = OUT / "state.json"
ERR = re.compile(r"^(.*?\.lean):(\d+):(\d+):\s+(?:error[^:]*:|error:)\s*(.*)$")
DECL = re.compile(
    r"^(\s*)(?:(?:private|protected|noncomputable|local)\s+)*"
    r"(theorem|lemma|corollary|example|instance|def|abbrev)\b"
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


def run(path: Path, max_errors: int = 1, timeout: int = 1000) -> tuple[int, str, float]:
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
        return 124, output + "\nFA_LIVE_TIMEOUT\n", time.monotonic() - started


def first(log: str) -> Failure | None:
    for line in log.splitlines():
        match = ERR.match(line)
        if match:
            return Failure(int(match.group(2)), int(match.group(3)), match.group(4))
    return None


def decl_bounds(lines: list[str], line_no: int) -> tuple[int, int] | None:
    starts = [i for i, line in enumerate(lines) if DECL.match(line)]
    preceding = [i for i in starts if i <= line_no - 1]
    if not preceding:
        return None
    start = preceding[-1]
    end = next((i for i in starts if i > start), len(lines))
    return start, end


def command_span(lines: list[str], line_no: int) -> tuple[int, int]:
    i = max(0, min(len(lines) - 1, line_no - 1))
    start = i
    while start > 0:
        previous = lines[start - 1].rstrip()
        current = lines[start].lstrip()
        if previous.endswith(("[", "(", "{", ",", "\\")) or current.startswith(("]", ")", "}")):
            start -= 1
        else:
            break
    end = i + 1
    depth = 0
    for j in range(start, min(len(lines), start + 50)):
        code = re.sub(r"--.*$", "", lines[j])
        depth += code.count("[") + code.count("(") + code.count("{")
        depth -= code.count("]") + code.count(")") + code.count("}")
        end = j + 1
        if j >= i and depth <= 0 and not code.rstrip().endswith((",", "\\")):
            break
    return start, end


def body_span(lines: list[str], start: int, end: int) -> tuple[int, int, str] | None:
    for i in range(start, min(end, start + 140)):
        if ":= by" in lines[i]:
            return i, end, lines[i].split(":= by", 1)[0] + ":= by"
    return None


def improvement(old: Failure, old_decl: tuple[int, int] | None,
                new: Failure | None, candidate: list[str]) -> bool:
    if new is None:
        return True
    if new.line > old.line + 2:
        return True
    new_decl = decl_bounds(candidate, new.line)
    return old_decl is not None and new_decl is not None and new_decl[0] > old_decl[0]


def strip_comments(text: str) -> str:
    text = re.sub(r"/-.*?-\/", "", text, flags=re.S)
    return re.sub(r"--.*$", "", text, flags=re.M)


def candidates(lines: list[str], failure: Failure):
    start, end = command_span(lines, failure.line)
    indent = re.match(r"^\s*", lines[start]).group(0)
    lowered = failure.message.lower()
    if any(term in lowered for term in ("no goals to be solved", "made no progress", "never executed")):
        yield "drop-redundant", lines[:start] + lines[end:]
    tactics = [
        "rfl", "assumption", "simp", "simpa", "simp_all", "aesop", "exact?", "aesop?",
        "omega", "linarith", "nlinarith", "ring", "ring_nf", "norm_num", "positivity",
        "fun_prop", "continuity", "ext <;> simp", "apply Subtype.ext <;> simp",
        "first | exact? | aesop | simp_all | omega | ring | nlinarith",
    ]
    for tactic in tactics:
        yield "command:" + tactic, lines[:start] + [indent + tactic] + lines[end:]
    bounds = decl_bounds(lines, failure.line)
    if bounds is None:
        return
    proof = body_span(lines, *bounds)
    if proof is None:
        return
    body_start, body_end, header = proof
    proof_indent = re.match(r"^\s*", lines[body_start]).group(0) + "  "
    portfolios = [
        ["classical", "exact?"],
        ["classical", "aesop"],
        ["classical", "simp_all"],
        ["classical", "ext <;> simp_all"],
        ["classical", "constructor <;> aesop"],
        ["classical", "first | exact? | aesop | simp_all | omega | ring | nlinarith"],
    ]
    for index, proof_lines in enumerate(portfolios, 1):
        replacement = [header] + [proof_indent + line for line in proof_lines]
        yield f"whole-proof:{index}", lines[:body_start] + replacement + lines[body_end:]


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--attempt-limit", type=int, default=28)
    parser.add_argument("--materialize-progress", action="store_true")
    args = parser.parse_args()
    OUT.mkdir(parents=True, exist_ok=True)
    shutil.copy2(TARGET, WORK)
    original = WORK.read_text(encoding="utf-8")
    rc, log, elapsed = run(WORK)
    LOG.write_text(log, encoding="utf-8")
    failure = first(log)
    state: dict = {
        "input_sha256": digest(original),
        "input_exit": rc,
        "input_elapsed_seconds": elapsed,
        "input_failure": dataclasses.asdict(failure) if failure else None,
        "attempts": [],
    }
    if rc == 0 and failure is None:
        rc2, log2, elapsed2 = run(WORK, max_errors=2000)
        (OUT / "compile-second.log").write_text(log2, encoding="utf-8")
        second = first(log2)
        state.update(
            {
                "status": "pass" if rc2 == 0 and second is None else "second-run-failed",
                "second_exit": rc2,
                "second_elapsed_seconds": elapsed2,
                "second_failure": dataclasses.asdict(second) if second else None,
            }
        )
        STATE.write_text(json.dumps(state, indent=2), encoding="utf-8")
        return 0 if state["status"] == "pass" else 2
    if failure is None:
        state["status"] = "nonstandard-failure"
        STATE.write_text(json.dumps(state, indent=2), encoding="utf-8")
        return 3
    lines = original.splitlines()
    old_decl = decl_bounds(lines, failure.line)
    for number, (label, candidate_lines) in enumerate(candidates(lines, failure), 1):
        if number > args.attempt_limit:
            break
        candidate_text = "\n".join(candidate_lines) + "\n"
        bad = FORBIDDEN.search(strip_comments(candidate_text))
        if bad:
            continue
        candidate = OUT / "candidate.lean"
        candidate.write_text(candidate_text, encoding="utf-8")
        crc, clog, celapsed = run(candidate)
        (OUT / f"attempt-{number}.log").write_text(clog, encoding="utf-8")
        candidate_failure = first(clog)
        record = {
            "number": number,
            "label": label,
            "exit": crc,
            "elapsed_seconds": celapsed,
            "failure": dataclasses.asdict(candidate_failure) if candidate_failure else None,
        }
        state["attempts"].append(record)
        if crc == 0 or improvement(failure, old_decl, candidate_failure, candidate_lines):
            state["status"] = "progress"
            state["accepted"] = record
            state["output_sha256"] = digest(candidate_text)
            shutil.copy2(candidate, OUT / "accepted.lean")
            if args.materialize_progress:
                shutil.copy2(candidate, TARGET)
            STATE.write_text(json.dumps(state, indent=2), encoding="utf-8")
            return 10
    state["status"] = "stuck"
    STATE.write_text(json.dumps(state, indent=2), encoding="utf-8")
    return 5


if __name__ == "__main__":
    raise SystemExit(main())
