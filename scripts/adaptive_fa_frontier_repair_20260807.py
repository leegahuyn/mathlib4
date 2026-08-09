from __future__ import annotations

import argparse
import difflib
import json
import re
import subprocess
import sys
from dataclasses import dataclass, asdict
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
OUTDIR = ROOT / ".lake" / "build" / "lib" / "lean" / "PrimalitySheafVerification"
WORK = Path("/tmp/adaptive-fa-frontier")


@dataclass
class Frontier:
    exit_code: int
    line: int | None
    column: int | None
    kind: str
    message: str
    error_count: int


def run_lean(label: str, max_errors: int = 1) -> Frontier:
    WORK.mkdir(parents=True, exist_ok=True)
    OUTDIR.mkdir(parents=True, exist_ok=True)
    log = WORK / f"{label}.log"
    for ext in ("olean", "ilean", "olean.private"):
        path = OUTDIR / f"Mock2_FunctionalAnalysis.{ext}"
        if path.exists():
            path.unlink()
    cmd = [
        "lake", "env", "lean", f"-DmaxErrors={max_errors}", str(TARGET.relative_to(ROOT)),
        "-o", str(OUTDIR / "Mock2_FunctionalAnalysis.olean"),
        "-i", str(OUTDIR / "Mock2_FunctionalAnalysis.ilean"),
    ]
    proc = subprocess.run(
        cmd,
        cwd=ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        encoding="utf-8",
        errors="replace",
        timeout=1800,
        check=False,
    )
    log.write_text(proc.stdout, encoding="utf-8")
    errors = list(re.finditer(r"(?m)^.*?:([0-9]+):([0-9]+): error(?:\([^\n]*\))?: (.*)$", proc.stdout))
    if not errors:
        return Frontier(proc.returncode, None, None, "none", proc.stdout[-3000:], 0)
    first = errors[0]
    line = int(first.group(1))
    column = int(first.group(2))
    first_line = first.group(3).strip()
    following = proc.stdout[first.start():]
    following = following[: min(len(following), 6000)]
    kind = classify(first_line, following)
    return Frontier(proc.returncode, line, column, kind, following, len(errors))


def classify(first_line: str, message: str) -> str:
    text = first_line + "\n" + message
    if "No goals to be solved" in text:
        return "no_goals"
    if "`simp` made no progress" in text:
        return "simp_no_progress"
    if "unknown namespace" in text:
        return "unknown_namespace"
    if "Unknown identifier" in text or "Unknown constant" in text:
        return "unknown_identifier"
    if "Function expected at" in text and "identifier" in text and "unknown" in text:
        return "unknown_function"
    if "Invalid field" in text:
        return "invalid_field"
    return "other"


def declaration_index(lines: list[str]) -> tuple[dict[str, list[str]], dict[str, list[str]]]:
    declarations: dict[str, list[str]] = {}
    namespaces: dict[str, list[str]] = {}
    stack: list[str] = []
    decl_re = re.compile(
        r"^\s*(?:(?:noncomputable|private|protected|local)\s+)*"
        r"(?:theorem|lemma|def|abbrev|opaque|structure|class|inductive)\s+"
        r"([A-Za-z_][A-Za-z0-9_']*)"
    )
    ns_re = re.compile(r"^\s*namespace\s+([A-Za-z_][A-Za-z0-9_'.]*)\s*$")
    end_re = re.compile(r"^\s*end(?:\s+([A-Za-z_][A-Za-z0-9_'.]*))?\s*$")
    for raw in lines:
        stripped = raw.split("--", 1)[0].rstrip()
        match = ns_re.match(stripped)
        if match:
            name = match.group(1)
            if "." in name:
                full = name
                stack = name.split(".")
            else:
                stack.append(name)
                full = ".".join(stack)
            namespaces.setdefault(name.split(".")[-1], []).append(full)
            continue
        if end_re.match(stripped):
            if stack:
                stack.pop()
            continue
        match = decl_re.match(stripped)
        if match:
            short = match.group(1)
            full = ".".join([*stack, short]) if stack else short
            declarations.setdefault(short, []).append(full)
    for table in (declarations, namespaces):
        for key, values in table.items():
            table[key] = sorted(set(values))
    return declarations, namespaces


def nearby_indices(line: int, total: int, radius: int = 3) -> range:
    start = max(0, line - 1 - radius)
    stop = min(total, line + radius)
    return range(start, stop)


def candidate_edits(frontier: Frontier, lines: list[str]) -> list[tuple[str, list[str]]]:
    if frontier.line is None:
        return []
    declarations, namespaces = declaration_index(lines)
    candidates: list[tuple[str, list[str]]] = []
    index = frontier.line - 1

    def add(label: str, changed: list[str]) -> None:
        if changed != lines and all(changed != existing for _, existing in candidates):
            candidates.append((label, changed))

    if frontier.kind in {"no_goals", "simp_no_progress"} and 0 <= index < len(lines):
        stripped = lines[index].strip()
        if stripped.startswith(("simp", "simpa", "rfl", "exact", "assumption", "done")):
            changed = lines.copy()
            del changed[index]
            add(f"remove redundant tactic at line {frontier.line}", changed)

    if frontier.kind == "unknown_namespace":
        match = re.search(r"unknown namespace `([^`]+)`", frontier.message)
        if match:
            unknown = match.group(1)
            suffix = unknown.split(".")[-1]
            choices = namespaces.get(suffix, [])
            if len(choices) == 1:
                full = choices[0]
                for i in nearby_indices(frontier.line, len(lines), 5):
                    if unknown in lines[i]:
                        changed = lines.copy()
                        changed[i] = changed[i].replace(unknown, full)
                        add(f"qualify namespace {unknown} as {full} near line {i + 1}", changed)

    if frontier.kind in {"unknown_identifier", "unknown_function"}:
        matches = re.findall(r"(?:Unknown identifier|Unknown constant) `([^`]+)`", frontier.message)
        if not matches:
            hint = re.search(r"identifier `([^`]+)` is unknown", frontier.message)
            if hint:
                matches = [hint.group(1)]
        if not matches:
            function = re.search(r"Function expected at\s*\n\s*([A-Za-z_][A-Za-z0-9_'.]*)", frontier.message)
            if function:
                matches = [function.group(1)]
        for unknown in matches:
            short = unknown.split(".")[-1]
            choices = declarations.get(short, [])
            if len(choices) == 1 and choices[0] != unknown:
                full = choices[0]
                for i in nearby_indices(frontier.line, len(lines), 7):
                    pattern = rf"(?<![A-Za-z0-9_'.]){re.escape(unknown)}(?![A-Za-z0-9_'])"
                    if re.search(pattern, lines[i]):
                        changed = lines.copy()
                        changed[i] = re.sub(pattern, full, changed[i])
                        add(f"qualify identifier {unknown} as {full} near line {i + 1}", changed)

    if frontier.kind == "invalid_field":
        match = re.search(r"Invalid field `([^`]+)`", frontier.message)
        if match:
            field = match.group(1).split(".")[-1]
            choices = declarations.get(field, [])
            if len(choices) == 1:
                theorem = choices[0]
                for i in nearby_indices(frontier.line, len(lines), 5):
                    field_pattern = re.compile(
                        rf"\b([A-Za-z_][A-Za-z0-9_']*)\.{re.escape(field)}\b"
                    )
                    found = field_pattern.search(lines[i])
                    if found:
                        receiver = found.group(1)
                        changed = lines.copy()
                        changed[i] = field_pattern.sub(f"{theorem} {receiver}", changed[i], count=1)
                        add(f"replace invalid field {receiver}.{field} by {theorem} {receiver}", changed)
    return candidates


def better(before: Frontier, after: Frontier) -> bool:
    if after.exit_code == 0 and after.error_count == 0:
        return True
    if before.line is None or after.line is None:
        return False
    if after.line > before.line:
        return True
    if after.line == before.line and after.kind != before.kind:
        # Accept only when a mechanical elaboration failure becomes a later proof-level
        # obligation; never accept a move in the opposite direction.
        mechanical = {"unknown_namespace", "unknown_identifier", "unknown_function", "invalid_field", "no_goals", "simp_no_progress"}
        return before.kind in mechanical and after.kind not in {"unknown_namespace", "unknown_identifier", "unknown_function"}
    return False


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-iterations", type=int, default=24)
    args = parser.parse_args()
    WORK.mkdir(parents=True, exist_ok=True)
    original = TARGET.read_text(encoding="utf-8")
    original_lines = original.splitlines(keepends=True)
    history: list[dict[str, object]] = []
    frontier = run_lean("iteration-000", max_errors=1)
    history.append({"iteration": 0, "frontier": asdict(frontier), "accepted": None})

    for iteration in range(1, args.max_iterations + 1):
        if frontier.exit_code == 0:
            break
        current_text = TARGET.read_text(encoding="utf-8")
        lines = current_text.splitlines(keepends=True)
        candidates = candidate_edits(frontier, lines)
        accepted = False
        for candidate_index, (label, changed) in enumerate(candidates, 1):
            TARGET.write_text("".join(changed), encoding="utf-8")
            candidate_frontier = run_lean(
                f"iteration-{iteration:03d}-candidate-{candidate_index:02d}", max_errors=1
            )
            if better(frontier, candidate_frontier):
                history.append({
                    "iteration": iteration,
                    "frontier_before": asdict(frontier),
                    "accepted": label,
                    "frontier_after": asdict(candidate_frontier),
                })
                frontier = candidate_frontier
                accepted = True
                break
            TARGET.write_text(current_text, encoding="utf-8")
        if not accepted:
            history.append({
                "iteration": iteration,
                "frontier_before": asdict(frontier),
                "accepted": None,
                "candidate_count": len(candidates),
            })
            break

    final = run_lean("final-full", max_errors=1000)
    repaired = TARGET.read_text(encoding="utf-8")
    diff = "".join(difflib.unified_diff(
        original.splitlines(keepends=True),
        repaired.splitlines(keepends=True),
        fromfile="Mock2_FunctionalAnalysis.before.lean",
        tofile="Mock2_FunctionalAnalysis.after.lean",
    ))
    (WORK / "repair-history.json").write_text(
        json.dumps(history, ensure_ascii=False, indent=2), encoding="utf-8"
    )
    (WORK / "candidate.patch").write_text(diff, encoding="utf-8")
    (WORK / "final-frontier.json").write_text(
        json.dumps(asdict(final), ensure_ascii=False, indent=2), encoding="utf-8"
    )
    (WORK / "candidate.lean").write_text(repaired, encoding="utf-8")
    print(json.dumps(asdict(final), ensure_ascii=False))
    return 0 if final.exit_code == 0 and final.error_count == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
