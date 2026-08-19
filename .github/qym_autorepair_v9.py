#!/usr/bin/env python3
"""Persistent prefix-filtered direct-Lean repair loop for FA followed by QYM.

Each round:
  1. verifies the current full target;
  2. locates the declaration containing the first actual Lean error;
  3. checks many independent proof strategies on a closed source prefix;
  4. full-compiles only prefix-clean candidates;
  5. commits/pushes only a strict direct-Lean metric improvement.

The loop first verifies Mock2_FunctionalAnalysis.lean, then QYM.lean.  It never
uses workflow success, generated candidates, or source position alone as PASS.
"""

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
import sys
import time
from pathlib import Path
from typing import Iterable, Sequence

ROOT = Path(__file__).resolve().parents[1]
WORK = ROOT / ".qym_v9"
STATE = ROOT / ".github" / "qym_autorepair_v9_state.json"
FULL_TIMEOUT = int(os.environ.get("LEAN_TIMEOUT_SECONDS", "10800"))
PREFIX_TIMEOUT = int(os.environ.get("PREFIX_TIMEOUT_SECONDS", "1800"))
MAX_ROUNDS = int(os.environ.get("MAX_V9_ROUNDS", "40"))
MAX_WORKERS = int(os.environ.get("V9_PREFIX_WORKERS", "3"))
MAX_FULL_CANDIDATES = int(os.environ.get("V9_MAX_FULL_CANDIDATES", "4"))
BRANCH = os.environ.get("BRANCH", "gpt/qym-gb85-c2-v6-mulinv-20260819")

ERROR_RE = re.compile(
    r"(?m)^(?P<file>[^\n:]*?\.lean):(?P<line>\d+):(?P<col>\d+):\s+error:"
)
DECL_RE = re.compile(
    r"^(?:private\s+|protected\s+|noncomputable\s+)?"
    r"(?P<kind>theorem|lemma|example|instance)\b"
)
TOP_COMMAND_RE = re.compile(
    r"^(?:private\s+|protected\s+|noncomputable\s+)?"
    r"(?:theorem|lemma|example|instance|def|abbrev|opaque|structure|class|inductive|"
    r"namespace|section|end\b|open\b|variable\b|variables\b|include\b|omit\b|"
    r"local\b|attribute\b|macro\b|syntax\b|set_option\b)"
)


@dataclasses.dataclass(frozen=True)
class Metric:
    exit_code: int
    errors: int
    first_file: str
    first_line: int
    first_col: int
    timed_out: bool
    elapsed_seconds: float
    log: str = ""

    @property
    def zero(self) -> bool:
        return self.exit_code == 0 and self.errors == 0 and not self.timed_out

    @property
    def usable(self) -> bool:
        return self.zero or (not self.timed_out and self.errors > 0)

    @property
    def score(self) -> tuple[int, int, int, int]:
        if not self.usable:
            return (1, 10**9, 0, 0)
        return (0, self.errors, -self.first_line, -self.first_col)

    def public(self) -> dict[str, object]:
        data = dataclasses.asdict(self)
        data.pop("log", None)
        data["score"] = self.score
        data["zero"] = self.zero
        return data


@dataclasses.dataclass(frozen=True)
class Declaration:
    file: str
    error_line: int
    start_line: int
    end_line: int
    kind: str
    name: str
    by_offset: int
    boundary_offset: int


@dataclasses.dataclass(frozen=True)
class Candidate:
    name: str
    source: str
    proof: str


def relative(path: Path) -> str:
    return path.resolve().relative_to(ROOT.resolve()).as_posix()


def write_json(path: Path, data: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def run_lean(path: Path, timeout: int, log_path: Path | None = None) -> Metric:
    started = time.monotonic()
    timed_out = False
    command = ["lake", "env", "lean", relative(path)]
    try:
        result = subprocess.run(
            command,
            cwd=ROOT,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=timeout,
            check=False,
        )
        output = result.stdout or ""
        code = result.returncode
    except subprocess.TimeoutExpired as exc:
        timed_out = True
        output = exc.stdout if isinstance(exc.stdout, str) else ""
        output += f"\nV9_TIMEOUT after {timeout}s\n"
        code = 124
    elapsed = time.monotonic() - started
    if log_path is not None:
        log_path.parent.mkdir(parents=True, exist_ok=True)
        log_path.write_text(output, encoding="utf-8", errors="replace")
    matches = list(ERROR_RE.finditer(output))
    if matches:
        first = matches[0]
        first_file = first.group("file")
        first_line = int(first.group("line"))
        first_col = int(first.group("col"))
    else:
        first_file = ""
        first_line = 10**9 if code == 0 else 0
        first_col = 10**9 if code == 0 else 0
    return Metric(
        exit_code=code,
        errors=len(matches),
        first_file=first_file,
        first_line=first_line,
        first_col=first_col,
        timed_out=timed_out,
        elapsed_seconds=round(elapsed, 3),
        log=output,
    )


def resolve_error_file(metric: Metric, target: Path) -> Path:
    if metric.first_file:
        raw = Path(metric.first_file)
        direct = raw if raw.is_absolute() else ROOT / raw
        if direct.is_file():
            return direct.resolve()
        matches = [p for p in ROOT.rglob(raw.name) if ".lake" not in p.parts and ".git" not in p.parts]
        if len(matches) == 1:
            return matches[0].resolve()
        for match in matches:
            if match.as_posix().endswith(raw.as_posix()):
                return match.resolve()
    return target.resolve()


def line_offsets(lines: Sequence[str]) -> list[int]:
    offsets = [0]
    for line in lines:
        offsets.append(offsets[-1] + len(line))
    return offsets


def declaration_name(line: str, kind: str) -> str:
    stripped = line.strip()
    for prefix in ("private ", "protected ", "noncomputable "):
        if stripped.startswith(prefix):
            stripped = stripped[len(prefix):]
    stripped = stripped[len(kind):].lstrip()
    found = re.match(r"([^\s(:{\[]+)", stripped)
    return found.group(1) if found else f"<{kind}>"


def locate_declaration(path: Path, error_line: int) -> Declaration:
    text = path.read_text(encoding="utf-8")
    lines = text.splitlines(keepends=True)
    if not lines:
        raise RuntimeError(f"empty file: {path}")
    index = max(0, min(len(lines) - 1, error_line - 1))
    start = None
    kind = ""
    for i in range(index, -1, -1):
        raw = lines[i]
        if raw.startswith((" ", "\t")):
            continue
        match = DECL_RE.match(raw.rstrip("\n"))
        if match:
            start = i
            kind = match.group("kind")
            break
    if start is None:
        raise RuntimeError(f"no proof declaration before {relative(path)}:{error_line}")

    boundary = len(lines)
    for i in range(start + 1, len(lines)):
        raw = lines[i]
        if raw.startswith((" ", "\t")) or not raw.strip():
            continue
        if raw.startswith("@[") or TOP_COMMAND_RE.match(raw.rstrip("\n")):
            boundary = i
            break

    offsets = line_offsets(lines)
    region_start = offsets[start]
    region_end = offsets[boundary]
    region = text[region_start:region_end]
    proof = re.search(r":=\s*by\b", region)
    if not proof:
        raise RuntimeError(
            f"{relative(path)}:{start + 1}-{boundary} has no replaceable ':= by' proof"
        )
    by_rel = region.find("by", proof.start())
    if by_rel < 0:
        raise RuntimeError("proof-offset failure")
    return Declaration(
        file=relative(path),
        error_line=error_line,
        start_line=start + 1,
        end_line=boundary,
        kind=kind,
        name=declaration_name(lines[start], kind),
        by_offset=region_start + by_rel,
        boundary_offset=region_end,
    )


def extract_suggestions(log: str) -> list[str]:
    suggestions: list[str] = []
    for line in log.splitlines():
        stripped = line.strip()
        for prefix in ("Try this: ", "try this: "):
            if stripped.startswith(prefix):
                tactic = stripped[len(prefix):].strip()
                if tactic and not tactic.startswith("by"):
                    tactic = "by\n  " + tactic
                suggestions.append(tactic)
    return suggestions[:8]


def proof_templates() -> list[tuple[str, str]]:
    return [
        ("rfl", "by\n  rfl"),
        ("simp", "by\n  simp"),
        ("simpa", "by\n  simpa"),
        ("simp_scaling", "by\n  simp [gammaTwoCuspScaling]"),
        ("simp_matrix", "by\n  simp [gammaTwoCuspScaling, Matrix.mul_apply]"),
        ("classical_simp", "by\n  classical\n  simp"),
        ("classical_scaling", "by\n  classical\n  simp [gammaTwoCuspScaling, Matrix.mul_apply]"),
        ("simp_all", "by\n  simp_all [gammaTwoCuspScaling, Matrix.mul_apply]"),
        ("aesop", "by\n  aesop"),
        ("classical_aesop", "by\n  classical\n  aesop"),
        ("exact_search", "by\n  exact?"),
        ("simp_search", "by\n  simp?"),
        ("aesop_search", "by\n  aesop?"),
        ("apply_search", "by\n  apply?"),
        ("grind", "by\n  grind"),
        ("omega", "by\n  omega"),
        ("norm_num", "by\n  norm_num"),
        ("norm_num_scaling", "by\n  norm_num [gammaTwoCuspScaling, Matrix.mul_apply]"),
        ("ring", "by\n  ring"),
        ("ring_nf", "by\n  ring_nf"),
        ("noncomm_ring", "by\n  noncomm_ring"),
        ("positivity", "by\n  positivity"),
        ("continuity", "by\n  continuity"),
        ("fun_prop", "by\n  fun_prop"),
        ("measurability", "by\n  measurability"),
        ("decide", "by\n  decide"),
        ("native_decide", "by\n  native_decide"),
        ("subsingleton", "by\n  apply Subsingleton.elim"),
        ("constructor_simp", "by\n  constructor <;> simp [gammaTwoCuspScaling]"),
        ("ext_simp", "by\n  ext <;> simp [gammaTwoCuspScaling, Matrix.mul_apply]"),
        ("ext_exact", "by\n  ext <;> exact?"),
        ("cusp_cases_rfl", "by\n  cases ‹GammaTwoCusp› <;> rfl"),
        ("cusp_cases_simp", "by\n  cases ‹GammaTwoCusp› <;> simp [gammaTwoCuspScaling]"),
        ("cusp_cases_decide", "by\n  cases ‹GammaTwoCusp› <;> decide"),
        ("cusp_cases_native", "by\n  cases ‹GammaTwoCusp› <;> native_decide"),
        (
            "cusp_matrix_ext",
            "by\n  cases ‹GammaTwoCusp› <;> ext i j <;> fin_cases i <;> fin_cases j <;>\n"
            "    norm_num [gammaTwoCuspScaling, Matrix.mul_apply]",
        ),
        (
            "mul_inv_cusp",
            "by\n  simpa using (mul_inv_cancel (gammaTwoCuspScaling ‹GammaTwoCusp›))",
        ),
        (
            "inv_mul_cusp",
            "by\n  simpa using (inv_mul_cancel (gammaTwoCuspScaling ‹GammaTwoCusp›))",
        ),
        ("rw_mul_inv", "by\n  rw [mul_inv_cancel]"),
        ("rw_inv_mul", "by\n  rw [inv_mul_cancel]"),
        ("group", "by\n  group"),
    ]


def transformed_proofs(old_proof: str) -> list[tuple[str, str]]:
    transforms: list[tuple[str, list[tuple[str, str]]]] = [
        (
            "drop_zero_suffix",
            [
                ("mul_inv_cancel₀", "mul_inv_cancel"),
                ("inv_mul_cancel₀", "inv_mul_cancel"),
                ("mul_inv_rev₀", "mul_inv_rev"),
                ("inv_mul_rev₀", "inv_mul_rev"),
            ],
        ),
        (
            "add_zero_suffix",
            [
                ("mul_inv_cancel", "mul_inv_cancel₀"),
                ("inv_mul_cancel", "inv_mul_cancel₀"),
                ("mul_inv_rev", "mul_inv_rev₀"),
                ("inv_mul_rev", "inv_mul_rev₀"),
            ],
        ),
        ("mul_to_inv", [("mul_inv_cancel", "inv_mul_cancel")]),
        ("inv_to_mul", [("inv_mul_cancel", "mul_inv_cancel")]),
        ("rev_drop_zero", [("inv_mul_rev₀", "inv_mul_rev"), ("mul_inv_rev₀", "mul_inv_rev")]),
    ]
    results: list[tuple[str, str]] = []
    for name, changes in transforms:
        proof = old_proof
        for old, new in changes:
            proof = proof.replace(old, new)
        if proof != old_proof:
            results.append((name, proof.rstrip()))
    if old_proof.startswith("by"):
        body = old_proof[2:].lstrip("\n ")
        results.append(("classical_original", "by\n  classical\n" + body))
    return results


def make_candidates(source: str, decl: Declaration, log: str) -> list[Candidate]:
    old_proof = source[decl.by_offset:decl.boundary_offset]
    variants = proof_templates() + transformed_proofs(old_proof)
    for idx, suggestion in enumerate(extract_suggestions(log)):
        variants.insert(0, (f"suggestion_{idx}", suggestion))

    seen: set[str] = set()
    candidates: list[Candidate] = []
    for name, proof in variants:
        proof = proof.rstrip()
        if not proof.startswith("by") or proof in seen:
            continue
        seen.add(proof)
        patched = source[:decl.by_offset] + proof + "\n\n" + source[decl.boundary_offset:].lstrip("\n")
        candidates.append(Candidate(name=name, source=patched, proof=proof))
    return candidates


def uncommented_top_level(line: str, in_block: int) -> tuple[str, int]:
    out: list[str] = []
    i = 0
    while i < len(line):
        if in_block:
            if line.startswith("/-", i):
                in_block += 1
                i += 2
            elif line.startswith("-/", i):
                in_block -= 1
                i += 2
            else:
                i += 1
            continue
        if line.startswith("--", i):
            break
        if line.startswith("/-", i):
            in_block += 1
            i += 2
            continue
        out.append(line[i])
        i += 1
    return "".join(out), in_block


def closing_commands(prefix: str) -> str:
    stack: list[tuple[str, str]] = []
    in_block = 0
    for raw in prefix.splitlines():
        clean, in_block = uncommented_top_level(raw, in_block)
        if clean.startswith((" ", "\t")):
            continue
        stripped = clean.strip()
        match = re.match(r"^(namespace|section)\b\s*([^\s]+)?", stripped)
        if match:
            stack.append((match.group(1), match.group(2) or ""))
            continue
        if re.match(r"^end\b", stripped) and stack:
            stack.pop()
    endings = []
    for _kind, name in reversed(stack):
        endings.append(f"end {name}" if name else "end")
    return "\n" + "\n".join(endings) + "\n" if endings else "\n"


def prefix_source(candidate: Candidate, decl: Declaration) -> str:
    prefix = candidate.source[:decl.boundary_offset]
    return prefix.rstrip() + "\n" + closing_commands(prefix)


def safe_id(name: str) -> str:
    return re.sub(r"[^A-Za-z0-9_.-]+", "_", name)


def test_prefix(candidate: Candidate, decl: Declaration, round_dir: Path) -> tuple[Candidate, Metric, Path]:
    digest = hashlib.sha256(candidate.proof.encode("utf-8")).hexdigest()[:10]
    stem = f"QYMRepairV9_{safe_id(candidate.name)}_{digest}"
    temp = ROOT / "PrimalitySheafVerification" / f"{stem}.lean"
    log_path = round_dir / "prefix_logs" / f"{stem}.log"
    try:
        temp.write_text(prefix_source(candidate, decl), encoding="utf-8")
        metric = run_lean(temp, PREFIX_TIMEOUT, log_path)
        return candidate, metric, log_path
    finally:
        temp.unlink(missing_ok=True)


def strict_improvement(candidate: Metric, baseline: Metric) -> bool:
    return candidate.usable and candidate.score < baseline.score


def git_checkpoint(source_path: Path | None, state: dict[str, object], message: str) -> None:
    write_json(STATE, state)
    subprocess.run(["git", "add", str(STATE.relative_to(ROOT))], cwd=ROOT, check=True)
    if source_path is not None:
        subprocess.run(["git", "add", relative(source_path)], cwd=ROOT, check=True)
    diff = subprocess.run(["git", "diff", "--cached", "--quiet"], cwd=ROOT, check=False)
    if diff.returncode == 0:
        return
    subprocess.run(["git", "commit", "-m", message], cwd=ROOT, check=True)
    subprocess.run(["git", "push", "origin", f"HEAD:{BRANCH}"], cwd=ROOT, check=True)


def preferred_targets() -> list[Path]:
    targets: list[Path] = []
    fa = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
    if fa.is_file():
        targets.append(fa)

    exact_qym = ROOT / "PrimalitySheafVerification" / "QYM.lean"
    if exact_qym.is_file():
        targets.append(exact_qym)
    else:
        matches = [
            p for p in (ROOT / "PrimalitySheafVerification").glob("*QYM*.lean")
            if "Repair" not in p.name and "candidate" not in p.name.lower()
        ]
        if matches:
            matches.sort(key=lambda p: (-p.stat().st_size, p.name))
            targets.append(matches[0])
    return targets


def repair_target(target: Path, global_state: dict[str, object]) -> tuple[bool, dict[str, object]]:
    target_name = relative(target)
    target_state: dict[str, object] = {
        "target": target_name,
        "status": "RUNNING",
        "rounds": [],
    }
    global_state.setdefault("targets", {})[target_name] = target_state
    baseline_log = WORK / safe_id(target.stem) / "baseline.log"
    baseline = run_lean(target, FULL_TIMEOUT, baseline_log)
    target_state["initial_metric"] = baseline.public()

    if baseline.zero:
        target_state["status"] = "ZERO_ERROR"
        target_state["final_metric"] = baseline.public()
        git_checkpoint(None, global_state, f"QYM v9 verify {target.stem}: zero errors")
        return True, global_state
    if not baseline.usable:
        target_state["status"] = "UNUSABLE_BASELINE"
        target_state["final_metric"] = baseline.public()
        git_checkpoint(None, global_state, f"QYM v9 diagnostic: unusable {target.stem} baseline")
        return False, global_state

    for round_index in range(1, MAX_ROUNDS + 1):
        round_dir = WORK / safe_id(target.stem) / f"round_{round_index:03d}"
        round_dir.mkdir(parents=True, exist_ok=True)
        error_file = resolve_error_file(baseline, target)
        source = error_file.read_text(encoding="utf-8")
        try:
            decl = locate_declaration(error_file, baseline.first_line)
        except Exception as exc:
            round_state = {
                "round": round_index,
                "status": "NO_REPLACEABLE_DECLARATION",
                "baseline": baseline.public(),
                "reason": str(exc),
            }
            target_state["rounds"].append(round_state)
            target_state["status"] = "BLOCKED"
            target_state["final_metric"] = baseline.public()
            git_checkpoint(None, global_state, f"QYM v9 blocked at {target.stem}:{baseline.first_line}")
            return False, global_state

        candidates = make_candidates(source, decl, baseline.log)
        prefix_results: list[tuple[Candidate, Metric, Path]] = []
        with concurrent.futures.ThreadPoolExecutor(max_workers=MAX_WORKERS) as pool:
            futures = [pool.submit(test_prefix, c, decl, round_dir) for c in candidates]
            for future in concurrent.futures.as_completed(futures):
                try:
                    prefix_results.append(future.result())
                except Exception:
                    continue

        passing = [row for row in prefix_results if row[1].zero]
        order = {candidate.name: idx for idx, candidate in enumerate(candidates)}
        passing.sort(key=lambda row: order.get(row[0].name, 10**9))
        best_source: str | None = None
        best_metric: Metric | None = None
        best_name = ""
        full_attempts: list[dict[str, object]] = []

        for candidate, prefix_metric, _prefix_log in passing[:MAX_FULL_CANDIDATES]:
            error_file.write_text(candidate.source, encoding="utf-8")
            full_log = round_dir / f"full_{safe_id(candidate.name)}.log"
            metric = run_lean(target, FULL_TIMEOUT, full_log)
            full_attempts.append({
                "candidate": candidate.name,
                "prefix": prefix_metric.public(),
                "full": metric.public(),
            })
            error_file.write_text(source, encoding="utf-8")
            if strict_improvement(metric, baseline):
                if best_metric is None or metric.score < best_metric.score:
                    best_source = candidate.source
                    best_metric = metric
                    best_name = candidate.name
                if metric.zero or metric.errors < baseline.errors:
                    break

        round_state = {
            "round": round_index,
            "declaration": dataclasses.asdict(decl),
            "baseline": baseline.public(),
            "candidate_count": len(candidates),
            "prefix_pass_count": len(passing),
            "prefix_passes": [row[0].name for row in passing],
            "full_attempts": full_attempts,
        }

        if best_source is None or best_metric is None:
            round_state["status"] = "NO_STRICT_IMPROVEMENT"
            target_state["rounds"].append(round_state)
            target_state["status"] = "BLOCKED"
            target_state["final_metric"] = baseline.public()
            git_checkpoint(None, global_state, f"QYM v9 no strict improvement at {decl.name}")
            return False, global_state

        error_file.write_text(best_source, encoding="utf-8")
        round_state["status"] = "IMPROVED"
        round_state["selected"] = best_name
        round_state["selected_metric"] = best_metric.public()
        target_state["rounds"].append(round_state)
        target_state["final_metric"] = best_metric.public()
        target_state["status"] = "ZERO_ERROR" if best_metric.zero else "IMPROVED"
        git_checkpoint(
            error_file,
            global_state,
            f"QYM v9 {target.stem}: {best_metric.errors} errors via {best_name}",
        )
        baseline = best_metric
        if baseline.zero:
            return True, global_state

    target_state["status"] = "ROUND_LIMIT"
    target_state["final_metric"] = baseline.public()
    git_checkpoint(None, global_state, f"QYM v9 round limit at {target.stem}")
    return False, global_state


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--targets", nargs="*", default=[])
    args = parser.parse_args()
    WORK.mkdir(parents=True, exist_ok=True)
    targets = [ROOT / item for item in args.targets] if args.targets else preferred_targets()
    if not targets:
        raise RuntimeError("no FA/QYM Lean target found")

    state: dict[str, object] = {
        "status": "RUNNING",
        "branch": BRANCH,
        "started_at_unix": int(time.time()),
        "targets": {},
    }
    all_zero = True
    for target in targets:
        ok, state = repair_target(target.resolve(), state)
        if not ok:
            all_zero = False
            break
    state["status"] = "ZERO_ERROR" if all_zero else "BLOCKED"
    state["finished_at_unix"] = int(time.time())
    git_checkpoint(None, state, "QYM v9 final verified state")
    return 0 if all_zero else 2


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as exc:
        failure = {
            "status": "FATAL",
            "error": repr(exc),
            "finished_at_unix": int(time.time()),
        }
        write_json(STATE, failure)
        print(f"V9_FATAL: {exc}", file=sys.stderr)
        raise
