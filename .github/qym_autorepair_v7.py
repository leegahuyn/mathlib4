#!/usr/bin/env python3
"""Verified one-frontier Lean autorepair driver for the QYM/FA recovery branch.

The script never treats candidate generation as progress.  A source is selected only
when a direct Lean run strictly improves the verified metric tuple
(error count, first error position).  It supports three workflow phases:

  prepare    compile the current baseline and locate the first failing declaration
  candidate  patch that declaration with one independent proof strategy and compile
  select     choose and install only a strictly verified improvement
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Iterable

ROOT = Path(__file__).resolve().parents[1]
WORK = ROOT / ".qym_v7"
DEFAULT_TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
LEAN_TIMEOUT_SECONDS = int(os.environ.get("LEAN_TIMEOUT_SECONDS", "10800"))

ERROR_RE = re.compile(
    r"(?m)^(?P<file>[^\n:]*?\.lean):(?P<line>\d+):(?P<col>\d+):\s+error:"
)
DECL_RE = re.compile(
    r"^(?:private\s+|protected\s+|noncomputable\s+)?"
    r"(?P<kind>theorem|lemma|example|instance)\b"
)
BOUNDARY_RE = re.compile(
    r"^(?:@\[|private\s+|protected\s+|noncomputable\s+)?"
    r"(?:theorem|lemma|example|instance|def|abbrev|opaque|structure|class|inductive|"
    r"namespace|section|end\b|open\b|variable\b|variables\b|include\b|omit\b|"
    r"local\b|attribute\b|macro\b|syntax\b)"
)


@dataclass(frozen=True)
class Metric:
    exit_code: int
    errors: int
    first_file: str
    first_line: int
    first_col: int
    timed_out: bool
    elapsed_seconds: float

    @property
    def score(self) -> tuple[int, int, int, int]:
        # Lower is better.  For equal error counts, a later first error is better.
        unusable = 1 if (self.timed_out or (self.exit_code != 0 and self.errors == 0)) else 0
        error_value = self.errors if self.errors else (0 if self.exit_code == 0 else 10**9)
        return (unusable, error_value, -self.first_line, -self.first_col)


@dataclass(frozen=True)
class Declaration:
    file: str
    error_line: int
    start_line: int
    end_line: int
    kind: str
    name: str
    by_offset: int
    boundary_offset: int


def rel(path: Path) -> str:
    try:
        return path.resolve().relative_to(ROOT.resolve()).as_posix()
    except ValueError:
        return path.as_posix()


def run_lean(target: Path, log_path: Path) -> Metric:
    log_path.parent.mkdir(parents=True, exist_ok=True)
    command = ["lake", "env", "lean", rel(target)]
    started = time.monotonic()
    timed_out = False
    try:
        proc = subprocess.run(
            command,
            cwd=ROOT,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=LEAN_TIMEOUT_SECONDS,
            check=False,
        )
        output = proc.stdout or ""
        exit_code = proc.returncode
    except subprocess.TimeoutExpired as exc:
        timed_out = True
        output = (exc.stdout or "") if isinstance(exc.stdout, str) else ""
        if exc.stderr:
            output += "\n" + (exc.stderr if isinstance(exc.stderr, str) else "")
        output += f"\nAUTOREPAIR_TIMEOUT after {LEAN_TIMEOUT_SECONDS}s\n"
        exit_code = 124

    elapsed = time.monotonic() - started
    log_path.write_text(output, encoding="utf-8", errors="replace")
    matches = list(ERROR_RE.finditer(output))
    if matches:
        first = matches[0]
        first_file = first.group("file")
        first_line = int(first.group("line"))
        first_col = int(first.group("col"))
    else:
        first_file = ""
        first_line = 10**9 if exit_code == 0 else 0
        first_col = 10**9 if exit_code == 0 else 0
    return Metric(
        exit_code=exit_code,
        errors=len(matches),
        first_file=first_file,
        first_line=first_line,
        first_col=first_col,
        timed_out=timed_out,
        elapsed_seconds=round(elapsed, 3),
    )


def resolve_error_file(metric: Metric, fallback: Path) -> Path:
    if metric.first_file:
        raw = Path(metric.first_file)
        candidates = [raw, ROOT / raw]
        if raw.name:
            candidates.extend(ROOT.rglob(raw.name))
        for candidate in candidates:
            if candidate.is_file():
                return candidate.resolve()
    return fallback.resolve()


def declaration_name(line: str, kind: str) -> str:
    rest = line
    for prefix in ("private ", "protected ", "noncomputable "):
        if rest.startswith(prefix):
            rest = rest[len(prefix):]
    rest = rest[len(kind):].lstrip()
    if kind == "instance" and (not rest or rest.startswith(":") or rest.startswith("[")):
        return "<anonymous-instance>"
    match = re.match(r"([^\s(:{\[]+)", rest)
    return match.group(1) if match else f"<{kind}>"


def locate_declaration(path: Path, error_line: int) -> Declaration:
    text = path.read_text(encoding="utf-8")
    lines = text.splitlines(keepends=True)
    if not lines:
        raise RuntimeError(f"empty Lean file: {path}")
    idx = max(0, min(len(lines) - 1, error_line - 1))

    start = None
    kind = ""
    for i in range(idx, -1, -1):
        if lines[i].startswith((" ", "\t")):
            continue
        match = DECL_RE.match(lines[i].rstrip("\n"))
        if match:
            start = i
            kind = match.group("kind")
            break
    if start is None:
        raise RuntimeError(f"could not locate theorem/lemma/instance before {path}:{error_line}")

    boundary = len(lines)
    for i in range(start + 1, len(lines)):
        raw = lines[i]
        if raw.startswith((" ", "\t")) or not raw.strip():
            continue
        if BOUNDARY_RE.match(raw.rstrip("\n")):
            boundary = i
            break

    offsets = [0]
    for line in lines:
        offsets.append(offsets[-1] + len(line))
    region_start = offsets[start]
    region_end = offsets[boundary]
    region = text[region_start:region_end]
    proof = re.search(r":=\s*by\b", region)
    if not proof:
        raise RuntimeError(
            f"declaration {path}:{start + 1}-{boundary} has no replaceable ':= by' proof"
        )
    by_in_region = region.find("by", proof.start())
    if by_in_region < 0:
        raise RuntimeError("internal proof-offset failure")

    first_line = lines[start].rstrip("\n")
    return Declaration(
        file=rel(path),
        error_line=error_line,
        start_line=start + 1,
        end_line=boundary,
        kind=kind,
        name=declaration_name(first_line, kind),
        by_offset=region_start + by_in_region,
        boundary_offset=region_end,
    )


def proof_templates() -> dict[str, str]:
    return {
        "simp": "by\n  simp",
        "simp_scaling": "by\n  simp [gammaTwoCuspScaling]",
        "simp_all_scaling": "by\n  simp_all [gammaTwoCuspScaling]",
        "aesop": "by\n  aesop",
        "aesop_scaling": "by\n  aesop (add simp [gammaTwoCuspScaling])",
        "cases_cusp_simp": (
            "by\n  cases ‹GammaTwoCusp› <;> simp [gammaTwoCuspScaling]"
        ),
        "cases_cusp_rfl": "by\n  cases ‹GammaTwoCusp› <;> rfl",
        "ext_simp": "by\n  ext <;> simp [gammaTwoCuspScaling]",
        "ext_matrix_norm": (
            "by\n  ext i j <;> fin_cases i <;> fin_cases j <;>\n"
            "    norm_num [gammaTwoCuspScaling, Matrix.mul_apply]"
        ),
        "group": "by\n  group",
        "noncomm_ring": "by\n  noncomm_ring",
        "simpa_mul_inv": "by\n  simpa only [mul_inv_cancel]",
        "simpa_inv_mul": "by\n  simpa only [inv_mul_cancel]",
        "change_simp": "by\n  change _\n  simp [gammaTwoCuspScaling]",
        "all_goals_simp": "by\n  all_goals simp [gammaTwoCuspScaling]",
        "exact_by_contra_aesop": "by\n  by_contra h\n  aesop",
    }


def patch_source(original: str, decl: Declaration, candidate_id: str) -> str:
    if candidate_id in proof_templates():
        proof = proof_templates()[candidate_id]
        suffix = original[decl.boundary_offset:]
        # Keep exactly one blank separator before the next top-level command.
        return original[:decl.by_offset] + proof.rstrip() + "\n\n" + suffix.lstrip("\n")

    old_proof = original[decl.by_offset:decl.boundary_offset]
    transformed = old_proof
    if candidate_id == "api_group_names":
        transformed = transformed.replace("mul_inv_cancel₀", "mul_inv_cancel")
        transformed = transformed.replace("inv_mul_cancel₀", "inv_mul_cancel")
        transformed = transformed.replace("mul_inv_rev₀", "mul_inv_rev")
        transformed = transformed.replace("inv_mul_rev₀", "inv_mul_rev")
    elif candidate_id == "api_zero_names":
        transformed = re.sub(r"\bmul_inv_cancel\b", "mul_inv_cancel₀", transformed)
        transformed = re.sub(r"\binv_mul_cancel\b", "inv_mul_cancel₀", transformed)
        transformed = re.sub(r"\bmul_inv_rev\b", "mul_inv_rev₀", transformed)
        transformed = re.sub(r"\binv_mul_rev\b", "inv_mul_rev₀", transformed)
    elif candidate_id == "prepend_simp":
        transformed = re.sub(r"^by\s*", "by\n  simp [gammaTwoCuspScaling]\n", transformed, count=1)
    elif candidate_id == "prepend_classical_simp":
        transformed = re.sub(
            r"^by\s*",
            "by\n  classical\n  simp [gammaTwoCuspScaling]\n",
            transformed,
            count=1,
        )
    else:
        raise KeyError(f"unknown candidate id: {candidate_id}")
    if transformed == old_proof:
        raise RuntimeError(f"candidate {candidate_id} made no textual change")
    return original[:decl.by_offset] + transformed + original[decl.boundary_offset:]


def write_json(path: Path, data: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def prepare(target: Path) -> int:
    WORK.mkdir(parents=True, exist_ok=True)
    metric = run_lean(target, WORK / "baseline.log")
    error_file = resolve_error_file(metric, target)
    payload: dict[str, object] = {
        "target": rel(target),
        "metric": asdict(metric),
        "score": metric.score,
    }
    if metric.exit_code == 0 and metric.errors == 0:
        payload["status"] = "ZERO_ERROR"
        write_json(WORK / "diagnostic.json", payload)
        return 0
    if metric.timed_out or metric.errors == 0:
        payload["status"] = "UNUSABLE_BASELINE"
        write_json(WORK / "diagnostic.json", payload)
        return 2
    decl = locate_declaration(error_file, metric.first_line)
    payload["status"] = "CANDIDATE_READY"
    payload["declaration"] = asdict(decl)
    write_json(WORK / "diagnostic.json", payload)
    return 0


def candidate(target: Path, candidate_id: str) -> int:
    diagnostic = json.loads((WORK / "diagnostic.json").read_text(encoding="utf-8"))
    if diagnostic.get("status") != "CANDIDATE_READY":
        raise RuntimeError(f"baseline is not candidate-ready: {diagnostic.get('status')}")
    decl = Declaration(**diagnostic["declaration"])
    source_path = ROOT / decl.file
    original = source_path.read_text(encoding="utf-8")
    out_dir = WORK / f"candidate_{candidate_id}"
    out_dir.mkdir(parents=True, exist_ok=True)
    try:
        patched = patch_source(original, decl, candidate_id)
    except Exception as exc:
        write_json(
            out_dir / "metrics.json",
            {
                "candidate": candidate_id,
                "valid": False,
                "reason": f"patch failure: {exc}",
                "metric": {
                    "exit_code": 125,
                    "errors": 10**9,
                    "first_file": decl.file,
                    "first_line": 0,
                    "first_col": 0,
                    "timed_out": False,
                    "elapsed_seconds": 0.0,
                },
            },
        )
        return 0

    source_path.write_text(patched, encoding="utf-8")
    metric = run_lean(target, out_dir / "lean.log")
    (out_dir / "source.lean").write_text(patched, encoding="utf-8")
    write_json(
        out_dir / "metrics.json",
        {
            "candidate": candidate_id,
            "valid": True,
            "declaration": asdict(decl),
            "metric": asdict(metric),
            "score": metric.score,
        },
    )
    source_path.write_text(original, encoding="utf-8")
    return 0


def metric_from_dict(data: dict[str, object]) -> Metric:
    return Metric(
        exit_code=int(data["exit_code"]),
        errors=int(data["errors"]),
        first_file=str(data["first_file"]),
        first_line=int(data["first_line"]),
        first_col=int(data["first_col"]),
        timed_out=bool(data["timed_out"]),
        elapsed_seconds=float(data["elapsed_seconds"]),
    )


def github_output(**values: object) -> None:
    output = os.environ.get("GITHUB_OUTPUT")
    if not output:
        return
    with open(output, "a", encoding="utf-8") as handle:
        for key, value in values.items():
            handle.write(f"{key}={str(value).lower() if isinstance(value, bool) else value}\n")


def select(download_root: Path) -> int:
    baseline_data = json.loads((WORK / "diagnostic.json").read_text(encoding="utf-8"))
    baseline = metric_from_dict(baseline_data["metric"])
    decl_data = baseline_data.get("declaration")
    if not decl_data:
        state = {
            "status": baseline_data.get("status", "NO_DECLARATION"),
            "baseline": asdict(baseline),
            "selected": None,
        }
        write_json(ROOT / ".github" / "qym_autorepair_v7_state.json", state)
        github_output(improved=False, zero=(baseline.exit_code == 0), errors=baseline.errors)
        return 0
    decl = Declaration(**decl_data)

    rows: list[tuple[Metric, str, Path, dict[str, object]]] = []
    for metrics_path in download_root.rglob("metrics.json"):
        try:
            row = json.loads(metrics_path.read_text(encoding="utf-8"))
            if not row.get("valid"):
                continue
            metric = metric_from_dict(row["metric"])
            source_path = metrics_path.parent / "source.lean"
            if source_path.is_file():
                rows.append((metric, str(row["candidate"]), source_path, row))
        except Exception:
            continue

    rows.sort(key=lambda item: (item[0].score, item[1]))
    best = rows[0] if rows else None
    improved = bool(best and best[0].score < baseline.score)
    selected_name = best[1] if improved and best else None
    selected_metric = best[0] if improved and best else baseline

    if improved and best:
        destination = ROOT / decl.file
        shutil.copyfile(best[2], destination)
        status = "ZERO_ERROR" if best[0].exit_code == 0 and best[0].errors == 0 else "IMPROVED"
    else:
        status = "NO_STRICT_IMPROVEMENT"

    state = {
        "status": status,
        "declaration": asdict(decl),
        "baseline": asdict(baseline),
        "baseline_score": baseline.score,
        "selected": selected_name,
        "selected_metric": asdict(selected_metric),
        "selected_score": selected_metric.score,
        "candidates_considered": [
            {
                "candidate": name,
                "metric": asdict(metric),
                "score": metric.score,
            }
            for metric, name, _path, _row in rows
        ],
    }
    write_json(ROOT / ".github" / "qym_autorepair_v7_state.json", state)
    github_output(
        improved=improved,
        zero=(selected_metric.exit_code == 0 and selected_metric.errors == 0),
        errors=selected_metric.errors,
        selected=selected_name or "none",
        first_line=selected_metric.first_line,
    )
    return 0


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("mode", choices=("prepare", "candidate", "select"))
    parser.add_argument("--target", default=os.environ.get("TARGET", rel(DEFAULT_TARGET)))
    parser.add_argument("--candidate", default="")
    parser.add_argument("--downloads", default=str(WORK / "downloads"))
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    target = (ROOT / args.target).resolve()
    if not target.is_file():
        raise FileNotFoundError(target)
    if args.mode == "prepare":
        return prepare(target)
    if args.mode == "candidate":
        if not args.candidate:
            raise ValueError("--candidate is required")
        return candidate(target, args.candidate)
    return select(Path(args.downloads).resolve())


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as exc:
        print(f"AUTOREPAIR_FATAL: {exc}", file=sys.stderr)
        raise
