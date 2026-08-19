#!/usr/bin/env python3
"""Second verified candidate family for the QYM/FA one-frontier recovery.

This driver reuses v7's direct-Lean metrics and selector, but supplies a broader
proof-search family and a stricter top-level declaration boundary.  It is a
fallback only: the workflow skips it when the verified v7 state is already
ZERO_ERROR.
"""

from __future__ import annotations

import argparse
import importlib.util
import json
import re
import sys
from dataclasses import asdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
WORK = ROOT / ".qym_v8"
V7_WORK = ROOT / ".qym_v7"

spec = importlib.util.spec_from_file_location("qym_v7", ROOT / ".github/qym_autorepair_v7.py")
if spec is None or spec.loader is None:
    raise RuntimeError("cannot load qym_autorepair_v7.py")
v7 = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = v7
spec.loader.exec_module(v7)


def boundary_offsets(text: str, start_line: int) -> tuple[int, int]:
    lines = text.splitlines(keepends=True)
    start_idx = max(0, start_line - 1)
    offsets = [0]
    for line in lines:
        offsets.append(offsets[-1] + len(line))

    boundary_idx = len(lines)
    top_command = re.compile(
        r"^(?:private\s+|protected\s+|noncomputable\s+)?"
        r"(?:theorem|lemma|example|instance|def|abbrev|opaque|structure|class|inductive|"
        r"namespace|section|end\b|open\b|variable\b|variables\b|include\b|omit\b|"
        r"local\b|attribute\b|macro\b|syntax\b)"
    )
    for idx in range(start_idx + 1, len(lines)):
        raw = lines[idx]
        if raw.startswith((" ", "\t")) or not raw.strip():
            continue
        if raw.startswith("@[") or top_command.match(raw.rstrip("\n")):
            boundary_idx = idx
            break

    region_start = offsets[start_idx]
    region_end = offsets[boundary_idx]
    region = text[region_start:region_end]
    proof = re.search(r":=\s*by\b", region)
    if not proof:
        raise RuntimeError("selected declaration has no ':= by' proof")
    by_rel = region.find("by", proof.start())
    if by_rel < 0:
        raise RuntimeError("cannot locate proof body")
    return region_start + by_rel, region_end


def templates() -> dict[str, str]:
    return {
        "classical_simp": "by\n  classical\n  simp",
        "classical_simp_scaling": "by\n  classical\n  simp [gammaTwoCuspScaling]",
        "classical_simp_matrix": (
            "by\n  classical\n  simp [gammaTwoCuspScaling, Matrix.mul_apply]"
        ),
        "exact_search": "by\n  exact?",
        "simp_search": "by\n  simp?",
        "aesop_search": "by\n  aesop?",
        "apply_search": "by\n  apply?",
        "grind": "by\n  grind",
        "omega": "by\n  omega",
        "norm_num": "by\n  norm_num",
        "norm_num_scaling": (
            "by\n  norm_num [gammaTwoCuspScaling, Matrix.mul_apply]"
        ),
        "ring": "by\n  ring",
        "ring_nf": "by\n  ring_nf",
        "native_decide": "by\n  native_decide",
        "decide": "by\n  decide",
        "cusp_native_decide": (
            "by\n  cases ‹GammaTwoCusp› <;> native_decide"
        ),
        "cusp_decide": "by\n  cases ‹GammaTwoCusp› <;> decide",
        "cusp_ext_norm": (
            "by\n  cases ‹GammaTwoCusp› <;> ext i j <;> fin_cases i <;> fin_cases j <;>\n"
            "    norm_num [gammaTwoCuspScaling, Matrix.mul_apply]"
        ),
        "cusp_ext_simp": (
            "by\n  cases ‹GammaTwoCusp› <;> ext <;> simp [gammaTwoCuspScaling, Matrix.mul_apply]"
        ),
        "exact_mul_inv_cusp": (
            "by\n  simpa using (mul_inv_cancel (gammaTwoCuspScaling ‹GammaTwoCusp›))"
        ),
        "exact_inv_mul_cusp": (
            "by\n  simpa using (inv_mul_cancel (gammaTwoCuspScaling ‹GammaTwoCusp›))"
        ),
        "rw_mul_inv": "by\n  rw [mul_inv_cancel]",
        "rw_inv_mul": "by\n  rw [inv_mul_cancel]",
        "constructor_simp": (
            "by\n  constructor <;> simp [gammaTwoCuspScaling]"
        ),
        "ext_exact_search": "by\n  ext <;> exact?",
        "classical_aesop": "by\n  classical\n  aesop",
        "classical_aesop_scaling": (
            "by\n  classical\n  simp_all [gammaTwoCuspScaling, Matrix.mul_apply] <;> aesop"
        ),
    }


def transform_original(old_proof: str, candidate_id: str) -> str:
    transformed = old_proof
    replacements: dict[str, list[tuple[str, str]]] = {
        "drop_zero_suffix": [
            ("mul_inv_cancel₀", "mul_inv_cancel"),
            ("inv_mul_cancel₀", "inv_mul_cancel"),
            ("mul_inv_rev₀", "mul_inv_rev"),
            ("inv_mul_rev₀", "inv_mul_rev"),
        ],
        "add_zero_suffix": [
            ("mul_inv_cancel", "mul_inv_cancel₀"),
            ("inv_mul_cancel", "inv_mul_cancel₀"),
            ("mul_inv_rev", "mul_inv_rev₀"),
            ("inv_mul_rev", "inv_mul_rev₀"),
        ],
        "swap_mul_inv_to_inv_mul": [
            ("mul_inv_cancel", "inv_mul_cancel"),
            ("mul_inv_cancel₀", "inv_mul_cancel₀"),
        ],
        "swap_inv_mul_to_mul_inv": [
            ("inv_mul_cancel", "mul_inv_cancel"),
            ("inv_mul_cancel₀", "mul_inv_cancel₀"),
        ],
    }
    if candidate_id not in replacements:
        raise KeyError(candidate_id)
    for old, new in replacements[candidate_id]:
        transformed = transformed.replace(old, new)
    if transformed == old_proof:
        raise RuntimeError("transformation made no change")
    return transformed


def candidate(target: Path, candidate_id: str) -> int:
    diagnostic = json.loads((V7_WORK / "diagnostic.json").read_text(encoding="utf-8"))
    if diagnostic.get("status") != "CANDIDATE_READY":
        raise RuntimeError(f"baseline is not candidate-ready: {diagnostic.get('status')}")
    decl = v7.Declaration(**diagnostic["declaration"])
    source_path = ROOT / decl.file
    original = source_path.read_text(encoding="utf-8")
    by_offset, boundary_offset = boundary_offsets(original, decl.start_line)
    out_dir = WORK / f"candidate_{candidate_id}"
    out_dir.mkdir(parents=True, exist_ok=True)

    try:
        if candidate_id in templates():
            replacement = templates()[candidate_id].rstrip()
        else:
            replacement = transform_original(original[by_offset:boundary_offset], candidate_id).rstrip()
        patched = original[:by_offset] + replacement + "\n\n" + original[boundary_offset:].lstrip("\n")
    except Exception as exc:
        v7.write_json(
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
    metric = v7.run_lean(target, out_dir / "lean.log")
    (out_dir / "source.lean").write_text(patched, encoding="utf-8")
    v7.write_json(
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


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("mode", choices=("prepare", "candidate", "select"))
    parser.add_argument("--target", default="PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean")
    parser.add_argument("--candidate", default="")
    parser.add_argument("--downloads", default=str(WORK / "downloads"))
    args = parser.parse_args()
    target = (ROOT / args.target).resolve()

    if args.mode == "prepare":
        # Keep the artifact layout expected by v7's selector.
        result = v7.prepare(target)
        if V7_WORK.exists():
            WORK.mkdir(parents=True, exist_ok=True)
            for name in ("diagnostic.json", "baseline.log"):
                source = V7_WORK / name
                if source.exists():
                    (WORK / name).write_bytes(source.read_bytes())
        return result
    if args.mode == "candidate":
        if not args.candidate:
            raise ValueError("--candidate is required")
        # Candidate jobs download the baseline under .qym_v8; mirror it for v7 APIs.
        V7_WORK.mkdir(parents=True, exist_ok=True)
        for name in ("diagnostic.json", "baseline.log"):
            source = WORK / name
            if source.exists():
                (V7_WORK / name).write_bytes(source.read_bytes())
        return candidate(target, args.candidate)

    # Mirror baseline into the v7 selector's expected location, then select.
    V7_WORK.mkdir(parents=True, exist_ok=True)
    for name in ("diagnostic.json", "baseline.log"):
        source = WORK / name
        if source.exists():
            (V7_WORK / name).write_bytes(source.read_bytes())
    return v7.select(Path(args.downloads).resolve())


if __name__ == "__main__":
    raise SystemExit(main())
