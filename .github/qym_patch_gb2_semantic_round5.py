#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import subprocess
import sys
from pathlib import Path

BASE_SHA256 = "231efe9a0b8f9d05aae5e65ff3904b3636182ef6f1c93c11eac0c05313730998"
GB2_SHA256 = "c798cc256e41e19073cc57aef0723e213ef234e353dde65daf47790a91efcd7f"
R5_SHA256 = "7b0037843b41d19134df52e70c9c6d64fed5563d9a5a1e598cb9fc22c1d98f4b"
R5_BLOB = "3af2b62afce1b62a0613130e484c3da77d29bab9"

PETERS_OLD = """theorem actualStagePeterssonInner_self_re_eq_zero_iff
    {Y : ℝ} (u : ActualStageInverseEtaL2Section Y) :
    (actualStagePeterssonInner u u).re = 0 ↔ u = 0 := by
  unfold actualStagePeterssonInner
  rw [← norm_sq_eq_re_inner, sq_eq_zero_iff, norm_eq_zero]
"""
PETERS_NEW = """theorem actualStagePeterssonInner_self_re_eq_zero_iff
    {Y : ℝ} (u : ActualStageInverseEtaL2Section Y) :
    (actualStagePeterssonInner u u).re = 0 ↔ u = 0 := by
  unfold actualStagePeterssonInner
  rw [inner_self_eq_norm_sq_to_K]
  simp
"""

HAMILTONIAN_OLD = """theorem coordinateHamiltonianForm_re_self (u : CoordinateL2) :
    RCLike.re (coordinateHamiltonianForm u u) =
      ‖covariantDerivative u‖ ^ 2 + (1 / 4 : ℝ) * ‖groundProjection u‖ ^ 2 := by
  rw [coordinateHamiltonianForm_apply, map_add, Complex.mul_re]
  change
    (inner ℂ (covariantDerivative u) (covariantDerivative u)).re +
      ((1 / 4 : ℝ) *
        (inner ℂ (groundProjection u) (groundProjection u)).re - 0) =
      ‖covariantDerivative u‖ ^ 2 +
        (1 / 4 : ℝ) * ‖groundProjection u‖ ^ 2
  rw [← norm_sq_eq_re_inner, ← norm_sq_eq_re_inner]
  ring
"""
HAMILTONIAN_NEW = """theorem coordinateHamiltonianForm_re_self (u : CoordinateL2) :
    RCLike.re (coordinateHamiltonianForm u u) =
      ‖covariantDerivative u‖ ^ 2 + (1 / 4 : ℝ) * ‖groundProjection u‖ ^ 2 := by
  rw [coordinateHamiltonianForm_apply,
    inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
  simp
"""


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def replace_once(text: str, old: str, new: str, label: str) -> str:
    count = text.count(old)
    if count != 1:
        raise SystemExit(f"{label}: expected exactly one match, found {count}")
    return text.replace(old, new, 1)


def main() -> None:
    if len(sys.argv) != 5:
        raise SystemExit(
            "usage: qym_patch_gb2_semantic_round5.py R4_GENERATOR BASE INTERMEDIATE OUTPUT"
        )
    generator = Path(sys.argv[1])
    base = Path(sys.argv[2])
    intermediate = Path(sys.argv[3])
    output = Path(sys.argv[4])
    if sha256(base) != BASE_SHA256:
        raise SystemExit(f"wrong five-error authority bytes: {sha256(base)}")

    subprocess.run(
        [sys.executable, "-B", str(generator), "convert-change", str(base), str(intermediate)],
        check=True,
    )
    if sha256(intermediate) != GB2_SHA256:
        raise SystemExit(
            f"failed to reproduce verified two-error frontier: {sha256(intermediate)}"
        )

    text = intermediate.read_text()
    text = replace_once(text, PETERS_OLD, PETERS_NEW, "Petersson definiteness")
    text = replace_once(
        text,
        HAMILTONIAN_OLD,
        HAMILTONIAN_NEW,
        "Hamiltonian real self-evaluation",
    )
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(text)
    actual_sha = sha256(output)
    actual_blob = subprocess.check_output(
        ["git", "hash-object", str(output)], text=True
    ).strip()
    if actual_sha != R5_SHA256 or actual_blob != R5_BLOB:
        raise SystemExit(
            f"R5 deterministic output drift: sha256={actual_sha} blob={actual_blob}"
        )
    print(f"intermediate_sha256={GB2_SHA256}")
    print(f"candidate_sha256={actual_sha}")
    print(f"candidate_blob={actual_blob}")


if __name__ == "__main__":
    main()
