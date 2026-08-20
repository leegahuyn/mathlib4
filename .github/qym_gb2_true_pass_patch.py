#!/usr/bin/env python3
from __future__ import annotations

import hashlib
from pathlib import Path

QYM = Path("PrimalitySheafVerification/QYM.lean")
BASE_SHA256 = "c798cc256e41e19073cc57aef0723e213ef234e353dde65daf47790a91efcd7f"

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
  constructor
  · intro hzero
    by_contra hne
    exact (ne_of_gt ((re_inner_self_pos (𝕜 := ℂ)).2 hne)) hzero
  · intro hzero
    subst u
    simp
"""

HAM_OLD = """@[simp]
theorem coordinateHamiltonianForm_re_self (u : CoordinateL2) :
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

HAM_NEW = """@[simp]
theorem coordinateHamiltonianForm_re_self (u : CoordinateL2) :
    RCLike.re (coordinateHamiltonianForm u u) =
      ‖covariantDerivative u‖ ^ 2 + (1 / 4 : ℝ) * ‖groundProjection u‖ ^ 2 := by
  rw [coordinateHamiltonianForm_apply, map_add]
  have hreal :
      RCLike.re ((((1 : ℝ) / 4 : ℝ) : ℂ) *
        inner ℂ (groundProjection u) (groundProjection u)) =
        (1 / 4 : ℝ) *
          RCLike.re (inner ℂ (groundProjection u) (groundProjection u)) := by
    change
      ((((1 : ℝ) / 4 : ℝ) : ℂ) *
        inner ℂ (groundProjection u) (groundProjection u)).re =
        (1 / 4 : ℝ) *
          (inner ℂ (groundProjection u) (groundProjection u)).re
    simp [Complex.mul_re]
  rw [hreal,
    (norm_sq_eq_re_inner (𝕜 := ℂ) (covariantDerivative u)).symm,
    (norm_sq_eq_re_inner (𝕜 := ℂ) (groundProjection u)).symm]
"""


def replace_exact(text: str, old: str, new: str, label: str) -> str:
    count = text.count(old)
    if count != 1:
        raise SystemExit(f"{label}: expected exactly one source block, found {count}")
    return text.replace(old, new, 1)


raw = QYM.read_bytes()
actual = hashlib.sha256(raw).hexdigest()
if actual != BASE_SHA256:
    raise SystemExit(f"authority mismatch: expected {BASE_SHA256}, got {actual}")

text = raw.decode("utf-8")
text = replace_exact(text, PETERS_OLD, PETERS_NEW, "Petersson blocker")
text = replace_exact(text, HAM_OLD, HAM_NEW, "Hamiltonian blocker")
QYM.write_text(text, encoding="utf-8")
print(hashlib.sha256(QYM.read_bytes()).hexdigest())
