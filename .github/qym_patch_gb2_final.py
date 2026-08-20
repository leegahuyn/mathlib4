#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import sys
from pathlib import Path

BASE_SHA256 = "1e545a316c33741875b5c0ca252105f5a0d858f327b44b0e79e8e5193a7986d4"


def replace_once(text: str, old: str, new: str, label: str) -> str:
    count = text.count(old)
    if count != 1:
        raise SystemExit(f"{label}: expected exactly one match, found {count}")
    return text.replace(old, new, 1)


def main() -> None:
    if len(sys.argv) != 3:
        raise SystemExit("usage: qym_patch_gb2_final.py INPUT OUTPUT")

    source = Path(sys.argv[1])
    output = Path(sys.argv[2])
    raw = source.read_bytes()
    actual = hashlib.sha256(raw).hexdigest()
    if actual != BASE_SHA256:
        raise SystemExit(f"wrong QYM two-error base bytes: {actual}")

    text = raw.decode()

    text = replace_once(
        text,
        """theorem actualStagePeterssonInner_self_re_eq_zero_iff
    {Y : ℝ} (u : ActualStageInverseEtaL2Section Y) :
    (actualStagePeterssonInner u u).re = 0 ↔ u = 0 := by
  unfold actualStagePeterssonInner
  rw [inner_self_eq_norm_sq_to_K]
  simp
""",
        """theorem actualStagePeterssonInner_self_re_eq_zero_iff
    {Y : ℝ} (u : ActualStageInverseEtaL2Section Y) :
    (actualStagePeterssonInner u u).re = 0 ↔ u = 0 := by
  unfold actualStagePeterssonInner
  rw [inner_self_eq_norm_sq_to_K]
  simp [pow_two, Complex.mul_re]
""",
        "Petersson real-part definiteness by expanded complex square",
    )

    text = replace_once(
        text,
        """theorem coordinateHamiltonianForm_re_self (u : CoordinateL2) :
    RCLike.re (coordinateHamiltonianForm u u) =
      ‖covariantDerivative u‖ ^ 2 + (1 / 4 : ℝ) * ‖groundProjection u‖ ^ 2 := by
  rw [coordinateHamiltonianForm_apply,
    inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
  simp
""",
        """theorem coordinateHamiltonianForm_re_self (u : CoordinateL2) :
    RCLike.re (coordinateHamiltonianForm u u) =
      ‖covariantDerivative u‖ ^ 2 + (1 / 4 : ℝ) * ‖groundProjection u‖ ^ 2 := by
  rw [coordinateHamiltonianForm_apply,
    inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
  simp [pow_two, Complex.mul_re]
""",
        "Hamiltonian real-part identity by expanded complex squares",
    )

    output.write_text(text)
    digest = hashlib.sha256(output.read_bytes()).hexdigest()
    blob = hashlib.sha1(
        f"blob {output.stat().st_size}\0".encode() + output.read_bytes()
    ).hexdigest()
    print(f"candidate_sha256={digest}")
    print(f"candidate_blob={blob}")


if __name__ == "__main__":
    main()
