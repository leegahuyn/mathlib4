from __future__ import annotations

from hashlib import sha256
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
EXPECTED_INPUT_SHA256 = "199fa4c17559a26fd5dfa5524db0a1eab46493fc33786608eef040fb7c05a40b"


def digest(text: str) -> str:
    return sha256(text.encode("utf-8")).hexdigest()


def replace_exact(text: str, old: str, new: str, label: str, expected: int = 1) -> str:
    count = text.count(old)
    print(f"{label}: expected={expected} actual={count}")
    if count != expected:
        raise RuntimeError(f"{label}: expected {expected} occurrence(s), found {count}")
    return text.replace(old, new)


def main() -> int:
    text = TARGET.read_text(encoding="utf-8")
    input_sha = digest(text)
    print(f"input_sha256={input_sha}")
    if input_sha != EXPECTED_INPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass343 input sha256: {input_sha}; expected {EXPECTED_INPUT_SHA256}"
        )

    text = replace_exact(
        text,
        "  exact hh.1.deriv",
        "  exact hh.deriv",
        "ContDiff derivative smoothness",
        expected=7,
    )

    old_dx = '''theorem fixedPhaseEuclideanGauge_contDiff_dx (n : ℤ) (u : InverseEtaFixedPhaseCore n)
    (z : ℝ × ℝ) (hz : z ∈ UpperHalfPlane.upperHalfPlaneSet) :
    ContDiffWithinAt ℝ ∞ (UpperHalfPlane.upperLift
      (fun w => dx (fixedPhaseEuclideanGauge n u) w))
      UpperHalfPlane.upperHalfPlaneSet z := by
  have hh := fixedPhaseEuclideanGauge_contDiff (n := n) (u := u) (z := z) hz
  exact hh.dy'''
    new_dx = '''theorem fixedPhaseEuclideanGauge_contDiff_dx (n : ℤ) (u : InverseEtaFixedPhaseCore n)
    (z : ℝ × ℝ) (hz : z ∈ UpperHalfPlane.upperHalfPlaneSet) :
    ContDiffWithinAt ℝ ∞ (UpperHalfPlane.upperLift
      (fun w => dx (fixedPhaseEuclideanGauge n u) w))
      UpperHalfPlane.upperHalfPlaneSet z := by
  simpa only [UpperHalfPlane.upperOfRealProd] using
    (contDiff_fixedPhaseEuclideanGauge_dx n u).contDiffWithinAt
      (x := (z.1, z.2)) (s := UpperHalfPlane.upperHalfPlaneSet)'''
    text = replace_exact(text, old_dx, new_dx, "fixed-phase dx smoothness")

    old_dy = '''theorem fixedPhaseEuclideanGauge_contDiff_dy (n : ℤ) (u : InverseEtaFixedPhaseCore n)
    (z : ℝ × ℝ) (hz : z ∈ UpperHalfPlane.upperHalfPlaneSet) :
    ContDiffWithinAt ℝ ∞ (UpperHalfPlane.upperLift
      (fun w => dy (fixedPhaseEuclideanGauge n u) w))
      UpperHalfPlane.upperHalfPlaneSet z := by
  have hh := fixedPhaseEuclideanGauge_contDiff (n := n) (u := u) (z := z) hz
  exact hh.dy'''
    new_dy = '''theorem fixedPhaseEuclideanGauge_contDiff_dy (n : ℤ) (u : InverseEtaFixedPhaseCore n)
    (z : ℝ × ℝ) (hz : z ∈ UpperHalfPlane.upperHalfPlaneSet) :
    ContDiffWithinAt ℝ ∞ (UpperHalfPlane.upperLift
      (fun w => dy (fixedPhaseEuclideanGauge n u) w))
      UpperHalfPlane.upperHalfPlaneSet z := by
  simpa only [UpperHalfPlane.upperOfRealProd] using
    (contDiff_fixedPhaseEuclideanGauge_dy n u).contDiffWithinAt
      (x := (z.1, z.2)) (s := UpperHalfPlane.upperHalfPlaneSet)'''
    text = replace_exact(text, old_dy, new_dy, "fixed-phase dy smoothness")

    output_sha = digest(text)
    TARGET.write_text(text, encoding="utf-8")
    print(f"output_sha256={output_sha}")
    print("[pass343] ContDiff derivative and fixed-phase dx/dy smoothness repairs applied")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
