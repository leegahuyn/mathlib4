from __future__ import annotations

from hashlib import sha256
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
EXPECTED_INPUT_SHA256 = "ba8e9ae92a27b5ea965990b207458b477d1527fa081e854cd43b299eac82150e"
EXPECTED_OUTPUT_SHA256 = "fd80630d62f9fb72c101c83ced4b19f47256e0601595642ed93cd7b4d058b464"


def digest(text: str) -> str:
    return sha256(text.encode("utf-8")).hexdigest()


def replace_once(text: str, old: str, new: str, label: str) -> str:
    count = text.count(old)
    print(f"{label}: expected=1 actual={count}")
    if count != 1:
        raise RuntimeError(f"{label}: expected one occurrence, found {count}")
    return text.replace(old, new)


def main() -> int:
    text = TARGET.read_text(encoding="utf-8")
    input_sha = digest(text)
    print(f"input_sha256={input_sha}")
    if input_sha == EXPECTED_OUTPUT_SHA256:
        print("[pass346] already applied")
        return 0
    if input_sha != EXPECTED_INPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass346 input sha256: {input_sha}; expected {EXPECTED_INPUT_SHA256}"
        )

    text = replace_once(
        text,
        """  have hProd := congrFun
    (dx_mul (realSmooth_complexHeightRpow _)
      u.1.1.2) z
""",
        """  have hProd :=
    dx_mul (realSmooth_complexHeightRpow _)
      u.1.1.2 z
""",
        "FunctionalAnalysis apply the horizontal product rule at the point",
    )
    text = replace_once(
        text,
        """  have hProd := congrFun
    (dy_mul (realSmooth_complexHeightRpow _)
      u.1.1.2) z
""",
        """  have hProd :=
    dy_mul (realSmooth_complexHeightRpow _)
      u.1.1.2 z
""",
        "FunctionalAnalysis apply the vertical product rule at the point",
    )
    text = replace_once(
        text,
        """  have hz : heightC z ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr z.im_ne_zero
  field_simp [hz]
  ring

/-- Exact pointwise conjugation of lowering from the successor orbit by the
""",
        """  have hz : heightC z ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr z.im_ne_zero
  field_simp [hz]
  ring_nf

/-- Exact pointwise conjugation of lowering from the successor orbit by the
""",
        "FunctionalAnalysis normalize the Euclidean raising identity",
    )
    text = replace_once(
        text,
        """  have hz : heightC z ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr z.im_ne_zero
  field_simp [hz]
  ring

/-! #### Compact Hermitian test transposes -/
""",
        """  have hz : heightC z ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr z.im_ne_zero
  rw [show (1 + n : ℤ) = n + 1 by omega,
    euclideanGaugeExponent_succ]
  field_simp [hz]
  ring_nf

/-! #### Compact Hermitian test transposes -/
""",
        "FunctionalAnalysis align and normalize the Euclidean lowering identity",
    )
    text = replace_once(
        text,
        """    HalfWeightCompactCoordinateGreen.localizeLeft
        (fun z => Complex.conj (euclideanRaiseGauge n f z))
        (RealSmooth.conj (euclideanRaiseGauge_realSmooth n hf)) v =
      (-Complex.I) •
          HalfWeightCompactCoordinateGreen.localizeLeft
            (dx (fun z => Complex.conj (f z)))
            (RealSmooth.dx (RealSmooth.conj hf))
            (HalfWeightCompactCoordinateGreen.rpowMul 1 v) +
        HalfWeightCompactCoordinateGreen.localizeLeft
          (dy (fun z => Complex.conj (f z)))
          (RealSmooth.dy (RealSmooth.conj hf))
          (HalfWeightCompactCoordinateGreen.rpowMul 1 v) +
        ((euclideanGaugeExponent n + 2 : ℝ) : ℂ) •
          HalfWeightCompactCoordinateGreen.localizeLeft
            (fun z => Complex.conj (f z)) (RealSmooth.conj hf) v := by
""",
        """    HalfWeightCompactCoordinateGreen.localizeLeft
        (fun z => star (euclideanRaiseGauge n f z))
        (RealSmooth.conj (euclideanRaiseGauge_realSmooth n hf)) v =
      (-Complex.I) •
          HalfWeightCompactCoordinateGreen.localizeLeft
            (dx (fun z => star (f z)))
            (RealSmooth.dx (RealSmooth.conj hf))
            (HalfWeightCompactCoordinateGreen.rpowMul 1 v) +
        HalfWeightCompactCoordinateGreen.localizeLeft
          (dy (fun z => star (f z)))
          (RealSmooth.dy (RealSmooth.conj hf))
          (HalfWeightCompactCoordinateGreen.rpowMul 1 v) +
        ((euclideanGaugeExponent n + 2 : ℝ) : ℂ) •
          HalfWeightCompactCoordinateGreen.localizeLeft
            (fun z => star (f z)) (RealSmooth.conj hf) v := by
""",
        "FunctionalAnalysis migrate the compact raising transpose to star",
    )

    output_sha = digest(text)
    print(f"output_sha256={output_sha}")
    if output_sha != EXPECTED_OUTPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass346 output sha256: {output_sha}; expected {EXPECTED_OUTPUT_SHA256}"
        )
    TARGET.write_text(text, encoding="utf-8")
    print("[pass346] FunctionalAnalysis product rules, gauge identities, and star API repaired")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
