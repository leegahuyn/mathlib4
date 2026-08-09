from __future__ import annotations

from hashlib import sha256
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
EXPECTED_INPUT_SHA256 = "5f7052b75353817e55e4fab35cc5f6578a9449737476a3dd05621999eaa67eed"


def digest(text: str) -> str:
    return sha256(text.encode("utf-8")).hexdigest()


def replace_count(
    text: str, old: str, new: str, label: str, expected: int
) -> str:
    actual = text.count(old)
    print(f"{label}: expected={expected} actual={actual}")
    if actual != expected:
        raise RuntimeError(
            f"{label}: expected {expected} occurrences, found {actual}"
        )
    return text.replace(old, new)


def main() -> int:
    text = TARGET.read_text(encoding="utf-8")
    input_sha = digest(text)
    print(f"input_sha256={input_sha}")
    if input_sha != EXPECTED_INPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass323 input sha256: {input_sha}; "
            f"expected {EXPECTED_INPUT_SHA256}"
        )

    replacements = [
        (
            """  have h : RealSmooth
      ((Complex.I • (heightC * dx f)) +
        (heightC * dy f) +
        (((euclideanGaugeExponent n + 2 : ℝ) : ℂ) • f)) :=
    (((realSmooth_heightC.mul RealSmooth.dx hf).const_complex_smul Complex.I).add
      (realSmooth_heightC.mul RealSmooth.dy hf)).add
        (hf.const_complex_smul
          ((euclideanGaugeExponent n + 2 : ℝ) : ℂ))
""",
            """  have h : RealSmooth
      ((Complex.I • (heightC * dx f)) +
        (heightC * dy f) +
        (((euclideanGaugeExponent n + 2 : ℝ) : ℂ) • f)) :=
    RealSmooth.add
      (RealSmooth.add
        (RealSmooth.const_complex_smul Complex.I
          (RealSmooth.mul realSmooth_heightC (RealSmooth.dx hf)))
        (RealSmooth.mul realSmooth_heightC (RealSmooth.dy hf)))
      (RealSmooth.const_complex_smul
        ((euclideanGaugeExponent n + 2 : ℝ) : ℂ) hf)
""",
            "FunctionalAnalysis explicit raising smoothness",
            1,
        ),
        (
            """  have h : RealSmooth
      (((-Complex.I) • (heightC * dx f)) +
        (heightC * dy f) -
        (((euclideanGaugeExponent n + 1 : ℝ) : ℂ) • f)) :=
    (((realSmooth_heightC.mul RealSmooth.dx hf).const_complex_smul
      (-Complex.I)).add (realSmooth_heightC.mul RealSmooth.dy hf)).sub
        (hf.const_complex_smul
          ((euclideanGaugeExponent n + 1 : ℝ) : ℂ))
""",
            """  have h : RealSmooth
      (((-Complex.I) • (heightC * dx f)) +
        (heightC * dy f) -
        (((euclideanGaugeExponent n + 1 : ℝ) : ℂ) • f)) :=
    RealSmooth.sub
      (RealSmooth.add
        (RealSmooth.const_complex_smul (-Complex.I)
          (RealSmooth.mul realSmooth_heightC (RealSmooth.dx hf)))
        (RealSmooth.mul realSmooth_heightC (RealSmooth.dy hf)))
      (RealSmooth.const_complex_smul
        ((euclideanGaugeExponent n + 1 : ℝ) : ℂ) hf)
""",
            "FunctionalAnalysis explicit lowering smoothness",
            1,
        ),
        (
            "        RealSmooth.conj (euclideanRaiseGauge_realSmooth n hf) v",
            "        (RealSmooth.conj (euclideanRaiseGauge_realSmooth n hf)) v",
            "FunctionalAnalysis group raising conjugate proof",
            1,
        ),
        (
            "        RealSmooth.conj (euclideanLowerFromSuccGauge_realSmooth n hf) v",
            "        (RealSmooth.conj (euclideanLowerFromSuccGauge_realSmooth n hf)) v",
            "FunctionalAnalysis group lowering conjugate proof",
            1,
        ),
        (
            "(fun z => star (f z)) RealSmooth.conj hf v",
            "(fun z => star (f z)) (RealSmooth.conj hf) v",
            "FunctionalAnalysis group base conjugate proof",
            12,
        ),
        (
            "(RealSmooth.conj hf).dx",
            "RealSmooth.dx (RealSmooth.conj hf)",
            "FunctionalAnalysis qualify conjugate dx",
            2,
        ),
        (
            "(RealSmooth.conj hf).dy",
            "RealSmooth.dy (RealSmooth.conj hf)",
            "FunctionalAnalysis qualify conjugate dy",
            2,
        ),
        (
            "(selectedCosetDerivative_realSmooth q).complexRealPart",
            "RealSmooth.complexRealPart (selectedCosetDerivative_realSmooth q)",
            "FunctionalAnalysis qualify real-part smoothness",
            1,
        ),
        (
            "(selectedCosetDerivative_realSmooth q).complexImagPart",
            "RealSmooth.complexImagPart (selectedCosetDerivative_realSmooth q)",
            "FunctionalAnalysis qualify imaginary-part smoothness",
            1,
        ),
        (
            "hX.comp_selectedCosetAction q",
            "RealSmooth.comp_selectedCosetAction hX q",
            "FunctionalAnalysis qualify X composition",
            3,
        ),
        (
            "hY.comp_selectedCosetAction q",
            "RealSmooth.comp_selectedCosetAction hY q",
            "FunctionalAnalysis qualify Y composition",
            3,
        ),
        (
            "realSmooth_heightC.comp_selectedCosetAction q",
            "RealSmooth.comp_selectedCosetAction realSmooth_heightC q",
            "FunctionalAnalysis qualify height composition",
            3,
        ),
        (
            "hf.comp_selectedCosetAction q",
            "RealSmooth.comp_selectedCosetAction hf q",
            "FunctionalAnalysis qualify generic selected-coset composition",
            3,
        ),
        (
            "hPull.comp_logHeightBasePoint t",
            "RealSmooth.comp_logHeightBasePoint hPull t",
            "FunctionalAnalysis qualify pullback log-height composition",
            1,
        ),
        (
            "hh.comp_logHeightBasePoint t",
            "RealSmooth.comp_logHeightBasePoint hh t",
            "FunctionalAnalysis qualify local log-height composition",
            1,
        ),
        (
            "hh.dy.continuous.comp hpoint",
            "(RealSmooth.dy hh).continuous.comp hpoint",
            "FunctionalAnalysis qualify smooth vertical derivative",
            1,
        ),
        (
            "hTail.exists_commonBaseHeight_zero",
            "HasZeroThreeCuspTail.exists_commonBaseHeight_zero hTail",
            "FunctionalAnalysis qualify common cusp-height witness",
            4,
        ),
        (
            """  exact
    (upstairsCoreCutoff_realSmooth.dx.const_complex_smul Complex.I).add
      upstairsCoreCutoff_realSmooth.dy
""",
            """  exact RealSmooth.add
    (RealSmooth.const_complex_smul Complex.I
      (RealSmooth.dx upstairsCoreCutoff_realSmooth))
    (RealSmooth.dy upstairsCoreCutoff_realSmooth)
""",
            "FunctionalAnalysis explicit holomorphic cutoff smoothness",
            1,
        ),
        (
            """  exact
    (upstairsCoreCutoff_realSmooth.dx.const_complex_smul (-Complex.I)).add
      upstairsCoreCutoff_realSmooth.dy
""",
            """  exact RealSmooth.add
    (RealSmooth.const_complex_smul (-Complex.I)
      (RealSmooth.dx upstairsCoreCutoff_realSmooth))
    (RealSmooth.dy upstairsCoreCutoff_realSmooth)
""",
            "FunctionalAnalysis explicit antiholomorphic cutoff smoothness",
            1,
        ),
    ]

    for old, new, label, expected in replacements:
        text = replace_count(text, old, new, label, expected)

    paired_pattern = re.compile(
        r"\(\(q, GammaTwoModularTileEdge\."
        r"(circularArc|leftVerticalSegment|rightVerticalSegment)"
        r"\) :\s*\n\s*GammaTwoActualPolygonEdge\)\.paired"
    )
    text, paired_count = paired_pattern.subn(
        lambda match: (
            "GammaTwoActualPolygonEdge.paired "
            f"((q, GammaTwoModularTileEdge.{match.group(1)}) : "
            "GammaTwoActualPolygonEdge)"
        ),
        text,
    )
    print(f"FunctionalAnalysis qualify actual-edge pairing: expected=9 actual={paired_count}")
    if paired_count != 9:
        raise RuntimeError(
            f"expected 9 actual-edge pairing occurrences, found {paired_count}"
        )

    output_sha = digest(text)
    print(f"output_sha256={output_sha}")
    TARGET.write_text(text, encoding="utf-8")
    print("[pass323] FunctionalAnalysis explicit namespace/API frontier repaired")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
