from __future__ import annotations

from pathlib import Path
import hashlib

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
EXPECTED_INPUT_SHA256 = "a61e8c20bdc28395d6b71857ec714780e36e8d98233480226e0442098ae3a438"
EXPECTED_OUTPUT_SHA256 = "171588d37133a6494727645474dadad3f80828bdcf8a1ce5b8fd72b77d4d3c0a"


def sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def replace_exact(text: str, old: str, new: str, label: str, expected: int = 1) -> str:
    actual = text.count(old)
    print(f"{label}: expected={expected} actual={actual}")
    if actual != expected:
        raise RuntimeError(f"{label}: expected {expected} matches, found {actual}")
    return text.replace(old, new)


def main() -> int:
    text = TARGET.read_text(encoding="utf-8")
    input_sha = sha256_text(text)
    print(f"input_sha256={input_sha}")
    if input_sha == EXPECTED_OUTPUT_SHA256:
        print("[pass319] already applied")
        return 0
    if input_sha != EXPECTED_INPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass319 input sha256: {input_sha}; expected {EXPECTED_INPUT_SHA256}"
        )

    text = replace_exact(
        text,
        '''/-- `InverseEtaFixedPhaseCore` is an opaque noncomputable abbreviation of a
submodule. Re-export exactly the canonical subtype algebra structures at this
boundary so the coordinate package does not invent a second module structure. -/
noncomputable local instance fixedPhaseCoreAddCommGroup (n : ℤ) :
    AddCommGroup (InverseEtaFixedPhaseCore n) :=
  inferInstanceAs
    (AddCommGroup (inverseEtaFixedPhaseStableCoreSubmodule n))

noncomputable local instance fixedPhaseCoreModule (n : ℤ) :
    Module ℂ (InverseEtaFixedPhaseCore n) :=
  inferInstanceAs
    (Module ℂ (inverseEtaFixedPhaseStableCoreSubmodule n))

''',
        '',
        "FunctionalAnalysis remove redundant fixed-phase subtype instances",
    )
    text = replace_exact(
        text,
        '''#synth NormedAddCommGroup (GraphSobolevCompletion 0)
#synth NormedSpace ℂ (GraphSobolevCompletion 0)
#synth InnerProductSpace ℂ (GraphSobolevCompletion 0)
#synth CompleteSpace (GraphSobolevCompletion 0)
#synth Norm (GraphSobolevCompletion 0 →L[ℂ] OrbitPeterssonHilbert 0)

''',
        '',
        "FunctionalAnalysis remove graph-completion debug synth commands",
    )
    text = replace_exact(
        text,
        "open DefinitionOneSobolev.GammaTwoQuotientGeometry\n",
        "open GammaTwoQuotientGeometry\n",
        "FunctionalAnalysis repair GammaTwo geometry namespace opens",
        expected=16,
    )
    text = replace_exact(
        text,
        '''open DefinitionOneSobolev.FixedPhaseGraphCompletion
open PhysicalLocalL2
''',
        '''open DefinitionOneSobolev.FixedPhaseGraphCompletion
open FixedPhaseClosedOperators.PhysicalLocalL2
''',
        "FunctionalAnalysis repair selected-trace PhysicalLocalL2 namespace",
    )
    text = replace_exact(
        text,
        '''variable [InnerProductSpace ℂ H]

/-- The explicit rank-one cusp-tail package. -/
''',
        '''end ExactTail

section RankOneExactTail

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The explicit rank-one cusp-tail package. -/
''',
        "FunctionalAnalysis split rank-one exact-tail instance context",
    )
    text = replace_exact(
        text,
        '''end ExactTail

section FredholmConstructors
''',
        '''end RankOneExactTail

section FredholmConstructors
''',
        "FunctionalAnalysis close rank-one exact-tail section",
    )
    text = replace_exact(
        text,
        "(euclideanRaiseGauge_realSmooth n hf).conj",
        "RealSmooth.conj (euclideanRaiseGauge_realSmooth n hf)",
        "FunctionalAnalysis explicit conjugate smoothness for raising",
    )
    text = replace_exact(
        text,
        "(euclideanLowerFromSuccGauge_realSmooth n hf).conj",
        "RealSmooth.conj (euclideanLowerFromSuccGauge_realSmooth n hf)",
        "FunctionalAnalysis explicit conjugate smoothness for lowering",
    )
    text = replace_exact(
        text,
        "hf.conj.dx",
        "(RealSmooth.conj hf).dx",
        "FunctionalAnalysis explicit conjugate dx smoothness",
        expected=2,
    )
    text = replace_exact(
        text,
        "hf.conj.dy",
        "(RealSmooth.conj hf).dy",
        "FunctionalAnalysis explicit conjugate dy smoothness",
        expected=2,
    )
    text = replace_exact(
        text,
        "hf.conj",
        "RealSmooth.conj hf",
        "FunctionalAnalysis explicit conjugate smoothness",
        expected=12,
    )
    text = replace_exact(
        text,
        '''    (constantCompactCuspTail C hC).truncation n - C = 0 := by
  simp
''',
        '''    (constantCompactCuspTail C hC).truncation n - C = 0 := by
  rw [constantCompactCuspTail_truncation, sub_self]
''',
        "FunctionalAnalysis explicit constant-tail subtraction",
    )
    text = replace_exact(
        text,
        '''    ‖(constantCompactCuspTail C hC).truncation n - C‖ = 0 := by
  simp
''',
        '''    ‖(constantCompactCuspTail C hC).truncation n - C‖ = 0 := by
  rw [constantCompactCuspTail_truncation, sub_self, norm_zero]
''',
        "FunctionalAnalysis explicit constant-tail norm",
    )

    output_sha = sha256_text(text)
    print(f"output_sha256={output_sha}")
    if output_sha != EXPECTED_OUTPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass319 output sha256: {output_sha}; expected {EXPECTED_OUTPUT_SHA256}"
        )
    TARGET.write_text(text, encoding="utf-8")
    print("[pass319] FunctionalAnalysis instance and namespace cascade repaired")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
