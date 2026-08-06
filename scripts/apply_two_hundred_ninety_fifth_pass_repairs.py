from __future__ import annotations

from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
M2A = ROOT / "PrimalitySheafVerification" / "Mock2_Advanced.lean"
FA = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"


def replace_exact(text: str, old: str, new: str, label: str, expected: int = 1) -> str:
    count = text.count(old)
    if count != expected:
        raise RuntimeError(f"{label}: expected {expected} matches, found {count}")
    print(f"{label}: applied {count}")
    return text.replace(old, new)


def materialize_fintypes(text: str) -> str:
    lines = text.splitlines(keepends=True)
    out: list[str] = []
    i = 0
    replaced = 0
    while i < len(lines):
        line = lines[i]
        m = re.match(r"inductive ([A-Za-z0-9_]+)\s*$", line.rstrip("\n"))
        if not m:
            out.append(line)
            i += 1
            continue
        name = m.group(1)
        j = i + 1
        while j < len(lines) and lines[j] != "  deriving DecidableEq, Fintype, Repr\n":
            if j > i + 400 or (j > i + 1 and lines[j].startswith("inductive ")):
                break
            j += 1
        if j >= len(lines) or lines[j] != "  deriving DecidableEq, Fintype, Repr\n":
            out.append(line)
            i += 1
            continue
        block = lines[i:j]
        constructors: list[tuple[str, str]] = []
        for candidate in block[1:]:
            cm = re.match(r"\s*\|\s+([A-Za-z0-9_]+)(.*)$", candidate.rstrip("\n"))
            if cm:
                constructors.append((cm.group(1), cm.group(2).strip()))
        out.extend(block)
        out.append("  deriving DecidableEq, Repr\n\n")
        if constructors and all(not tail or tail.startswith("--") for _, tail in constructors):
            elems = ", ".join(f".{ctor}" for ctor, _ in constructors)
            out.extend([
                f"instance : Fintype {name} where\n",
                f"  elems := {{{elems}}}\n",
                "  complete := by\n",
                "    intro x\n",
                "    cases x <;> simp\n",
            ])
        elif [ctor for ctor, _ in constructors] == [
            "definition", "lemma", "proposition", "finalClaim"
        ]:
            out.extend([
                "instance : Fintype Claim where\n",
                "  elems :=\n",
                "    (Finset.univ.image Claim.definition) ∪\n",
                "      (Finset.univ.image Claim.«lemma») ∪\n",
                "      (Finset.univ.image Claim.proposition) ∪\n",
                "      (Finset.univ.image Claim.finalClaim)\n",
                "  complete := by\n",
                "    intro x\n",
                "    cases x <;> simp\n",
            ])
        else:
            raise RuntimeError(
                f"unsupported Fintype derivation for {name}: {constructors}"
            )
        replaced += 1
        i = j + 1
    if replaced != 11:
        raise RuntimeError(f"explicit Fintype ledgers: expected 11, found {replaced}")
    print(f"explicit Fintype ledgers: applied {replaced}")
    return "".join(out)


def main() -> int:
    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        """/-- Use the canonical restriction-of-scalars normed-space structure consistently
throughout the real-parameter derivative calculation. -/
local instance scalarUnitaryRealNormedSpace : NormedSpace ℝ ℂ :=
  NormedSpace.complexToReal

""",
        """/- Use Mathlib's canonical restriction-of-scalars normed-space structure
throughout the real-parameter derivative calculation. -/
attribute [local instance 10000] NormedSpace.complexToReal

""",
        "Mock2 Advanced canonical real scalar structure",
    )
    m2a = replace_exact(
        m2a,
        """theorem correction_hasDerivAt (q : ℂ) :
    HasDerivAt correctionValue 1 q := by
  simpa [correctionValue] using
    (hasDerivAt_id q).const_add (2 : ℂ)
""",
        """theorem correction_hasDerivAt (q : ℂ) :
    HasDerivAt correctionValue 1 q := by
  letI : NormedSpace ℂ ℂ := Complex.instNormedField.toNormedModule
  simpa [correctionValue] using
    (hasDerivAt_id q).const_add (2 : ℂ)
""",
        "Mock2 Advanced normed-field self module derivative",
    )
    m2a = materialize_fintypes(m2a)
    m2a = replace_exact(
        m2a,
        """  | .C_coefficientFormulaIdentification =>
      KernelEvidence
        (CorrectedLemmas.HalfOrderBessel.not_summable_criticalModulusEnvelope
          (by norm_num))
""",
        """  | .C_coefficientFormulaIdentification =>
      KernelEvidence
        (CorrectedLemmas.HalfOrderBessel.not_summable_criticalModulusEnvelope
          (A := 1) (by norm_num))
""",
        "Mock2 Advanced instantiate the critical nonzero envelope",
    )
    m2a = replace_exact(
        m2a,
        """theorem requirementEvidence (r : Requirement) : RequirementEvidence r := by
  cases r <;> exact KernelEvidence.certify _
""",
        """theorem requirementEvidence (r : Requirement) : RequirementEvidence r := by
  cases r <;> exact KernelEvidence.intro
""",
        "Mock2 Advanced construct proof-indexed requirement evidence",
        expected=2,
    )
    m2a = replace_exact(
        m2a,
        "theorem definition13_tensorLeibniz_correctedAndProved",
        "noncomputable def definition13_tensorLeibniz_correctedAndProved",
        "Mock2 Advanced infer the tensor Leibniz alias type",
    )
    m2a = replace_exact(
        m2a,
        "(h0 : Tendsto (massFunctional D) atTop (𝒩 0))",
        "(h0 : Tendsto (massFunctional D) atTop (𝓝 0))",
        "Mock2 Advanced current neighborhood notation",
    )
    m2a = replace_exact(
        m2a,
        """theorem claimEvidence (c : Claim) : ClaimEvidence c := by
  cases c <;> simp only [ClaimEvidence]
  all_goals first
    | exact lemma11_distributional_correctedAndProved
    | exact CorrectedLemmas.GlobalPoincare.unqualifiedPoincareSchema_false
    | exact CorrectedLemmas.KloostermanTail.not_summable_nonzero_mul_paper_tail_one
    | exact CorrectedLemmas.KloostermanTail.not_summable_nonzero_mul_paper_tail_half
    | exact ⟨lemma31_localPower_correctedAndProved,
        lemma31_rankinSelbergInferenceErratum⟩
    | exact lemma32_proved
    | exact lemma33_proved
    | exact lemma34_smoothReplacement_correctedAndProved
    | exact CorrectedLemmas.MassUnfolding.not_all_re_gt_one_resolvents_poleFree
    | exact CorrectedLemmas.Interchange.constant_arithmetic_series_not_summable
    | exact CorrectedLemmas.MassUnfolding.not_nonempty_toMassCertificate_of_negative
    | exact CorrectedLemmas.UniformActivity.not_hMass_of_tendsto_mass_zero
    | exact lemma61_covariance_proved
""",
        """theorem claimEvidence (c : Claim) : ClaimEvidence c := by
  cases c with
  | lemma11 => exact lemma11_distributional_correctedAndProved
  | lemma12 => exact CorrectedLemmas.GlobalPoincare.unqualifiedPoincareSchema_false
  | lemma13 =>
      exact CorrectedLemmas.KloostermanTail.not_summable_nonzero_mul_paper_tail_one
  | lemma21 => exact CorrectedLemmas.GlobalPoincare.unqualifiedPoincareSchema_false
  | lemma22 =>
      exact CorrectedLemmas.KloostermanTail.not_summable_nonzero_mul_paper_tail_half
  | lemma31 =>
      exact ⟨lemma31_localPower_correctedAndProved,
        lemma31_rankinSelbergInferenceErratum⟩
  | lemma32 => exact lemma32_proved
  | lemma33 => exact lemma33_proved
  | lemma34 => exact lemma34_smoothReplacement_correctedAndProved
  | lemma35 =>
      exact CorrectedLemmas.MassUnfolding.not_all_re_gt_one_resolvents_poleFree
  | lemma36 => exact CorrectedLemmas.Interchange.constant_arithmetic_series_not_summable
  | lemma37 =>
      exact CorrectedLemmas.MassUnfolding.not_nonempty_toMassCertificate_of_negative
  | lemma38 => exact CorrectedLemmas.UniformActivity.not_hMass_of_tendsto_mass_zero
  | lemma61 => exact lemma61_covariance_proved
""",
        "Mock2 Advanced distribute Section 5.2 evidence by constructor",
    )
    m2a = m2a.replace("| lemma c =>", "| «lemma» c =>")
    m2a = m2a.replace("| .lemma c =>", "| .«lemma» c =>")
    M2A.write_text(m2a, encoding="utf-8")

    fa = FA.read_text(encoding="utf-8")
    fa, count = re.subn(
        r"(?m)^local instance (graphRange|sobolevCompletion)",
        r"noncomputable local instance \1",
        fa,
    )
    if count != 8:
        raise RuntimeError(
            f"FunctionalAnalysis noncomputable coherent instances: expected 8, found {count}"
        )
    print(f"FunctionalAnalysis noncomputable coherent instances: applied {count}")
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
