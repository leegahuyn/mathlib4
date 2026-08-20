from __future__ import annotations

from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
M2A = ROOT / "PrimalitySheafVerification" / "Mock2_Advanced.lean"


def replace_exact(text: str, old: str, new: str, label: str, expected: int = 1) -> str:
    count = text.count(old)
    if count != expected:
        raise RuntimeError(f"{label}: expected {expected} matches, found {count}")
    print(f"{label}: applied {count}")
    return text.replace(old, new)


def insert_claim_evidence_simp(text: str, namespace: str) -> str:
    ns_start = text.index(f"namespace {namespace}\n")
    ns_end = text.index(f"\nend {namespace}\n", ns_start)
    theorem_start = text.index(
        "theorem claimEvidence (c : Claim) : ClaimEvidence c := by\n",
        ns_start,
        ns_end,
    )
    block = text[theorem_start:ns_end]
    branch_count = 0
    out: list[str] = []
    for line in block.splitlines(keepends=True):
        m_inline = re.match(r"^(  \| [^\n]+ =>) (.+)\n$", line)
        if m_inline:
            out.append(m_inline.group(1) + "\n")
            out.append("      simp only [ClaimEvidence]\n")
            out.append("      " + m_inline.group(2) + "\n")
            branch_count += 1
            continue
        m_block = re.match(r"^(  \| [^\n]+ =>)\n$", line)
        if m_block:
            out.append(line)
            out.append("      simp only [ClaimEvidence]\n")
            branch_count += 1
            continue
        out.append(line)
    expected = {"Section51Closure": 18, "Section52Closure": 14, "Section53Closure": 21}[namespace]
    if branch_count != expected:
        raise RuntimeError(
            f"{namespace} evidence branches: expected {expected}, found {branch_count}"
        )
    print(f"{namespace} evidence branches: applied {branch_count}")
    return text[:theorem_start] + "".join(out) + text[ns_end:]


def main() -> int:
    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        """theorem hasDerivAt_scalarUnitaryScattering (t : ℝ) :
    HasDerivAt scalarUnitaryScattering (scalarUnitaryDerivative t) t := by
  have hinner :
      HasDerivAt (fun z : ℂ => Complex.I * z) Complex.I (t : ℂ) :=
    hasDerivAt_const_mul Complex.I
  have hcomplex := hinner.cexp
  simpa [scalarUnitaryScattering, scalarUnitaryDerivative, mul_comm] using
    hcomplex.comp_ofReal
""",
        """theorem hasDerivAt_scalarUnitaryScattering (t : ℝ) :
    HasDerivAt scalarUnitaryScattering (scalarUnitaryDerivative t) t := by
  have hinner :
      HasDerivAt (fun z : ℂ => Complex.I * z) Complex.I (t : ℂ) :=
    hasDerivAt_const_mul Complex.I
  have hcomplex := hinner.cexp
  change HasDerivAt
    (fun y : ℝ => Complex.exp (Complex.I * (y : ℂ)))
    (Complex.I * Complex.exp (Complex.I * (t : ℂ))) t
  exact hcomplex.comp_ofReal
""",
        "Mock2 Advanced unitary scattering derivative target",
    )
    m2a = replace_exact(
        m2a,
        """theorem correction_hasDerivAt (q : ℂ) :
    HasDerivAt correctionValue 1 q := by
  letI : NormedSpace ℂ ℂ := Complex.instNormedField.toNormedModule
  simpa [correctionValue] using
    (hasDerivAt_id q).const_add (2 : ℂ)
""",
        """theorem correction_hasDerivAt (q : ℂ) :
    HasDerivAt correctionValue 1 q := by
  change HasDerivAt (fun z : ℂ => (2 : ℂ) + z) 1 q
  simpa using (hasDerivAt_id q).const_add (2 : ℂ)
""",
        "Mock2 Advanced affine correction derivative target",
    )
    m2a = replace_exact(
        m2a,
        "instance : Fintype Requirement where",
        "set_option maxHeartbeats 1000000 maxRecDepth 10000 in\ninstance : Fintype Requirement where",
        "Mock2 Advanced large requirement enumerations",
        expected=2,
    )
    m2a = replace_exact(
        m2a,
        "(@UnnumberedFormulaLedger.equations1_1_to_1_16_graphCoreDenseAndProved)",
        "(@UnnumberedFormulaLedger.equations1_1_to_1_16_graphCoreDenseAndProved.{0, 0, 0, 0})",
        "Mock2 Advanced specialize graph-density audit universes",
    )
    m2a = replace_exact(
        m2a,
        "(@p01_genuineAECompletion_correctedAndProved)",
        "(@p01_genuineAECompletion_correctedAndProved.{0})",
        "Mock2 Advanced specialize AE-completion audit universe",
    )
    for namespace in ("Section51Closure", "Section52Closure", "Section53Closure"):
        m2a = insert_claim_evidence_simp(m2a, namespace)
    m2a = replace_exact(
        m2a,
        """        (∀ k,
          (A * (k : ℝ) ^ a) * ((blocks k).card : ℝ) ≤
""",
        """        (∀ k : ℕ,
          (A * (k : ℝ) ^ a) * ((blocks k).card : ℝ) ≤
""",
        "Mock2 Advanced type the block index as a natural number",
    )
    m2a = replace_exact(
        m2a,
        "CorrectedLemmas.CorrectedPropositions.FlatQTransport.QLocalSystem V Model",
        "QLocalSystem V Model",
        "Mock2 Advanced use the actual q-local-system type",
    )
    m2a = replace_exact(
        m2a,
        "CorrectedLemmas.CorrectedPropositions.FlatQTransport.RadialDerivation",
        "RadialDerivation",
        "Mock2 Advanced use the actual radial derivation type",
    )
    m2a = replace_exact(
        m2a,
        "CorrectedLemmas.CorrectedPropositions.FlatQTransport.AlgebraicRadialConnection",
        "AlgebraicRadialConnection",
        "Mock2 Advanced use the actual radial connection type",
    )
    m2a = replace_exact(
        m2a,
        """theorem namedClaim_count : Fintype.card Claim = 57 := by
  decide
""",
        """set_option maxRecDepth 10000 in
theorem namedClaim_count : Fintype.card Claim = 57 := by
  decide
""",
        "Mock2 Advanced bound the combined claim-cardinality computation",
    )
    m2a = replace_exact(
        m2a,
        """def literalStatement : LiteralClaim -> Prop
  | .nearZeroPowerWindow =>
      Forall fun alpha : Real => alpha < -(1 / 2 : Real) ->
        IntegrableOn
          (fun y : Real => y ^ (alpha - (1 / 2 : Real))) (Set.Ioo 0 1)
  | .kloostermanTailOne =>
      Forall fun epsilon : Real => 0 < epsilon ->
        Summable (fun n : Nat =>
          1 / abs ((n : Real) + 1) ^ (1 - epsilon))
  | .kloostermanTailHalf =>
      Forall fun epsilon : Real => 0 < epsilon ->
        Summable (fun n : Nat =>
          1 / abs ((n : Real) + 1) ^ ((1 / 2 : Real) - epsilon))
""",
        """def literalStatement : LiteralClaim -> Prop
  | .nearZeroPowerWindow =>
      ∀ alpha : Real, alpha < -(1 / 2 : Real) ->
        IntegrableOn
          (fun y : Real => y ^ (alpha - (1 / 2 : Real))) (Set.Ioo 0 1)
  | .kloostermanTailOne =>
      ∀ epsilon : Real, 0 < epsilon ->
        Summable (fun n : Nat =>
          1 / abs ((n : Real) + 1) ^ (1 - epsilon))
  | .kloostermanTailHalf =>
      ∀ epsilon : Real, 0 < epsilon ->
        Summable (fun n : Nat =>
          1 / abs ((n : Real) + 1) ^ ((1 / 2 : Real) - epsilon))
""",
        "Mock2 Advanced use Lean quantifier syntax in literal claims",
    )
    m2a = replace_exact(
        m2a,
        """def AllLiteralClaims : Prop :=
  Forall fun c : LiteralClaim => literalStatement c
""",
        """def AllLiteralClaims : Prop :=
  ∀ c : LiteralClaim, literalStatement c
""",
        "Mock2 Advanced quantify all literal claims",
    )
    m2a = replace_exact(
        m2a,
        "Function.Periodic.qParam (1 : Real) (tau : Complex)",
        "Function.Periodic.qParam (1 : Nat) (tau : Complex)",
        "Mock2 Advanced use the natural q-parameter width",
    )
    m2a = replace_exact(
        m2a,
        """  | .resolventHalfPlanePoleFree =>
      Forall fun s : Complex => 1 < s.re -> Forall fun t : Real =>
        CorrectedLemmas.MassUnfolding.rankinSelbergResolventDenominator s t ≠ 0
  | .sameChartExterior =>
      Exists fun tau : UpperHalfPlane =>
        1 < norm (paperQ tau)
""",
        """  | .resolventHalfPlanePoleFree =>
      ∀ s : Complex, 1 < s.re -> ∀ t : Real,
        CorrectedLemmas.MassUnfolding.rankinSelbergResolventDenominator s t ≠ 0
  | .sameChartExterior =>
      ∃ tau : UpperHalfPlane,
        1 < norm (paperQ tau)
""",
        "Mock2 Advanced use Lean quantifier syntax in extracted obligations",
    )
    m2a = replace_exact(
        m2a,
        """def AllExtractedObligations : Prop :=
  Forall fun c : ExtractedObligation => obligationStatement c
""",
        """def AllExtractedObligations : Prop :=
  ∀ c : ExtractedObligation, obligationStatement c
""",
        "Mock2 Advanced quantify all extracted obligations",
    )
    M2A.write_text(m2a, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
