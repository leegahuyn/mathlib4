from __future__ import annotations

from pathlib import Path

PATH = Path("PrimalitySheafVerification/Mock1_Advanced.lean")


def replace_once(text: str, old: str, new: str, label: str) -> tuple[str, bool]:
    count = text.count(old)
    if count == 0:
        if new in text:
            print(f"{label}: already applied")
            return text, False
        print(f"{label}: source changed; skipped")
        return text, False
    if count != 1:
        raise RuntimeError(f"{label}: expected one match, found {count}")
    print(f"{label}: applied")
    return text.replace(old, new, 1), True


def main() -> int:
    text = PATH.read_text(encoding="utf-8")
    changed = False

    anchor = """def referenceT2PrincipalPart : PrincipalPart Complex where
  order := 2
  coeff := fun _ => 0

"""
    helpers = anchor + """def referenceT1PrincipalPartLink :
    PrincipalPartCertificate Complex where
  laurent := referenceConcreteLaurentQSeries
  principal := referenceT1PrincipalPart
  coeff_eq_laurent := by
    intro i
    rfl

def referenceT2PrincipalPartLink :
    PrincipalPartCertificate Complex where
  laurent := referenceConcreteLaurentQSeries
  principal := referenceT2PrincipalPart
  coeff_eq_laurent := by
    intro i
    rfl

def zeroIntLinearSystemCertificate (rows : Nat) :
    LinearSystemCertificate Int where
  system := {
    rows := rows
    cols := 0
    matrix := { entry := fun _ j => Fin.elim0 j }
    rhs := fun _ => 0
  }
  solution := fun j => Fin.elim0 j
  solution_ok := by
    intro i
    simp [MatrixData.mulVec]

def zeroRatLinearSystemCertificate (rows : Nat) :
    LinearSystemCertificate Rat where
  system := {
    rows := rows
    cols := 0
    matrix := { entry := fun _ j => Fin.elim0 j }
    rhs := fun _ => 0
  }
  solution := fun j => Fin.elim0 j
  solution_ok := by
    intro i
    simp [MatrixData.mulVec]

def zeroComplexIntervalLinearSystemCertificate (rows : Nat) :
    ComplexIntervalLinearSystemCertificate where
  system := {
    rows := rows
    cols := 0
    matrix := { entry := fun _ j => Fin.elim0 j }
    rhs := fun _ => referenceComplexInterval
  }
  solution := fun j => Fin.elim0 j
  residual := fun _ => referenceComplexInterval
  residual_contains_zero := by
    intro i
    change (((0 : Real) <= 0) /\\ ((0 : Real) <= 0)) /\\
      (((0 : Real) <= 0) /\\ ((0 : Real) <= 0))
    exact ⟨⟨le_rfl, le_rfl⟩, ⟨le_rfl, le_rfl⟩⟩

"""
    text, did = replace_once(
        text, anchor, helpers,
        "Mock1Advanced add row-matched principal-part support certificates")
    changed |= did

    old = """noncomputable def referenceT1ConcreteCertificate : ConcreteCertificate Unit :=
  { referenceConcreteCertificate with
    principalPart := referenceT1PrincipalPart
    paperPrincipalPartRows := referenceT1PrincipalPart.order
    paperPrincipalPartRows_eq := rfl }


noncomputable def referenceT2ConcreteCertificate : ConcreteCertificate Unit :=
  { referenceConcreteCertificate with
    principalPart := referenceT2PrincipalPart
    paperPrincipalPartRows := referenceT2PrincipalPart.order
    paperPrincipalPartRows_eq := rfl }
"""
    new = """noncomputable def referenceT1ConcreteCertificate : ConcreteCertificate Unit :=
  { referenceConcreteCertificate with
    principalPart := referenceT1PrincipalPart
    principalPartLink := referenceT1PrincipalPartLink
    principalPartLink_matches := rfl
    principalSystemInt :=
      zeroIntLinearSystemCertificate referenceT1PrincipalPart.order
    intervalSystemRat :=
      zeroRatLinearSystemCertificate referenceT1PrincipalPart.order
    intervalSystemComplex :=
      zeroComplexIntervalLinearSystemCertificate referenceT1PrincipalPart.order
    principalSystemInt_rows_match := rfl
    intervalSystemRat_rows_match := rfl
    intervalSystemComplex_rows_match := rfl
    paperPrincipalPartRows := referenceT1PrincipalPart.order
    paperPrincipalPartRows_eq := rfl }

noncomputable def referenceT2ConcreteCertificate : ConcreteCertificate Unit :=
  { referenceConcreteCertificate with
    principalPart := referenceT2PrincipalPart
    principalPartLink := referenceT2PrincipalPartLink
    principalPartLink_matches := rfl
    principalSystemInt :=
      zeroIntLinearSystemCertificate referenceT2PrincipalPart.order
    intervalSystemRat :=
      zeroRatLinearSystemCertificate referenceT2PrincipalPart.order
    intervalSystemComplex :=
      zeroComplexIntervalLinearSystemCertificate referenceT2PrincipalPart.order
    principalSystemInt_rows_match := rfl
    intervalSystemRat_rows_match := rfl
    intervalSystemComplex_rows_match := rfl
    paperPrincipalPartRows := referenceT2PrincipalPart.order
    paperPrincipalPartRows_eq := rfl }
"""
    text, did = replace_once(
        text, old, new,
        "Mock1Advanced update all dependent fields of the T1/T2 certificates")
    changed |= did

    old = """  residual_not_mem_theorem := by
    simp
"""
    new = """  residual_not_mem_theorem := by
    decide
"""
    text, did = replace_once(
        text, old, new,
        "Mock1Advanced decide the closed residual-table nonmembership")
    changed |= did

    old = """noncomputable def referenceMock1DepthOneConcreteCertificate :
    ConcreteCertificate Unit where
  object := referenceMock1DepthOneObject
  alpha := 1
  beta := 0
  entropyProof := by
    simpa [referenceMock1DepthOneObject] using exactEntropyCoeff_growth 1 0
  completion := referenceCompletion
  shadow := referenceShadow
  rademacher := referenceRademacher
  padic := referencePadic
  regression := referenceRegression
  principalPart := referenceT1PrincipalPart
  spt := referenceSPT
  crt := referenceCRT
  mahler := referenceMahler
  paperObjectName := referenceMock1DepthOneObject.name
  paperFamilyName := referenceMock1DepthOneFamilyName
  paperPrincipalPartRows := referenceT1PrincipalPart.order
  paperCoefficientTableLength := 22
  paperClaimRegistryName := referenceMock1DepthOneRegistryName
  paperObjectName_eq := rfl
  paperFamilyName_nonempty := by decide
  paperPrincipalPartRows_eq := rfl
  paperCoefficientTableLength_pos := by decide
  paperClaimRegistryName_nonempty := by decide
"""
    new = """def referenceMock1DepthOneQSeriesCertificate :
    ObjectQSeriesCertificate where
  object := referenceMock1DepthOneObject
  series := referenceObjectQSeries
  coeff_eq := by
    intro n
    rfl

noncomputable def referenceMock1DepthOneConcreteCertificate :
    ConcreteCertificate Unit :=
  { referenceConcreteCertificate with
    object := referenceMock1DepthOneObject
    qSeriesCertificate := referenceMock1DepthOneQSeriesCertificate
    qSeriesCertificate_matches := rfl
    entropyProof := by
      simpa [referenceMock1DepthOneObject] using exactEntropyCoeff_growth 1 0
    entropyExplicit := by
      simpa [referenceMock1DepthOneObject] using
        exactEntropyCoeff_growth_epsilonN 1 0
    degeneracy_matches := by
      intro n
      rfl
    principalPart := referenceT1PrincipalPart
    principalPartLink := referenceT1PrincipalPartLink
    principalPartLink_matches := rfl
    principalSystemInt :=
      zeroIntLinearSystemCertificate referenceT1PrincipalPart.order
    intervalSystemRat :=
      zeroRatLinearSystemCertificate referenceT1PrincipalPart.order
    intervalSystemComplex :=
      zeroComplexIntervalLinearSystemCertificate referenceT1PrincipalPart.order
    principalSystemInt_rows_match := rfl
    intervalSystemRat_rows_match := rfl
    intervalSystemComplex_rows_match := rfl
    paperObjectName := referenceMock1DepthOneObject.name
    paperFamilyName := referenceMock1DepthOneFamilyName
    paperPrincipalPartRows := referenceT1PrincipalPart.order
    paperCoefficientTableLength := 22
    paperClaimRegistryName := referenceMock1DepthOneRegistryName
    paperObjectName_eq := rfl
    paperFamilyName_nonempty := by decide
    paperPrincipalPartRows_eq := rfl
    paperCoefficientTableLength_pos := by decide
    paperClaimRegistryName_nonempty := by decide }
"""
    text, did = replace_once(
        text, old, new,
        "Mock1Advanced complete the depth-one certificate from the reference record")
    changed |= did

    old = """  depth_one_mem :
    List.Mem instance registry.instances
"""
    new = """  depth_one_mem :
    List.Mem namedInstance registry.instances
"""
    text, did = replace_once(
        text, old, new,
        "Mock1Advanced remove the reserved instance token from depth_one_mem")
    changed |= did

    count = text.count("referencePaperInstancesHCompletionCertificate.instance")
    if count:
        text = text.replace(
            "referencePaperInstancesHCompletionCertificate.instance",
            "referencePaperInstancesHCompletionCertificate.namedInstance")
        changed = True
        print(
            "Mock1Advanced update reference completion-certificate instance projections: "
            f"applied {count}")

    if changed:
        PATH.write_text(text, encoding="utf-8", newline="\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
