from __future__ import annotations

from pathlib import Path

import apply_one_hundred_thirty_sixth_pass_repairs as pass136
import apply_seventy_first_pass_repairs as pass71

ROOT = Path("PrimalitySheafVerification")
replace_exact = pass71.replace_exact


def apply_replacements(path: Path, replacements: list[tuple[str, str, int, str]]) -> None:
    text = path.read_text(encoding="utf-8")
    changed = False
    for old, new, expected, label in replacements:
        text, did = replace_exact(text, old, new, expected, label)
        changed |= did
    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2() -> None:
    apply_replacements(ROOT / "Mock2.lean", [
        (
            """abbrev PairSection (L M : LinearPresheaf X)
""",
            """abbrev PairSection
    (L : LinearPresheaf.{u, v} X) (M : LinearPresheaf.{u, w} X)
""",
            1,
            "Mock2 allow legacy pair factors in independent value universes",
        ),
        (
            """def pairRestriction (L M : LinearPresheaf X)
""",
            """def pairRestriction
    (L : LinearPresheaf.{u, v} X) (M : LinearPresheaf.{u, w} X)
""",
            1,
            "Mock2 generalize componentwise pair restriction",
        ),
        (
            """@[simp] theorem pairRestriction_fst (L M : LinearPresheaf X)
""",
            """@[simp] theorem pairRestriction_fst
    (L : LinearPresheaf.{u, v} X) (M : LinearPresheaf.{u, w} X)
""",
            1,
            "Mock2 generalize the first pair restriction projection",
        ),
        (
            """@[simp] theorem pairRestriction_snd (L M : LinearPresheaf X)
""",
            """@[simp] theorem pairRestriction_snd
    (L : LinearPresheaf.{u, v} X) (M : LinearPresheaf.{u, w} X)
""",
            1,
            "Mock2 generalize the second pair restriction projection",
        ),
        (
            """theorem pairRestriction_id (L M : LinearPresheaf X)
""",
            """theorem pairRestriction_id
    (L : LinearPresheaf.{u, v} X) (M : LinearPresheaf.{u, w} X)
""",
            1,
            "Mock2 generalize pair restriction identity",
        ),
        (
            """theorem pairRestriction_comp (L M : LinearPresheaf X)
""",
            """theorem pairRestriction_comp
    (L : LinearPresheaf.{u, v} X) (M : LinearPresheaf.{u, w} X)
""",
            1,
            "Mock2 generalize pair restriction composition",
        ),
        (
            """def pairPresheaf (L M : LinearPresheaf X) : LinearPresheaf X where
  obj U := ModuleCat.of ℂ (PairSection L M U)
""",
            """def pairPresheaf
    (L : LinearPresheaf.{u, v} X) (M : LinearPresheaf.{u, w} X) :
    LinearPresheaf.{u, max v w} X where
  obj U := ModuleCat.of.{max u (max v w), 0} ℂ (PairSection L M U)
""",
            1,
            "Mock2 place the mixed-universe pair presheaf in the maximum universe",
        ),
        (
            """@[simp] theorem pairPresheaf_obj (L M : LinearPresheaf X)
""",
            """@[simp] theorem pairPresheaf_obj
    (L : LinearPresheaf.{u, v} X) (M : LinearPresheaf.{u, w} X)
""",
            1,
            "Mock2 generalize pair object evaluation",
        ),
        (
            """@[simp] theorem pairPresheaf_res_apply (L M : LinearPresheaf X)
    {U V : TopologicalSpace.Opens X} (hUV : U ≤ V)
    (s : (pairPresheaf L M).obj V) :
    (pairPresheaf L M).res hUV s =
      (L.res hUV s.1, M.res hUV s.2) :=
  rfl
""",
            """@[simp] theorem pairPresheaf_res_apply
    (L : LinearPresheaf.{u, v} X) (M : LinearPresheaf.{u, w} X)
    {U V : TopologicalSpace.Opens X} (hUV : U ≤ V)
    (s : (pairPresheaf L M).obj V) :
    (pairPresheaf L M).res hUV s =
      (L.res hUV (show L.obj V from s.1),
        M.res hUV (show M.obj V from s.2)) :=
  rfl
""",
            1,
            "Mock2 expose both carriers in mixed-universe pair restriction",
        ),
        (
            """structure PairTensorEquivalenceData (L M : LinearPresheaf X) where
""",
            """structure PairTensorEquivalenceData
    (L : LinearPresheaf.{u, v} X) (M : LinearPresheaf.{u, w} X) where
""",
            1,
            "Mock2 generalize pair-tensor equivalence data",
        ),
        (
            """variable {L M : LinearPresheaf X}
""",
            """variable {L : LinearPresheaf.{u, v} X}
  {M : LinearPresheaf.{u, w} X}
""",
            1,
            "Mock2 generalize pair-tensor equivalence namespace variables",
        ),
        (
            """theorem fibre_equiv (H : PairTensorEquivalenceData L M)
""",
            """def fibre_equiv (H : PairTensorEquivalenceData L M)
""",
            1,
            "Mock2 define the data-valued fibre equivalence",
        ),
        (
            """structure PairTensorEquivalenceCertificate
    {L M : LinearPresheaf X} (H : PairTensorEquivalenceData L M) : Prop where
""",
            """structure PairTensorEquivalenceCertificate
    {L : LinearPresheaf.{u, v} X} {M : LinearPresheaf.{u, w} X}
    (H : PairTensorEquivalenceData L M) : Prop where
""",
            1,
            "Mock2 generalize the pair-tensor audit certificate",
        ),
        (
            """theorem pairTensorEquivalence_certificate
    {L M : LinearPresheaf X} (H : PairTensorEquivalenceData L M) :
""",
            """theorem pairTensorEquivalence_certificate
    {L : LinearPresheaf.{u, v} X} {M : LinearPresheaf.{u, w} X}
    (H : PairTensorEquivalenceData L M) :
""",
            1,
            "Mock2 generalize the pair-tensor certificate constructor",
        ),
    ])


def repair_mock2_advanced() -> None:
    apply_replacements(ROOT / "Mock2_Advanced.lean", [
        (
            """  exact add_le_add_right
    (mul_le_mul_of_nonneg_left
      (K.discreteSeries.term_le_contribution j₀ m) N.factor_pos.le)
    (massFunctional D m)
""",
            """  simpa only [add_comm] using
    (add_le_add_right
      (mul_le_mul_of_nonneg_left
        (K.discreteSeries.term_le_contribution j₀ m) N.factor_pos.le)
      (massFunctional D m))
""",
            1,
            "Mock2Advanced normalize the selected-mode mass addition order",
        ),
        (
            """  filter_upwards [hdominates, hlower, hupper] with m hdom hmLower hmUpper
  exact (not_lt_of_ge (hmLower.trans hmUpper)) hdom
""",
            """  obtain ⟨m, hdom, hmLower, hmUpper⟩ :=
    (hdominates.and (hlower.and hupper)).exists
  exact (not_lt_of_ge (hmLower.trans hmUpper)) hdom
""",
            1,
            "Mock2Advanced extract a concrete large index from the eventual contradiction",
        ),
        (
            """      (1 : ℝ≥0) • volume.restrict (Ioo (-δ) δ) =
""",
            """      (1 : NNReal) • volume.restrict (Ioo (-δ) δ) =
""",
            1,
            "Mock2Advanced parse the unit density as a nonnegative real",
        ),
        (
            """  · simp

/-- The active spectral set""",
            """  · simp [smoothVolumeUnitData]

/-- The active spectral set""",
            1,
            "Mock2Advanced reduce the unit-density restricted measure equality",
        ),
    ])


def repair_functional_analysis() -> None:
    apply_replacements(ROOT / "Mock2_FunctionalAnalysis.lean", [
        (
            """    have hfloor :
        ⌊(((n + 2 : ℕ) : ℝ))⌋₊ = n + 2 := by
      norm_num
""",
            """    have hfloor :
        ⌊(((n + 2 : ℕ) : ℝ))⌋₊ = n + 2 := by
      exact Nat.floor_natCast (R := ℝ) (n + 2)
""",
            1,
            "FunctionalAnalysis use the pinned natural-cast floor theorem directly",
        ),
    ])


def main() -> int:
    pass136.main()
    repair_mock2()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
