#!/usr/bin/env python3
"""Finalize the scope-safe QYM probe with exact independent-frontier repairs."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


EXPECTED_INPUT_SHA256 = (
    "52907b000d31b3f925fd8437ec6aa96beea682d3ba362afbf76c9e49fa188388"
)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def replace_exact(text: str, old: str, new: str, expected: int, label: str,
                  audit: list[dict[str, object]]) -> str:
    count = text.count(old)
    if count != expected:
        raise AssertionError(f"{label}: expected {expected}, found {count}")
    audit.append({"label": label, "occurrences": count})
    return text.replace(old, new)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", required=True)
    parser.add_argument("--output", required=True)
    parser.add_argument("--audit", required=True)
    args = parser.parse_args()

    input_path = Path(args.input)
    raw = input_path.read_bytes()
    if sha256(raw) != EXPECTED_INPUT_SHA256:
        raise AssertionError("scope-safe QYM input SHA-256 mismatch")
    if b"\r" in raw or b"\x00" in raw or not raw.endswith(b"\n"):
        raise AssertionError("scope-safe QYM encoding/newline invariant mismatch")
    text = raw.decode("utf-8")
    audit: list[dict[str, object]] = []

    text = replace_exact(
        text,
        "inductive X where\n"
        "  | left\n"
        "  | middle\n"
        "  | right\n"
        "deriving DecidableEq, Fintype",
        "inductive X where\n"
        "  | left\n"
        "  | middle\n"
        "  | right\n"
        "deriving DecidableEq\n\n"
        "instance : Fintype X where\n"
        "  elems := {X.left, X.middle, X.right}\n"
        "  complete := by\n"
        "    intro x\n"
        "    cases x <;> simp",
        1,
        "replace_broken_fintype_deriving_X",
        audit,
    )
    text = replace_exact(
        text,
        "inductive Patch0Point where\n"
        "  | left\n"
        "  | middle\n"
        "deriving DecidableEq, Fintype",
        "inductive Patch0Point where\n"
        "  | left\n"
        "  | middle\n"
        "deriving DecidableEq\n\n"
        "instance : Fintype Patch0Point where\n"
        "  elems := {Patch0Point.left, Patch0Point.middle}\n"
        "  complete := by\n"
        "    intro x\n"
        "    cases x <;> simp",
        1,
        "replace_broken_fintype_deriving_Patch0Point",
        audit,
    )
    text = replace_exact(
        text,
        "inductive Patch1Point where\n"
        "  | middle\n"
        "  | right\n"
        "deriving DecidableEq, Fintype",
        "inductive Patch1Point where\n"
        "  | middle\n"
        "  | right\n"
        "deriving DecidableEq\n\n"
        "instance : Fintype Patch1Point where\n"
        "  elems := {Patch1Point.middle, Patch1Point.right}\n"
        "  complete := by\n"
        "    intro x\n"
        "    cases x <;> simp",
        1,
        "replace_broken_fintype_deriving_Patch1Point",
        audit,
    )
    text = replace_exact(
        text,
        "inductive OverlapPoint where\n"
        "  | middle\n"
        "deriving DecidableEq, Fintype",
        "inductive OverlapPoint where\n"
        "  | middle\n"
        "deriving DecidableEq\n\n"
        "instance : Fintype OverlapPoint where\n"
        "  elems := {OverlapPoint.middle}\n"
        "  complete := by\n"
        "    intro x\n"
        "    cases x <;> simp",
        1,
        "replace_broken_fintype_deriving_OverlapPoint",
        audit,
    )
    text = replace_exact(
        text,
        "  simpa only [paperSignLevel_apply] using\n"
        "    tendsto_atBot_add_const_right atTop c hneg",
        "  change Tendsto (fun n : ℕ => -(n : ℝ) + c) atTop atBot\n"
        "  exact tendsto_atBot_add_const_right atTop c hneg",
        1,
        "make_paper_sign_tendsto_target_explicit",
        audit,
    )
    text = replace_exact(
        text,
        "  simpa only [correctedSignLevel] using\n"
        "    tendsto_atTop_add_const_right atTop c\n"
        "      (tendsto_natCast_atTop_atTop :\n"
        "        Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)",
        "  change Tendsto (fun n : ℕ => (n : ℝ) + c) atTop atTop\n"
        "  exact tendsto_atTop_add_const_right atTop c\n"
        "    (tendsto_natCast_atTop_atTop :\n"
        "      Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)",
        1,
        "make_corrected_sign_tendsto_target_explicit",
        audit,
    )
    text = replace_exact(
        text,
        "  | .hypA_6 =>\n"
        "      [\"QYM.MassAbsorptionTruncationCore.nonnegative_forms_do_not_imply_positiveDomination\",\n"
        "       \"QYM.FullCertification.PaperNormalized.hypA_6_nonnegativeFormDominationInferenceStatement_refuted\"]\n"
        "  | _ => []",
        "  | .hypA_6 =>\n"
        "      [\"QYM.MassAbsorptionTruncationCore.nonnegative_forms_do_not_imply_positiveDomination\",\n"
        "       \"QYM.FullCertification.PaperNormalized.hypA_6_nonnegativeFormDominationInferenceStatement_refuted\"]",
        1,
        "remove_redundant_claim_match_alternative",
        audit,
    )
    text = replace_exact(
        text,
        "theorem auditRegistry_ids : auditRegistry.map AuditRecord.id = allClaims := by\n"
        "  simp [auditRegistry, record]",
        "theorem auditRegistry_ids : auditRegistry.map AuditRecord.id = allClaims := by\n"
        "  simp only [auditRegistry, List.map_map]\n"
        "  change List.map (fun claim : ClaimId => claim) allClaims = allClaims\n"
        "  rfl",
        1,
        "make_audit_registry_projection_explicit",
        audit,
    )
    text = replace_exact(
        text,
        "    allCertificates.map Certificate.id = allEvidence := by\n"
        "  simp [allCertificates, certificate]",
        "    allCertificates.map Certificate.id = allEvidence := by\n"
        "  simp only [allCertificates, List.map_map]\n"
        "  change List.map (fun evidence : EvidenceId => evidence) allEvidence = allEvidence\n"
        "  rfl",
        10,
        "make_all_certificate_projections_explicit",
        audit,
    )
    text = replace_exact(
        text,
        "    (certificatesForClaim claim).map Certificate.id = evidenceForClaim claim := by\n"
        "  simp [certificatesForClaim, certificate]",
        "    (certificatesForClaim claim).map Certificate.id = evidenceForClaim claim := by\n"
        "  simp only [certificatesForClaim, List.map_map]\n"
        "  change List.map (fun evidence : EvidenceId => evidence) (evidenceForClaim claim) =\n"
        "    evidenceForClaim claim\n"
        "  cases claim <;> rfl",
        10,
        "make_claim_certificate_projections_explicit",
        audit,
    )
    text = replace_exact(
        text,
        "theorem leibniz00 (a b : Form0 R) :\n"
        "    d0 (wedge00 a b) = wedge10 (d0 a) b + wedge01 a (d0 b) := by\n"
        "  simp [d0, wedge00, wedge01, wedge10]",
        "theorem leibniz00 (a b : Form0 R) :\n"
        "    d0 (wedge00 a b) = wedge10 (d0 a) b + wedge01 a (d0 b) := by\n"
        "  ext <;> simp [d0, wedge00, wedge01, wedge10]",
        1,
        "close_product_zero_components_in_leibniz00",
        audit,
    )
    text = replace_exact(
        text,
        "theorem d0_conj0 (g : Rˣ) (a : Form0 R) :\n"
        "    d0 (conj0 g a) = conj1 g (d0 a) := by\n"
        "  simp [d0, conj0, conj1]",
        "theorem d0_conj0 (g : Rˣ) (a : Form0 R) :\n"
        "    d0 (conj0 g a) = conj1 g (d0 a) := by\n"
        "  ext <;> simp [d0, conj0, conj1]",
        1,
        "close_product_zero_components_in_d0_conj0",
        audit,
    )
    text = replace_exact(
        text,
        "theorem projection0_pythagoras (x : Vec2) :\n"
        "    normSq x = normSq (projection0 x) + normSq (x - projection0 x) := by\n"
        "  simp [normSq, dot, projection0]\n"
        "  ring",
        "theorem projection0_pythagoras (x : Vec2) :\n"
        "    normSq x = normSq (projection0 x) + normSq (x - projection0 x) := by\n"
        "  simp [normSq, dot, projection0]",
        1,
        "remove_unreachable_ring_after_projection_simp",
        audit,
    )
    text = replace_exact(
        text,
        "theorem cubicNonlinearity_apply_zero (x : Vec2) :\n"
        "    cubicNonlinearity x 0 = -(normSq x * x 1) := by\n"
        "  simp [cubicNonlinearity]\n"
        "  ring",
        "theorem cubicNonlinearity_apply_zero (x : Vec2) :\n"
        "    cubicNonlinearity x 0 = -(normSq x * x 1) := by\n"
        "  simp [cubicNonlinearity]",
        1,
        "remove_unreachable_ring_after_cubic_simp",
        audit,
    )
    text = replace_exact(
        text,
        "  simp only [Matrix.add_apply, map_add]\n"
        "  ring",
        "  simp only [Matrix.add_apply, star_add]\n"
        "  ring",
        1,
        "use_star_add_in_weighted_pairing",
        audit,
    )
    text = replace_exact(
        text,
        "  simp only [Matrix.smul_apply, smul_eq_mul, map_mul]\n"
        "  ring",
        "  simp only [Matrix.smul_apply, smul_eq_mul, star_mul]\n"
        "  ring",
        1,
        "use_star_mul_in_weighted_pairing",
        audit,
    )
    text = replace_exact(
        text,
        "  simp only [map_add, map_mul, map_ofNat, star_star]\n"
        "  ring",
        "  simp only [star_add, star_mul, map_ofNat, star_star]\n"
        "  ring",
        1,
        "use_star_laws_in_weighted_pairing_symmetry",
        audit,
    )
    text = replace_exact(
        text,
        "def windowIndices {n : ℕ} (spectrum : Fin n → ℝ) (center radius : ℝ) : Finset (Fin n) :=\n"
        "  Finset.univ.filter fun i => InWindow center radius (spectrum i)",
        "def windowIndices {n : ℕ} (spectrum : Fin n → ℝ) (center radius : ℝ) : Finset (Fin n) := by\n"
        "  classical\n"
        "  exact Finset.univ.filter fun i => InWindow center radius (spectrum i)",
        1,
        "make_window_predicate_decidable_locally",
        audit,
    )
    text = replace_exact(
        text,
        "theorem invariantUnder_add {G X Y : Type*} [Add Y]\n"
        "    {transform : G → X → X} {F H : X → Y}\n"
        "    (hF : InvariantUnder transform F) (hH : InvariantUnder transform H) :\n"
        "    InvariantUnder transform (fun x => F x + H x) := by\n"
        "  intro g x\n"
        "  rw [hF g x, hH g x]",
        "theorem invariantUnder_add {G X Y : Type*} [Add Y]\n"
        "    {transform : G → X → X} {F H : X → Y}\n"
        "    (hF : InvariantUnder transform F) (hH : InvariantUnder transform H) :\n"
        "    InvariantUnder transform (fun x => F x + H x) := by\n"
        "  intro g x\n"
        "  change F (transform g x) + H (transform g x) = F x + H x\n"
        "  rw [hF g x, hH g x]",
        1,
        "expose_beta_redex_in_invariant_add",
        audit,
    )
    text = replace_exact(
        text,
        "theorem invariantUnder_neg {G X Y : Type*} [Neg Y]\n"
        "    {transform : G → X → X} {F : X → Y}\n"
        "    (hF : InvariantUnder transform F) :\n"
        "    InvariantUnder transform (fun x => -F x) := by\n"
        "  intro g x\n"
        "  rw [hF g x]",
        "theorem invariantUnder_neg {G X Y : Type*} [Neg Y]\n"
        "    {transform : G → X → X} {F : X → Y}\n"
        "    (hF : InvariantUnder transform F) :\n"
        "    InvariantUnder transform (fun x => -F x) := by\n"
        "  intro g x\n"
        "  change -F (transform g x) = -F x\n"
        "  rw [hF g x]",
        1,
        "expose_beta_redex_in_invariant_neg",
        audit,
    )
    text = replace_exact(
        text,
        "theorem invariantUnder_sub {G X Y : Type*} [Sub Y]\n"
        "    {transform : G → X → X} {F H : X → Y}\n"
        "    (hF : InvariantUnder transform F) (hH : InvariantUnder transform H) :\n"
        "    InvariantUnder transform (fun x => F x - H x) := by\n"
        "  intro g x\n"
        "  rw [hF g x, hH g x]",
        "theorem invariantUnder_sub {G X Y : Type*} [Sub Y]\n"
        "    {transform : G → X → X} {F H : X → Y}\n"
        "    (hF : InvariantUnder transform F) (hH : InvariantUnder transform H) :\n"
        "    InvariantUnder transform (fun x => F x - H x) := by\n"
        "  intro g x\n"
        "  change F (transform g x) - H (transform g x) = F x - H x\n"
        "  rw [hF g x, hH g x]",
        1,
        "expose_beta_redex_in_invariant_sub",
        audit,
    )
    text = replace_exact(
        text,
        "theorem eigenvalue_zero : eigenvalue 0 = 0 := by\n"
        "  norm_num [eigenvalue]",
        "theorem eigenvalue_zero : eigenvalue 0 = 0 := by\n"
        "  have h : (0 : Fin 3) ≠ 2 := by decide\n"
        "  simp only [eigenvalue, if_neg h]",
        1,
        "decide_fin3_zero_ne_two_for_eigenvalue",
        audit,
    )
    text = replace_exact(
        text,
        "theorem eigenvalue_one : eigenvalue 1 = 0 := by\n"
        "  norm_num [eigenvalue]",
        "theorem eigenvalue_one : eigenvalue 1 = 0 := by\n"
        "  have h : (1 : Fin 3) ≠ 2 := by decide\n"
        "  simp only [eigenvalue, if_neg h]",
        1,
        "decide_fin3_one_ne_two_for_eigenvalue",
        audit,
    )
    text = replace_exact(
        text,
        "theorem zero_isGround : IsGroundIndex 0 := by\n"
        "  norm_num [IsGroundIndex]",
        "theorem zero_isGround : IsGroundIndex 0 := by\n"
        "  change (0 : Fin 3) ≠ 2\n"
        "  decide",
        1,
        "decide_fin3_zero_ground_membership",
        audit,
    )
    text = replace_exact(
        text,
        "theorem one_isGround : IsGroundIndex 1 := by\n"
        "  norm_num [IsGroundIndex]",
        "theorem one_isGround : IsGroundIndex 1 := by\n"
        "  change (1 : Fin 3) ≠ 2\n"
        "  decide",
        1,
        "decide_fin3_one_ground_membership",
        audit,
    )
    text = replace_exact(
        text,
        "theorem eigenvalue_eq_zero_of_isGround\n"
        "    (i : Fin 3) (hi : IsGroundIndex i) : eigenvalue i = 0 := by\n"
        "  simp [eigenvalue, IsGroundIndex, hi]",
        "theorem eigenvalue_eq_zero_of_isGround\n"
        "    (i : Fin 3) (hi : IsGroundIndex i) : eigenvalue i = 0 := by\n"
        "  change i ≠ (2 : Fin 3) at hi\n"
        "  simp only [eigenvalue, if_neg hi]",
        1,
        "use_ground_hypothesis_for_fin3_eigenvalue",
        audit,
    )
    text = replace_exact(
        text,
        "      add_le_add_left (neg_relativeTerms_le_perturbation hbound x) (kinetic x)",
        "      add_le_add_right (neg_relativeTerms_le_perturbation hbound x) (kinetic x)",
        1,
        "correct_lower_enclosure_addition_side",
        audit,
    )
    text = replace_exact(
        text,
        "      add_le_add_left (perturbation_le_relativeMajorant hbound x) (kinetic x)",
        "      add_le_add_right (perturbation_le_relativeMajorant hbound x) (kinetic x)",
        1,
        "correct_upper_enclosure_addition_side",
        audit,
    )
    text = replace_exact(
        text,
        "      add_le_add_right hscaled (b * normSq x)",
        "      add_le_add_left hscaled (b * normSq x)",
        1,
        "correct_upper_bound_scaling_addition_side",
        audit,
    )
    text = replace_exact(
        text,
        "      add_le_add_right (hshiftedLower x) (shift * normSq x)",
        "      add_le_add_left (hshiftedLower x) (shift * normSq x)",
        1,
        "correct_shifted_lower_bound_addition_side",
        audit,
    )
    text = replace_exact(
        text,
        "  have hindex : (n : ℝ) ≤ 2 * (n : ℝ) + 1 := by\n"
        "    linarith [Nat.cast_nonneg n]",
        "  have hindex : (n : ℝ) ≤ 2 * (n : ℝ) + 1 := by\n"
        "    linarith [(Nat.cast_nonneg n : 0 ≤ (n : ℝ))]",
        1,
        "pin_nat_cast_order_for_adjacent_gap",
        audit,
    )
    text = replace_exact(
        text,
        "  have hnposReal : (1 : ℝ) ≤ (n : ℝ) :=\n"
        "    Nat.cast_le.mpr hnpos",
        "  have hnposReal : (1 : ℝ) ≤ (n : ℝ) := by\n"
        "    exact_mod_cast hnpos",
        1,
        "make_nat_to_real_order_cast_explicit",
        audit,
    )
    text = replace_exact(
        text,
        "/-- A dependent evidence object retaining the proposition proved by its tag. -/\n"
        "structure Certificate where\n"
        "  id : EvidenceId\n"
        "  proof : EvidenceStatement id",
        "/-- A dependent evidence object retaining the proposition proved by its tag. -/\n"
        "structure Certificate where\n"
        "  id : EvidenceId\n"
        "  proof : EvidenceStatement.{0, 0, 0, 0, 0, 0, 0} id",
        1,
        "pin_direct_method_certificate_universes",
        audit,
    )
    text = replace_exact(
        text,
        "/-! ## Finite approximants and exact window cardinality -/",
        "attribute [local instance] Classical.propDecidable\n\n"
        "/-! ## Finite approximants and exact window cardinality -/",
        1,
        "enable_classical_decidability_for_window_counts",
        audit,
    )

    text = replace_exact(
        text,
        "/-- The specified coercivity constant gives the corresponding sharp "
        "operator lower bound. -/\nsection SpecifiedConstantLowerBound",
        "/- The specified coercivity constant gives the corresponding sharp "
        "operator lower bound. -/\nsection SpecifiedConstantLowerBound",
        1,
        "ordinary_comment_before_section",
        audit,
    )
    text = replace_exact(
        text,
        "    mod_cast congr_arg RCLike.re\n",
        "    exact_mod_cast congr_arg RCLike.re\n",
        2,
        "modernize_tactic_mode_mod_cast",
        audit,
    )
    text = replace_exact(
        text,
        "isCompact_iff_isClosed_bounded.mpr",
        "Metric.isCompact_iff_isClosed_bounded.mpr",
        1,
        "qualify_metric_compactness_criterion",
        audit,
    )
    text = replace_exact(
        text,
        "  min |x - y| |2 - |x - y||",
        "  min (abs (x - y)) (abs (2 - abs (x - y)))",
        1,
        "make_nested_absolute_values_parser_explicit",
        audit,
    )

    candidate = text.encode("utf-8")
    if b"\r" in candidate or b"\x00" in candidate or not candidate.endswith(b"\n"):
        raise AssertionError("final probe candidate encoding/newline invariant mismatch")
    output_path = Path(args.output)
    audit_path = Path(args.audit)
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_bytes(candidate)
    result = {
        "schema": "qym-repair-probe-finalizer-v1",
        "input_sha256": EXPECTED_INPUT_SHA256,
        "output_sha256": sha256(candidate),
        "input_bytes": len(raw),
        "output_bytes": len(candidate),
        "input_lf": raw.count(b"\n"),
        "output_lf": candidate.count(b"\n"),
        "rewrites": audit,
    }
    with audit_path.open("w", encoding="utf-8", newline="\n") as handle:
        handle.write(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
