#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import hashlib
import json
import re
import sys

SECTION_START = "/-! ## 5. The actual quotient fibre as a one-dimensional complex module -/\n"
SECTION_END = "/-- The Hermitian norm on the actual quotient total space. -/"
FIBRE_OLD = """/-- The actual fibre over a quotient point. -/
noncomputable abbrev InverseEtaFibre (x : InverseEtaBase) :=
  QYM.FullCertification.Mock2EtaPeterssonCarrierExtension.EtaAutomorphicLineBundle.Fibre x
"""
VARIANTS = {
    "explicit_simpa": ("explicit", "simpa"),
    "explicit_cases": ("explicit", "cases"),
    "opaque_instance_simpa": ("instance", "simpa"),
    "opaque_instance_cases": ("instance", "cases"),
}

FIBRE_EXPLICIT = '''/-- The actual fibre over a quotient point.  It is written as the
literal projection subtype so that topology and other subtype instances are
visible to typeclass synthesis without unfolding an opaque bundle-field
definition. -/
noncomputable abbrev InverseEtaFibre (x : InverseEtaBase) :=
  {z : InverseEtaTotal // inverseEtaProjection z = x}
'''

FIBRE_INSTANCE = '''/-- The actual fibre over a quotient point. -/
noncomputable abbrev InverseEtaFibre (x : InverseEtaBase) :=
  QYM.FullCertification.Mock2EtaPeterssonCarrierExtension.EtaAutomorphicLineBundle.Fibre x

/-- Re-expose the ordinary subtype topology hidden behind the opaque
`AutomorphicLineBundle.Fibre` definition. -/
noncomputable instance inverseEtaFibreTopologicalSpace
    (x : InverseEtaBase) : TopologicalSpace (InverseEtaFibre x) := by
  change TopologicalSpace
    {z : InverseEtaTotal // inverseEtaProjection z = x}
  infer_instance
'''

COORDINATE_INVERSE_SIMPA = '''@[simp] theorem inverseEtaFibreOfCoordinate_coordinate
    (x : InverseEtaBase) (u : InverseEtaFibre x) :
    inverseEtaFibreOfCoordinate x (inverseEtaFibreCoordinate u) = u := by
  apply Subtype.ext
  simpa only [u.2] using
    totalOfBaseScalar_projection_coordinate u.1
'''

COORDINATE_INVERSE_CASES = '''@[simp] theorem inverseEtaFibreOfCoordinate_coordinate
    (x : InverseEtaBase) (u : InverseEtaFibre x) :
    inverseEtaFibreOfCoordinate x (inverseEtaFibreCoordinate u) = u := by
  apply Subtype.ext
  cases u.2
  exact totalOfBaseScalar_projection_coordinate u.1
'''

COMMON_BEFORE_INVERSE = '''/-! ## 5. The actual quotient fibre as a one-dimensional complex module -/

/-- The invariant complex coordinate of a point in a fixed actual fibre. -/
noncomputable def inverseEtaFibreCoordinate
    {x : InverseEtaBase} (u : InverseEtaFibre x) : ℂ :=
  etaTrivializedCoordinate u.1

/-- Build a point of the actual fibre from its unique complex coordinate. -/
noncomputable def inverseEtaFibreOfCoordinate
    (x : InverseEtaBase) (c : ℂ) : InverseEtaFibre x :=
  ⟨totalOfBaseScalar x c,
    inverseEtaProjection_totalOfBaseScalar x c⟩

@[simp] theorem inverseEtaFibreCoordinate_ofCoordinate
    (x : InverseEtaBase) (c : ℂ) :
    inverseEtaFibreCoordinate (inverseEtaFibreOfCoordinate x c) = c :=
  etaTrivializedCoordinate_totalOfBaseScalar x c

'''

COMMON_AFTER_INVERSE = '''
/-- Every actual quotient fibre is canonically equivalent to `C`. -/
noncomputable def inverseEtaFibreCoordinateEquiv (x : InverseEtaBase) :
    InverseEtaFibre x ≃ ℂ where
  toFun := inverseEtaFibreCoordinate
  invFun := inverseEtaFibreOfCoordinate x
  left_inv := inverseEtaFibreOfCoordinate_coordinate x
  right_inv := inverseEtaFibreCoordinate_ofCoordinate x

/-- The fibre coordinate is continuous for the actual quotient-subspace
topology. -/
theorem inverseEtaFibreCoordinate_continuous (x : InverseEtaBase) :
    Continuous (inverseEtaFibreCoordinate (x := x)) := by
  change Continuous
    (fun u : {z : InverseEtaTotal // inverseEtaProjection z = x} =>
      etaTrivializedCoordinate u.1)
  exact etaTrivializedCoordinate_continuous.comp continuous_subtype_val

/-- Reconstruction of one fixed fibre is continuous. -/
theorem inverseEtaFibreOfCoordinate_continuous (x : InverseEtaBase) :
    Continuous (inverseEtaFibreOfCoordinate x) := by
  have hTotal : Continuous
      (fun c : ℂ => totalOfBaseScalar x c) := by
    simpa only [Function.comp_apply, id_eq] using
      totalOfBaseScalar_continuous.comp
        (continuous_const.prodMk continuous_id)
  change Continuous
    (fun c : ℂ =>
      (⟨totalOfBaseScalar x c,
        inverseEtaProjection_totalOfBaseScalar x c⟩ :
        {z : InverseEtaTotal // inverseEtaProjection z = x}))
  exact hTotal.subtype_mk
    (fun c => inverseEtaProjection_totalOfBaseScalar x c)

/-- Each actual quotient fibre is homeomorphic to the standard complex line,
not merely in bijection with it. -/
noncomputable def inverseEtaFibreCoordinateHomeomorph
    (x : InverseEtaBase) : InverseEtaFibre x ≃ₜ ℂ where
  toEquiv := inverseEtaFibreCoordinateEquiv x
  continuous_toFun := inverseEtaFibreCoordinate_continuous x
  continuous_invFun := inverseEtaFibreOfCoordinate_continuous x

/-- Transport the additive complex-line structure to the actual quotient
fibre along the proved coordinate equivalence. -/
noncomputable instance inverseEtaFibreAddCommGroup (x : InverseEtaBase) :
    AddCommGroup (InverseEtaFibre x) :=
  (inverseEtaFibreCoordinateEquiv x).addCommGroup

/-- Transport complex scalar multiplication to the actual quotient fibre. -/
noncomputable instance inverseEtaFibreModule (x : InverseEtaBase) :
    Module ℂ (InverseEtaFibre x) :=
  Equiv.module ℂ (inverseEtaFibreCoordinateEquiv x)

/-- The coordinate equivalence is complex linear for the transported fibre
operations. -/
noncomputable def inverseEtaFibreCoordinateLinearEquiv
    (x : InverseEtaBase) : InverseEtaFibre x ≃ₗ[ℂ] ℂ :=
  (inverseEtaFibreCoordinateEquiv x).linearEquiv ℂ

@[simp] theorem inverseEtaFibreCoordinate_zero (x : InverseEtaBase) :
    inverseEtaFibreCoordinate (0 : InverseEtaFibre x) = 0 :=
  (inverseEtaFibreCoordinateLinearEquiv x).map_zero

@[simp] theorem inverseEtaFibreCoordinate_add
    {x : InverseEtaBase} (u v : InverseEtaFibre x) :
    inverseEtaFibreCoordinate (u + v) =
      inverseEtaFibreCoordinate u + inverseEtaFibreCoordinate v :=
  (inverseEtaFibreCoordinateLinearEquiv x).map_add u v

@[simp] theorem inverseEtaFibreCoordinate_neg
    {x : InverseEtaBase} (u : InverseEtaFibre x) :
    inverseEtaFibreCoordinate (-u) = -inverseEtaFibreCoordinate u :=
  (inverseEtaFibreCoordinateLinearEquiv x).map_neg u

@[simp] theorem inverseEtaFibreCoordinate_smul
    {x : InverseEtaBase} (c : ℂ) (u : InverseEtaFibre x) :
    inverseEtaFibreCoordinate (c • u) =
      c * inverseEtaFibreCoordinate u := by
  change
    (inverseEtaFibreCoordinateLinearEquiv x) (c • u) =
      c • (inverseEtaFibreCoordinateLinearEquiv x) u
  exact (inverseEtaFibreCoordinateLinearEquiv x).map_smul c u

/-- A local coordinate represented at an upstairs point, packaged as a point
of the corresponding actual quotient fibre. -/
noncomputable def inverseEtaFibreMk (tau : H) (z : ℂ) :
    InverseEtaFibre (Mock2.Definition15Geometry.quotientMap tau) :=
  ⟨inverseEtaTotalMk tau z, inverseEtaProjection_mk tau z⟩

@[simp] theorem inverseEtaFibreCoordinate_mk (tau : H) (z : ℂ) :
    inverseEtaFibreCoordinate (inverseEtaFibreMk tau z) =
      Mock2.Definition15Geometry.EtaHalfWeight.etaValue tau * z := by
  rfl

@[simp] theorem inverseEtaFibreMk_zero (tau : H) :
    inverseEtaFibreMk tau 0 =
      (0 : InverseEtaFibre
        (Mock2.Definition15Geometry.quotientMap tau)) := by
  apply (inverseEtaFibreCoordinateEquiv _).injective
  change
    inverseEtaFibreCoordinate (inverseEtaFibreMk tau 0) =
      inverseEtaFibreCoordinate
        (0 : InverseEtaFibre
          (Mock2.Definition15Geometry.quotientMap tau))
  rw [inverseEtaFibreCoordinate_mk, inverseEtaFibreCoordinate_zero]
  ring

@[simp] theorem inverseEtaFibreMk_add
    (tau : H) (z w : ℂ) :
    inverseEtaFibreMk tau (z + w) =
      inverseEtaFibreMk tau z + inverseEtaFibreMk tau w := by
  apply (inverseEtaFibreCoordinateEquiv _).injective
  change
    inverseEtaFibreCoordinate (inverseEtaFibreMk tau (z + w)) =
      inverseEtaFibreCoordinate
        (inverseEtaFibreMk tau z + inverseEtaFibreMk tau w)
  rw [inverseEtaFibreCoordinate_mk,
    inverseEtaFibreCoordinate_add,
    inverseEtaFibreCoordinate_mk,
    inverseEtaFibreCoordinate_mk]
  ring

@[simp] theorem inverseEtaFibreMk_smul
    (tau : H) (c z : ℂ) :
    inverseEtaFibreMk tau (c * z) =
      c • inverseEtaFibreMk tau z := by
  apply (inverseEtaFibreCoordinateEquiv _).injective
  change
    inverseEtaFibreCoordinate (inverseEtaFibreMk tau (c * z)) =
      inverseEtaFibreCoordinate (c • inverseEtaFibreMk tau z)
  rw [inverseEtaFibreCoordinate_mk,
    inverseEtaFibreCoordinate_smul,
    inverseEtaFibreCoordinate_mk]
  ring

/-! ## 6. Descent of the exact inverse-eta Hermitian metric -/

/-- The descended Hermitian pairing on a fixed actual quotient fibre. -/
noncomputable def inverseEtaFibreHermitian
    {x : InverseEtaBase}
    (u v : InverseEtaFibre x) : ℂ :=
  ⟪inverseEtaFibreCoordinate u, inverseEtaFibreCoordinate v⟫_ℂ

/-- The descended pairing pulls back exactly to the base-dependent metric
already constructed in P1. -/
@[simp] theorem inverseEtaFibreHermitian_mk
    (tau : H) (z w : ℂ) :
    inverseEtaFibreHermitian
        (inverseEtaFibreMk tau z) (inverseEtaFibreMk tau w) =
      QYM.FullCertification.P1AdmissibleBackgroundExtension.inverseEtaHermitianMetricData.pairing tau z w := by
  rw [inverseEtaFibreHermitian,
    inverseEtaFibreCoordinate_mk, inverseEtaFibreCoordinate_mk,
    QYM.FullCertification.P1AdmissibleBackgroundExtension.inverseEtaHermitianMetricData_pairing]

/-- Conjugate symmetry of the descended pairing. -/
theorem inverseEtaFibreHermitian_conj_symm
    {x : InverseEtaBase} (u v : InverseEtaFibre x) :
    conj (inverseEtaFibreHermitian v u) =
      inverseEtaFibreHermitian u v := by
  exact inner_conj_symm _ _

/-- Additivity in the second argument. -/
theorem inverseEtaFibreHermitian_add_right
    {x : InverseEtaBase} (u v w : InverseEtaFibre x) :
    inverseEtaFibreHermitian u (v + w) =
      inverseEtaFibreHermitian u v +
        inverseEtaFibreHermitian u w := by
  simp only [inverseEtaFibreHermitian,
    inverseEtaFibreCoordinate_add, inner_add_right]

/-- Complex linearity in the second argument. -/
theorem inverseEtaFibreHermitian_smul_right
    {x : InverseEtaBase} (c : ℂ) (u v : InverseEtaFibre x) :
    inverseEtaFibreHermitian u (c • v) =
      c * inverseEtaFibreHermitian u v := by
  unfold inverseEtaFibreHermitian
  rw [inverseEtaFibreCoordinate_smul]
  change
    ⟪inverseEtaFibreCoordinate u,
      c • inverseEtaFibreCoordinate v⟫_ℂ =
      c • ⟪inverseEtaFibreCoordinate u,
        inverseEtaFibreCoordinate v⟫_ℂ
  simp only [inner_smul_right]

/-- The real part on the diagonal is the square of the descended norm. -/
theorem inverseEtaFibreHermitian_self_re
    {x : InverseEtaBase} (u : InverseEtaFibre x) :
    (inverseEtaFibreHermitian u u).re =
      ‖inverseEtaFibreCoordinate u‖ ^ 2 := by
  unfold inverseEtaFibreHermitian
  exact inner_self_eq_norm_sq (𝕜 := ℂ)
    (inverseEtaFibreCoordinate u)

/-- Positive definiteness on the actual quotient fibre. -/
theorem inverseEtaFibreHermitian_self_pos
    {x : InverseEtaBase} {u : InverseEtaFibre x} (hu : u ≠ 0) :
    0 < (inverseEtaFibreHermitian u u).re := by
  rw [inverseEtaFibreHermitian_self_re]
  have hCoordinate : inverseEtaFibreCoordinate u ≠ 0 := by
    intro hZero
    apply hu
    apply (inverseEtaFibreCoordinateEquiv x).injective
    change
      inverseEtaFibreCoordinate u =
        inverseEtaFibreCoordinate (0 : InverseEtaFibre x)
    rw [hZero, inverseEtaFibreCoordinate_zero]
  exact pow_pos (norm_pos_iff.mpr hCoordinate) 2

'''


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def blob(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def audit(text: str) -> dict[str, int]:
    return {
        "sorry": len(re.findall(r"\bsorry\b", text)),
        "admit": len(re.findall(r"\badmit\b", text)),
        "native_decide": len(re.findall(r"\bnative_decide\b", text)),
        "Lean.ofReduceBool": text.count("Lean.ofReduceBool"),
        "global_axiom": len(re.findall(r"(?m)^\s*axiom\s+", text)),
        "unsafe": len(re.findall(r"(?m)^\s*unsafe\s+", text)),
        "maxHeartbeats_zero": len(re.findall(r"set_option\s+maxHeartbeats\s+0\b", text)),
    }


def main() -> None:
    if len(sys.argv) != 4 or sys.argv[1] not in VARIANTS:
        raise SystemExit(
            f"usage: {Path(sys.argv[0]).name} VARIANT INPUT_QYM OUTPUT_QYM"
        )
    variant = sys.argv[1]
    topology, inverse_style = VARIANTS[variant]
    source_path = Path(sys.argv[2])
    output_path = Path(sys.argv[3])
    before = source_path.read_bytes()
    text = before.decode("utf-8")
    if text.count(FIBRE_OLD) != 1:
        raise SystemExit(f"unexpected fibre block count={text.count(FIBRE_OLD)}")
    if text.count(SECTION_START) != 1 or text.count(SECTION_END) != 1:
        raise SystemExit(
            f"unexpected section markers start={text.count(SECTION_START)} end={text.count(SECTION_END)}"
        )
    before_audit = audit(text)
    fibre_replacement = FIBRE_EXPLICIT if topology == "explicit" else FIBRE_INSTANCE
    text = text.replace(FIBRE_OLD, fibre_replacement, 1)
    section_start_index = text.index(SECTION_START)
    section_end_index = text.index(SECTION_END, section_start_index)
    inverse_proof = (
        COORDINATE_INVERSE_SIMPA
        if inverse_style == "simpa"
        else COORDINATE_INVERSE_CASES
    )
    replacement = COMMON_BEFORE_INVERSE + inverse_proof + COMMON_AFTER_INVERSE
    patched = text[:section_start_index] + replacement + text[section_end_index:]
    after_audit = audit(patched)
    if after_audit != before_audit or any(after_audit.values()):
        raise SystemExit(f"forbidden-token delta {before_audit} -> {after_audit}")
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(patched, encoding="utf-8")
    after = output_path.read_bytes()
    section_start = patched.count("\n", 0, section_start_index) + 1
    section_end = patched.count("\n", 0, section_start_index + len(replacement)) + 1
    print(json.dumps({
        "schema": "qym-gb77-fixedorigin-v17-inverse-eta-patch-v1",
        "variant": variant,
        "topology_strategy": topology,
        "dependent_transport_strategy": inverse_style,
        "input_sha256": sha(before),
        "input_blob": blob(before),
        "candidate_sha256": sha(after),
        "candidate_blob": blob(after),
        "section_start_line": section_start,
        "section_end_line": section_end,
        "forbidden": after_audit,
        "bytes": len(after),
        "lf": after.count(b"\n"),
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
