#!/usr/bin/env python3
from pathlib import Path
import hashlib, json, re, sys

BASE_SHA256 = "790b40c05a8f3735dd171a135eda65de92ab68b247d13e7e2ffe2968e3798421"
BASE_BLOB = "33e4fab1130e4c17ea5d212fe2691c3e0c0eb8d3"
VARIANTS = {"first3": 1, "first6": 2, "first13": 3}

NAMESPACE_ANCHOR = "namespace QYM.FullCertification.P2ExplicitEdgeVelocityExtension\n"
NAMESPACE_REPLACEMENT = """namespace QYM.FullCertification.P2ExplicitEdgeVelocityExtension

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
attribute [local instance 1001] NormedSpace.toModule
"""

OLD_EDGE = r'''theorem edgeParameterTransport_hasDerivAt
    (e : QYM.FullCertification.PolygonTraceExtension.PolygonEdge) (t : ℝ) :
    HasDerivAt (QYM.FullCertification.P2NormalGreenExtension.edgeParameterTransport e)
      (e.2.parameterSign : ℝ) t := by
  simpa [QYM.FullCertification.P2NormalGreenExtension.edgeParameterTransport] using
    (hasDerivAt_id t).const_mul (e.2.parameterSign : ℝ)
'''
NEW_EDGE = r'''theorem edgeParameterTransport_hasDerivAt
    (e : QYM.FullCertification.PolygonTraceExtension.PolygonEdge) (t : ℝ) :
    HasDerivAt (QYM.FullCertification.P2NormalGreenExtension.edgeParameterTransport e)
      (e.2.parameterSign : ℝ) t := by
  change HasDerivAt (fun x : ℝ => (e.2.parameterSign : ℝ) * x)
    (e.2.parameterSign : ℝ) t
  exact (hasDerivAt_id t).const_mul (e.2.parameterSign : ℝ)
'''

OLD_C8 = r'''theorem conj_mul_hyperbolicRightNormal_realMultiple_re
    (y s : ℝ) (v : ℂ) :
    (star v *
      hyperbolicRightNormal y (((s : ℝ) : ℂ) * v)).re = 0 := by
  simp [hyperbolicRightNormal, Complex.mul_re, Complex.mul_im]
  ring_nf
'''
NEW_C8 = r'''theorem conj_mul_hyperbolicRightNormal_realMultiple_re
    (y s : ℝ) (v : ℂ) :
    (star v *
      hyperbolicRightNormal y (((s : ℝ) : ℂ) * v)).re = 0 := by
  simp [hyperbolicRightNormal, Complex.mul_re, Complex.mul_im,
    Complex.inv_re, Complex.inv_im]
  ring
'''

OLD_C9 = r'''theorem conj_mul_hyperbolicRightNormal_im {y : ℝ} {w : ℂ}
    (hw : w ≠ 0) :
    (star w * hyperbolicRightNormal y w).im =
      -y * ‖w‖ := by
  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  rw [hyperbolicRightNormal,
    show star w * ((((y / ‖w‖ : ℝ) : ℂ) * (-Complex.I)) * w) =
        (((y / ‖w‖ : ℝ) : ℂ) * (-Complex.I)) *
          (star w * w) by ring]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
    neg_zero, mul_zero, zero_mul, sub_zero, zero_sub,
    pow_two]
  field_simp [hn]
  <;> ring_nf
'''
NEW_C9 = r'''theorem conj_mul_hyperbolicRightNormal_im {y : ℝ} {w : ℂ}
    (hw : w ≠ 0) :
    (star w * hyperbolicRightNormal y w).im =
      -y * ‖w‖ := by
  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  have hstar : star w * w = (Complex.normSq w : ℂ) := by
    simpa [Complex.star_def] using
      (Complex.normSq_eq_conj_mul_self (z := w)).symm
  rw [hyperbolicRightNormal,
    show star w * ((((y / ‖w‖ : ℝ) : ℂ) * (-Complex.I)) * w) =
        (((y / ‖w‖ : ℝ) : ℂ) * (-Complex.I)) *
          (star w * w) by ring,
    hstar]
  simp [Complex.mul_im, Complex.normSq_eq_norm_sq]
  field_simp [hn]
  ring
'''

ATLAS_BLOCK = r'''section ConditionalSmoothAtlas

variable (hSmooth : SmoothTransitionResidual)
include hSmooth

local instance conditionalChartedSpaceH :
    ChartedSpace ℍ GammaTwoQuotient :=
  allCoveringSheetsChartedSpaceH

private theorem conditionalHasGroupoidH :
    HasGroupoid GammaTwoQuotient upperHalfPlaneSmoothGroupoid :=
  allCoveringSheets_hasGroupoid hSmooth

/-- Compose the all-sheets atlas with the standard complex atlas on `ℍ`. -/
local instance conditionalChartedSpaceComplex :
    ChartedSpace ℂ GammaTwoQuotient :=
  ChartedSpace.comp ℂ ℍ GammaTwoQuotient

/-- Groupoid composition turns the single transition residual into the usual
complex smooth-atlas compatibility condition. -/
private theorem conditionalHasGroupoidComplex :
    HasGroupoid GammaTwoQuotient (contDiffGroupoid ∞ 𝓘(ℂ)) := by
  letI : HasGroupoid GammaTwoQuotient upperHalfPlaneSmoothGroupoid :=
    conditionalHasGroupoidH hSmooth
  apply StructureGroupoid.HasGroupoid.comp upperHalfPlaneSmoothGroupoid
  intro e he
  rw [isLocalStructomorphOn_contDiffGroupoid_iff]
  change
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ e e.source ∧
      ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ e.symm e.target at he
  exact he

/-- Conditional construction of the genuine smooth quotient manifold.  The
only hypothesis is `SmoothTransitionResidual`; no additional topological or
atlas premise is hidden in this theorem. -/
theorem gammaTwoQuotient_isManifold_of_smoothTransitionResidual :
    IsManifold 𝓘(ℂ) ∞ GammaTwoQuotient := by
  letI : HasGroupoid GammaTwoQuotient (contDiffGroupoid ∞ 𝓘(ℂ)) :=
    conditionalHasGroupoidComplex hSmooth
  exact IsManifold.mk' 𝓘(ℂ) ∞ GammaTwoQuotient

private theorem conditionalIsManifold :
    IsManifold 𝓘(ℂ) ∞ GammaTwoQuotient :=
  gammaTwoQuotient_isManifold_of_smoothTransitionResidual hSmooth

/-! ## 5. Open stage interiors -/

/-- The largest open submanifold canonically contained in the intrinsic closed
stage.  The closed subtype itself is not an `Opens`, so Mathlib's manifold
inclusion theorem does not apply directly to `IStage.X Y`. -/
def interiorStage (Y : ℝ) : TopologicalSpace.Opens GammaTwoQuotient :=
  ⟨interior (QYM.FullCertification.P2IntrinsicTruncatedQuotientExtension.XSet Y), isOpen_interior⟩

/-- Monotonicity of the closed stages induces monotonicity of their open
interiors. -/
theorem interiorStage_mono {Y Z : ℝ} (hYZ : Y ≤ Z) :
    interiorStage Y ≤ interiorStage Z :=
  interior_mono (QYM.FullCertification.P2IntrinsicTruncatedQuotientExtension.XSet_monotone hYZ)

/-- The canonical open-stage inclusion. -/
def interiorStageInclusion {Y Z : ℝ} (hYZ : Y ≤ Z) :
    interiorStage Y → interiorStage Z :=
  TopologicalSpace.Opens.inclusion (interiorStage_mono hYZ)

/-- Under the exact atlas-transition residual, every open-stage inclusion is
smooth. -/
theorem interiorStageInclusion_contMDiff
    {Y Z : ℝ} (hYZ : Y ≤ Z) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ (interiorStageInclusion hYZ) := by
  letI : HasGroupoid GammaTwoQuotient upperHalfPlaneSmoothGroupoid :=
    conditionalHasGroupoidH hSmooth
  letI : HasGroupoid GammaTwoQuotient (contDiffGroupoid ∞ 𝓘(ℂ)) :=
    conditionalHasGroupoidComplex hSmooth
  letI : IsManifold 𝓘(ℂ) ∞ GammaTwoQuotient :=
    conditionalIsManifold hSmooth
  exact contMDiff_inclusion (interiorStage_mono hYZ)

end ConditionalSmoothAtlas
'''
ATLAS_RE = re.compile(r"(?ms)^section ConditionalSmoothAtlas\b.*?^end ConditionalSmoothAtlas\s*")

FIBRE_NEW = r'''@[simp] theorem inverseEtaFibreOfCoordinate_coordinate
    (x : InverseEtaBase) (u : InverseEtaFibre x) :
    inverseEtaFibreOfCoordinate x (inverseEtaFibreCoordinate u) = u := by
  apply Subtype.ext
  simpa [inverseEtaFibreOfCoordinate, inverseEtaFibreCoordinate, u.2] using
    totalOfBaseScalar_projection_coordinate u.1
'''
FIBRE_RE = re.compile(r"(?ms)^@\[simp\] theorem inverseEtaFibreOfCoordinate_coordinate\b.*?(?=^/-- Every actual quotient fibre is canonically equivalent)")
TOPO_MARKER = "/-- The fibre coordinate is continuous for the actual quotient-subspace\ntopology. -/\n"
TOPO_INSERT = r'''/-- Re-expose the actual fibre as the subtype of the quotient total space carrying
its inherited quotient-subspace topology. -/
noncomputable instance inverseEtaFibreTopologicalSpace (x : InverseEtaBase) :
    TopologicalSpace (InverseEtaFibre x) := by
  change TopologicalSpace
    {u : InverseEtaTotal // inverseEtaProjection u = x}
  infer_instance

'''

GATE_MARKERS = {
  "first3": "/-! ## 2. The actual geometric normal and its three unconditional laws -/",
  "first6": "/-! ## 6. The remaining cusp-collar datum -/",
  "first13": "/-- Transport the additive complex-line structure to the actual quotient\nfibre along the proved coordinate equivalence. -/",
}

def git_blob(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()

def audit(text: str):
    return {
      "sorry": len(re.findall(r"\bsorry\b", text)),
      "admit": len(re.findall(r"\badmit\b", text)),
      "native_decide": len(re.findall(r"\bnative_decide\b", text)),
      "Lean.ofReduceBool": text.count("Lean.ofReduceBool"),
      "global_axiom": len(re.findall(r"(?m)^\s*axiom\s+", text)),
      "unsafe": len(re.findall(r"(?m)^\s*unsafe\s+", text)),
      "maxHeartbeats_zero": len(re.findall(r"set_option\s+maxHeartbeats\s+0\b", text)),
    }

def replace_exact(text, old, new, label):
    if text.count(old) != 1:
        raise SystemExit(f"{label}: expected one exact match, got {text.count(old)}")
    return text.replace(old, new, 1)

def main():
    if len(sys.argv) != 3 or sys.argv[1] not in VARIANTS:
        raise SystemExit("usage: qym_gb79_v11_patch.py {first3|first6|first13} QYM.lean")
    variant, filename = sys.argv[1], Path(sys.argv[2])
    before = filename.read_bytes()
    if hashlib.sha256(before).hexdigest() != BASE_SHA256 or git_blob(before) != BASE_BLOB:
        raise SystemExit("unexpected GB79 input identity")
    text = before.decode("utf-8")
    before_audit = audit(text)
    text = replace_exact(text, NAMESPACE_ANCHOR, NAMESPACE_REPLACEMENT, "explicit-edge namespace")
    text = replace_exact(text, OLD_EDGE, NEW_EDGE, "edgeParameterTransport")
    text = replace_exact(text, OLD_C8, NEW_C8, "realMultiple normal")
    text = replace_exact(text, OLD_C9, NEW_C9, "imaginary normal")
    level = VARIANTS[variant]
    if level >= 2:
        if len(list(ATLAS_RE.finditer(text))) != 1:
            raise SystemExit("atlas block mismatch")
        text = ATLAS_RE.sub(ATLAS_BLOCK + "\n", text, count=1)
    if level >= 3:
        if len(list(FIBRE_RE.finditer(text))) != 1:
            raise SystemExit("fibre reconstruction mismatch")
        text = FIBRE_RE.sub(FIBRE_NEW + "\n", text, count=1)
        if text.count(TOPO_MARKER) != 1:
            raise SystemExit("fibre topology marker mismatch")
        text = text.replace(TOPO_MARKER, TOPO_INSERT + TOPO_MARKER, 1)
    after_audit = audit(text)
    if after_audit != before_audit:
        raise SystemExit(f"forbidden-token delta: {before_audit} -> {after_audit}")
    marker = GATE_MARKERS[variant]
    if marker not in text:
        raise SystemExit("gate marker missing")
    filename.write_text(text, encoding="utf-8")
    out = filename.read_bytes()
    print(json.dumps({
      "schema": "qym-gb79-v11-patch-v1",
      "variant": variant,
      "input_sha256": BASE_SHA256,
      "input_blob": BASE_BLOB,
      "candidate_sha256": hashlib.sha256(out).hexdigest(),
      "candidate_blob": git_blob(out),
      "gate_line": text.count("\n", 0, text.index(marker)) + 1,
      "forbidden": after_audit,
      "bytes": len(out),
      "lf": out.count(b"\n"),
    }, indent=2, sort_keys=True))

if __name__ == "__main__":
    main()
