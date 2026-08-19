#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import hashlib
import json
import re
import sys

BASE_SHA256 = "b6f0126c27dfc08b5f81c306a7140f9531fcc3d6ca6b75dd8abbd71101d458fd"
BASE_BLOB = "c6e8883353b350f22b7f48d955fc5cfa4e61f88f"

RIGHT_NORMAL_RE = re.compile(
    r"(?ms)^theorem conj_mul_hyperbolicRightNormal_im\b.*?"
    r"(?=^/-! ## 2\. The actual geometric normal)"
)
ATLAS_RE = re.compile(
    r"(?ms)^section ConditionalSmoothAtlas\n.*?^end ConditionalSmoothAtlas\n"
)

RIGHT_NORMAL_FIX = r'''theorem conj_mul_hyperbolicRightNormal_im {y : ℝ} {w : ℂ}
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
  simp [Complex.mul_re, Complex.mul_im]
  rw [Complex.normSq_eq_norm_sq]
  field_simp [hn] <;> ring

'''

COMMON_HEADER = r'''section ConditionalSmoothAtlas

local instance conditionalChartedSpaceH :
    ChartedSpace ℍ GammaTwoQuotient :=
  allCoveringSheetsChartedSpaceH

/-- Compose the all-sheets atlas with the standard complex atlas on `ℍ`. -/
local instance conditionalChartedSpaceComplex :
    ChartedSpace ℂ GammaTwoQuotient :=
  ChartedSpace.comp ℂ ℍ GammaTwoQuotient
'''

GROUP_PROOF_APPLY = r'''  apply StructureGroupoid.HasGroupoid.comp upperHalfPlaneSmoothGroupoid
  intro e he
  rw [isLocalStructomorphOn_contDiffGroupoid_iff]
  change
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ e e.source ∧
      ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ e.symm e.target at he
  exact he
'''

GROUP_PROOF_EXACT = r'''  exact StructureGroupoid.HasGroupoid.comp upperHalfPlaneSmoothGroupoid (by
    intro e he
    rw [isLocalStructomorphOn_contDiffGroupoid_iff]
    change
      ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ e e.source ∧
        ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ e.symm e.target at he
    exact he)
'''

COMMON_INTERIORS = r'''
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
'''


def explicit_helpers(group_proof: str, keyword: str) -> str:
    return COMMON_HEADER + r'''
/-- The residual supplies the intermediate smooth-groupoid compatibility. -/
private theorem conditionalHasGroupoidH
    (hSmooth : SmoothTransitionResidual) :
    HasGroupoid GammaTwoQuotient upperHalfPlaneSmoothGroupoid :=
  allCoveringSheets_hasGroupoid hSmooth

/-- Groupoid composition supplies ordinary complex smooth compatibility. -/
private theorem conditionalHasGroupoidComplex
    (hSmooth : SmoothTransitionResidual) :
    HasGroupoid GammaTwoQuotient (contDiffGroupoid ∞ 𝓘(ℂ)) := by
''' + f'''  {keyword} : HasGroupoid GammaTwoQuotient upperHalfPlaneSmoothGroupoid :=\n    conditionalHasGroupoidH hSmooth\n''' + group_proof + r'''
/-- Conditional construction of the genuine smooth quotient manifold. -/
theorem gammaTwoQuotient_isManifold_of_smoothTransitionResidual
    (hSmooth : SmoothTransitionResidual) :
    IsManifold 𝓘(ℂ) ∞ GammaTwoQuotient := by
''' + f'''  {keyword} : HasGroupoid GammaTwoQuotient (contDiffGroupoid ∞ 𝓘(ℂ)) :=\n    conditionalHasGroupoidComplex hSmooth\n''' + r'''  exact IsManifold.mk' 𝓘(ℂ) ∞ GammaTwoQuotient
''' + COMMON_INTERIORS + r'''
/-- Under the exact atlas-transition residual, every open-stage inclusion is
smooth. -/
theorem interiorStageInclusion_contMDiff
    (hSmooth : SmoothTransitionResidual) {Y Z : ℝ} (hYZ : Y ≤ Z) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ (interiorStageInclusion hYZ) := by
''' + f'''  {keyword} : HasGroupoid GammaTwoQuotient (contDiffGroupoid ∞ 𝓘(ℂ)) :=\n    conditionalHasGroupoidComplex hSmooth\n  {keyword} : IsManifold 𝓘(ℂ) ∞ GammaTwoQuotient :=\n    gammaTwoQuotient_isManifold_of_smoothTransitionResidual hSmooth\n''' + r'''  exact contMDiff_inclusion (interiorStage_mono hYZ)

end ConditionalSmoothAtlas
'''


def fact_bridge(group_proof: str) -> str:
    return COMMON_HEADER + r'''
/-- A typeclass-safe bridge: the residual enters through `Fact`, so every
instance argument is inferable from another instance argument. -/
private theorem conditionalHasGroupoidComplex_of_fact
    [hSmooth : Fact SmoothTransitionResidual] :
    HasGroupoid GammaTwoQuotient (contDiffGroupoid ∞ 𝓘(ℂ)) := by
  letI : HasGroupoid GammaTwoQuotient upperHalfPlaneSmoothGroupoid :=
    allCoveringSheets_hasGroupoid hSmooth.out
''' + group_proof + r'''
/-- Conditional construction of the genuine smooth quotient manifold. -/
theorem gammaTwoQuotient_isManifold_of_smoothTransitionResidual
    (hSmooth : SmoothTransitionResidual) :
    IsManifold 𝓘(ℂ) ∞ GammaTwoQuotient := by
  letI : Fact SmoothTransitionResidual := ⟨hSmooth⟩
  letI : HasGroupoid GammaTwoQuotient (contDiffGroupoid ∞ 𝓘(ℂ)) :=
    conditionalHasGroupoidComplex_of_fact
  exact IsManifold.mk' 𝓘(ℂ) ∞ GammaTwoQuotient
''' + COMMON_INTERIORS + r'''
/-- Under the exact atlas-transition residual, every open-stage inclusion is
smooth. -/
theorem interiorStageInclusion_contMDiff
    (hSmooth : SmoothTransitionResidual) {Y Z : ℝ} (hYZ : Y ≤ Z) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ (interiorStageInclusion hYZ) := by
  letI : Fact SmoothTransitionResidual := ⟨hSmooth⟩
  letI : HasGroupoid GammaTwoQuotient (contDiffGroupoid ∞ 𝓘(ℂ)) :=
    conditionalHasGroupoidComplex_of_fact
  letI : IsManifold 𝓘(ℂ) ∞ GammaTwoQuotient :=
    gammaTwoQuotient_isManifold_of_smoothTransitionResidual hSmooth
  exact contMDiff_inclusion (interiorStage_mono hYZ)

end ConditionalSmoothAtlas
'''


def inline_duplicate(group_proof: str, keyword: str) -> str:
    nested = ''.join(('  ' + line) if line.strip() else line for line in group_proof.splitlines(True))
    return COMMON_HEADER + r'''
/-- Conditional construction of the genuine smooth quotient manifold. -/
theorem gammaTwoQuotient_isManifold_of_smoothTransitionResidual
    (hSmooth : SmoothTransitionResidual) :
    IsManifold 𝓘(ℂ) ∞ GammaTwoQuotient := by
''' + f'''  {keyword} : HasGroupoid GammaTwoQuotient upperHalfPlaneSmoothGroupoid :=\n    allCoveringSheets_hasGroupoid hSmooth\n  {keyword} : HasGroupoid GammaTwoQuotient (contDiffGroupoid ∞ 𝓘(ℂ)) := by\n''' + nested + r'''  exact IsManifold.mk' 𝓘(ℂ) ∞ GammaTwoQuotient
''' + COMMON_INTERIORS + r'''
/-- Under the exact atlas-transition residual, every open-stage inclusion is
smooth. -/
theorem interiorStageInclusion_contMDiff
    (hSmooth : SmoothTransitionResidual) {Y Z : ℝ} (hYZ : Y ≤ Z) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ (interiorStageInclusion hYZ) := by
''' + f'''  {keyword} : HasGroupoid GammaTwoQuotient upperHalfPlaneSmoothGroupoid :=\n    allCoveringSheets_hasGroupoid hSmooth\n  {keyword} : HasGroupoid GammaTwoQuotient (contDiffGroupoid ∞ 𝓘(ℂ)) := by\n''' + nested + f'''  {keyword} : IsManifold 𝓘(ℂ) ∞ GammaTwoQuotient :=\n    IsManifold.mk' 𝓘(ℂ) ∞ GammaTwoQuotient\n''' + r'''  exact contMDiff_inclusion (interiorStage_mono hYZ)

end ConditionalSmoothAtlas
'''

VARIANTS = {
    "helpers_letI_apply": explicit_helpers(GROUP_PROOF_APPLY, "letI"),
    "helpers_haveI_apply": explicit_helpers(GROUP_PROOF_APPLY, "haveI"),
    "helpers_letI_exact": explicit_helpers(GROUP_PROOF_EXACT, "letI"),
    "fact_apply": fact_bridge(GROUP_PROOF_APPLY),
    "inline_letI_apply": inline_duplicate(GROUP_PROOF_APPLY, "letI"),
    "inline_haveI_exact": inline_duplicate(GROUP_PROOF_EXACT, "haveI"),
}


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git_blob(data: bytes) -> str:
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
            f"usage: {Path(sys.argv[0]).name} VARIANT INPUT_GB77 OUTPUT_CANDIDATE"
        )
    variant = sys.argv[1]
    source_path = Path(sys.argv[2])
    output_path = Path(sys.argv[3])
    before = source_path.read_bytes()
    if sha256(before) != BASE_SHA256 or git_blob(before) != BASE_BLOB:
        raise SystemExit(
            f"exact GB77 authority mismatch sha={sha256(before)} blob={git_blob(before)}"
        )
    text = before.decode("utf-8")
    right_matches = list(RIGHT_NORMAL_RE.finditer(text))
    atlas_matches = list(ATLAS_RE.finditer(text))
    if len(right_matches) != 1 or len(atlas_matches) != 1:
        raise SystemExit(
            f"unexpected target counts right={len(right_matches)} atlas={len(atlas_matches)}"
        )
    before_audit = audit(text)
    text, right_count = RIGHT_NORMAL_RE.subn(RIGHT_NORMAL_FIX, text, count=1)
    text, atlas_count = ATLAS_RE.subn(VARIANTS[variant].rstrip() + "\n", text, count=1)
    if right_count != 1 or atlas_count != 1:
        raise SystemExit(f"replacement counts right={right_count} atlas={atlas_count}")
    after_audit = audit(text)
    if after_audit != before_audit or any(after_audit.values()):
        raise SystemExit(f"forbidden-token delta: {before_audit} -> {after_audit}")
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(text, encoding="utf-8")
    after = output_path.read_bytes()
    right_start = text.index("theorem conj_mul_hyperbolicRightNormal_im")
    atlas_start = text.index("section ConditionalSmoothAtlas")
    atlas_end = text.index("end ConditionalSmoothAtlas", atlas_start) + len("end ConditionalSmoothAtlas")
    print(json.dumps({
        "schema": "qym-fixed-gb77-v16-patch-v1",
        "status": "PREPARED_UNVERIFIED",
        "variant": variant,
        "fixed_baseline": "GB77",
        "baseline_error_headers": 77,
        "input_sha256": BASE_SHA256,
        "input_blob": BASE_BLOB,
        "candidate_sha256": sha256(after),
        "candidate_blob": git_blob(after),
        "right_normal_start_line": text.count("\n", 0, right_start) + 1,
        "atlas_start_line": text.count("\n", 0, atlas_start) + 1,
        "atlas_end_line": text.count("\n", 0, atlas_end) + 1,
        "forbidden": after_audit,
        "bytes": len(after),
        "lf": after.count(b"\n"),
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
