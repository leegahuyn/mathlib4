#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import hashlib
import json
import re
import sys

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

C12 = r'''@[simp] theorem inverseEtaFibreOfCoordinate_coordinate
    (x : InverseEtaBase) (u : InverseEtaFibre x) :
    inverseEtaFibreOfCoordinate x (inverseEtaFibreCoordinate u) = u := by
  apply Subtype.ext
  simpa [inverseEtaFibreOfCoordinate, inverseEtaFibreCoordinate, u.2] using
    totalOfBaseScalar_projection_coordinate u.1
'''

C13_INSERT = r'''/-- Re-expose the actual fibre as the subtype of the quotient total space carrying
its inherited quotient-subspace topology. -/
noncomputable instance inverseEtaFibreTopologicalSpace (x : InverseEtaBase) :
    TopologicalSpace (InverseEtaFibre x) := by
  change TopologicalSpace
    {u : InverseEtaTotal // inverseEtaProjection u = x}
  infer_instance

'''

ATLAS_RE = re.compile(
    r"(?ms)^section ConditionalSmoothAtlas\b.*?^end ConditionalSmoothAtlas\s*"
)
C12_RE = re.compile(
    r"(?ms)^@\[simp\] theorem inverseEtaFibreOfCoordinate_coordinate\b.*?"
    r"(?=^/-- Every actual quotient fibre is canonically equivalent)"
)
C13_MARKER = "/-- The fibre coordinate is continuous for the actual quotient-subspace\ntopology. -/\n"


def git_blob(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def replace_one(text: str, pattern: re.Pattern[str], replacement: str, label: str) -> str:
    matches = list(pattern.finditer(text))
    if len(matches) != 1:
        raise SystemExit(f"{label}: expected one match, found {len(matches)}")
    match = matches[0]
    return text[:match.start()] + replacement + "\n" + text[match.end():]


def main() -> None:
    if len(sys.argv) != 2:
        raise SystemExit("usage: qym_patch_c10_c13.py QYM.lean")
    path = Path(sys.argv[1])
    before = path.read_bytes()
    text = before.decode("utf-8")
    text = replace_one(text, ATLAS_RE, ATLAS_BLOCK, "c10-c11 atlas block")
    text = replace_one(text, C12_RE, C12, "c12 fibre reconstruction")
    if text.count(C13_MARKER) != 1:
        raise SystemExit(f"c13 marker count: {text.count(C13_MARKER)}")
    text = text.replace(C13_MARKER, C13_INSERT + C13_MARKER, 1)
    path.write_text(text, encoding="utf-8")

    after = path.read_bytes()
    decoded = after.decode("utf-8")
    forbidden = {
        "sorry": len(re.findall(r"\bsorry\b", decoded)),
        "admit": len(re.findall(r"\badmit\b", decoded)),
        "native_decide": len(re.findall(r"\bnative_decide\b", decoded)),
        "Lean.ofReduceBool": decoded.count("Lean.ofReduceBool"),
        "global_axiom": len(re.findall(r"(?m)^\s*axiom\s+", decoded)),
        "unsafe": len(re.findall(r"(?m)^\s*unsafe\s+", decoded)),
        "maxHeartbeats_zero": len(re.findall(r"set_option\s+maxHeartbeats\s+0\b", decoded)),
    }
    if any(forbidden.values()):
        raise SystemExit(f"forbidden token audit failed: {forbidden}")
    marker = "/-- Reconstruction of one fixed fibre is continuous. -/"
    gate_line = decoded.count("\n", 0, decoded.index(marker)) + 1
    print(json.dumps({
        "schema": "qym-c10-c13-v1",
        "input_sha256": hashlib.sha256(before).hexdigest(),
        "input_blob": git_blob(before),
        "candidate_sha256": hashlib.sha256(after).hexdigest(),
        "candidate_blob": git_blob(after),
        "bytes": len(after),
        "lf": after.count(b"\n"),
        "gate_line": gate_line,
        "forbidden": forbidden,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
