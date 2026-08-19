#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import hashlib
import json
import re
import sys

SECTION_RE = re.compile(
    r"(?ms)^section ConditionalSmoothAtlas\n.*?^end ConditionalSmoothAtlas\n"
)

COMMON_HEADER = '''section ConditionalSmoothAtlas

local instance conditionalChartedSpaceH :
    ChartedSpace ℍ GammaTwoQuotient :=
  allCoveringSheetsChartedSpaceH

/-- Compose the all-sheets atlas with the standard complex atlas on `ℍ`. -/
local instance conditionalChartedSpaceComplex :
    ChartedSpace ℂ GammaTwoQuotient :=
  ChartedSpace.comp ℂ ℍ GammaTwoQuotient
'''

COMMON_INTERIORS = '''
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

COMPLEX_PROOF = '''  apply StructureGroupoid.HasGroupoid.comp upperHalfPlaneSmoothGroupoid
  intro e he
  rw [isLocalStructomorphOn_contDiffGroupoid_iff]
  change
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ e e.source ∧
      ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ e.symm e.target at he
  exact he
'''

EXPLICIT_HELPERS = COMMON_HEADER + '''
/-- The residual supplies the intermediate smooth-groupoid compatibility.
This is an ordinary theorem rather than a parameterized local instance,
because its proof argument is absent from the instance result type. -/
private theorem conditionalHasGroupoidH
    (hSmooth : SmoothTransitionResidual) :
    HasGroupoid GammaTwoQuotient upperHalfPlaneSmoothGroupoid :=
  allCoveringSheets_hasGroupoid hSmooth

/-- Groupoid composition supplies ordinary complex smooth compatibility. -/
private theorem conditionalHasGroupoidComplex
    (hSmooth : SmoothTransitionResidual) :
    HasGroupoid GammaTwoQuotient (contDiffGroupoid ∞ 𝓘(ℂ)) := by
  letI : HasGroupoid GammaTwoQuotient upperHalfPlaneSmoothGroupoid :=
    conditionalHasGroupoidH hSmooth
''' + COMPLEX_PROOF + '''
/-- Conditional construction of the genuine smooth quotient manifold. -/
theorem gammaTwoQuotient_isManifold_of_smoothTransitionResidual
    (hSmooth : SmoothTransitionResidual) :
    IsManifold 𝓘(ℂ) ∞ GammaTwoQuotient := by
  letI : HasGroupoid GammaTwoQuotient (contDiffGroupoid ∞ 𝓘(ℂ)) :=
    conditionalHasGroupoidComplex hSmooth
  exact IsManifold.mk' 𝓘(ℂ) ∞ GammaTwoQuotient
''' + COMMON_INTERIORS + '''
/-- Under the exact atlas-transition residual, every open-stage inclusion is
smooth. -/
theorem interiorStageInclusion_contMDiff
    (hSmooth : SmoothTransitionResidual) {Y Z : ℝ} (hYZ : Y ≤ Z) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ (interiorStageInclusion hYZ) := by
  letI : HasGroupoid GammaTwoQuotient (contDiffGroupoid ∞ 𝓘(ℂ)) :=
    conditionalHasGroupoidComplex hSmooth
  letI : IsManifold 𝓘(ℂ) ∞ GammaTwoQuotient :=
    gammaTwoQuotient_isManifold_of_smoothTransitionResidual hSmooth
  exact contMDiff_inclusion (interiorStage_mono hYZ)

end ConditionalSmoothAtlas
'''

FACT_BRIDGE = COMMON_HEADER + '''
/-- A typeclass-safe bridge: the residual enters through `Fact`, so every
instance argument is inferable from another instance argument. -/
private theorem conditionalHasGroupoidComplex_of_fact
    [hSmooth : Fact SmoothTransitionResidual] :
    HasGroupoid GammaTwoQuotient (contDiffGroupoid ∞ 𝓘(ℂ)) := by
  letI : HasGroupoid GammaTwoQuotient upperHalfPlaneSmoothGroupoid :=
    allCoveringSheets_hasGroupoid hSmooth.out
''' + COMPLEX_PROOF + '''
/-- Conditional construction of the genuine smooth quotient manifold. -/
theorem gammaTwoQuotient_isManifold_of_smoothTransitionResidual
    (hSmooth : SmoothTransitionResidual) :
    IsManifold 𝓘(ℂ) ∞ GammaTwoQuotient := by
  letI : Fact SmoothTransitionResidual := ⟨hSmooth⟩
  letI : HasGroupoid GammaTwoQuotient (contDiffGroupoid ∞ 𝓘(ℂ)) :=
    conditionalHasGroupoidComplex_of_fact
  exact IsManifold.mk' 𝓘(ℂ) ∞ GammaTwoQuotient
''' + COMMON_INTERIORS + '''
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

INLINE_DUPLICATE = COMMON_HEADER + '''
/-- Conditional construction of the genuine smooth quotient manifold. -/
theorem gammaTwoQuotient_isManifold_of_smoothTransitionResidual
    (hSmooth : SmoothTransitionResidual) :
    IsManifold 𝓘(ℂ) ∞ GammaTwoQuotient := by
  letI : HasGroupoid GammaTwoQuotient upperHalfPlaneSmoothGroupoid :=
    allCoveringSheets_hasGroupoid hSmooth
  letI : HasGroupoid GammaTwoQuotient (contDiffGroupoid ∞ 𝓘(ℂ)) := by
''' + ''.join('  ' + line if line.strip() else line for line in COMPLEX_PROOF.splitlines(True)) + '''  exact IsManifold.mk' 𝓘(ℂ) ∞ GammaTwoQuotient
''' + COMMON_INTERIORS + '''
/-- Under the exact atlas-transition residual, every open-stage inclusion is
smooth. -/
theorem interiorStageInclusion_contMDiff
    (hSmooth : SmoothTransitionResidual) {Y Z : ℝ} (hYZ : Y ≤ Z) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ (interiorStageInclusion hYZ) := by
  letI : HasGroupoid GammaTwoQuotient upperHalfPlaneSmoothGroupoid :=
    allCoveringSheets_hasGroupoid hSmooth
  letI : HasGroupoid GammaTwoQuotient (contDiffGroupoid ∞ 𝓘(ℂ)) := by
''' + ''.join('  ' + line if line.strip() else line for line in COMPLEX_PROOF.splitlines(True)) + '''  letI : IsManifold 𝓘(ℂ) ∞ GammaTwoQuotient :=
    IsManifold.mk' 𝓘(ℂ) ∞ GammaTwoQuotient
  exact contMDiff_inclusion (interiorStage_mono hYZ)

end ConditionalSmoothAtlas
'''

VARIANTS = {
    "explicit_helpers": EXPLICIT_HELPERS,
    "fact_bridge": FACT_BRIDGE,
    "inline_duplicate": INLINE_DUPLICATE,
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
    if len(sys.argv) != 7 or sys.argv[1] not in VARIANTS:
        raise SystemExit(
            "usage: qym_patch_dynamic_v16_groupoid.py VARIANT INPUT OUTPUT EXPECTED_SHA EXPECTED_BLOB BASE_ERRORS"
        )
    variant = sys.argv[1]
    source_path = Path(sys.argv[2])
    output_path = Path(sys.argv[3])
    expected_sha = sys.argv[4]
    expected_blob = sys.argv[5]
    base_errors = int(sys.argv[6])
    before = source_path.read_bytes()
    if sha256(before) != expected_sha or git_blob(before) != expected_blob:
        raise SystemExit(
            f"authority mismatch sha={sha256(before)} blob={git_blob(before)}"
        )
    text = before.decode("utf-8")
    matches = list(SECTION_RE.finditer(text))
    if len(matches) != 1:
        raise SystemExit(f"ConditionalSmoothAtlas matches={len(matches)}")
    before_audit = audit(text)
    match = matches[0]
    replacement = VARIANTS[variant]
    patched = text[:match.start()] + replacement + text[match.end():]
    after_audit = audit(patched)
    if after_audit != before_audit or any(after_audit.values()):
        raise SystemExit(f"forbidden-token delta {before_audit} -> {after_audit}")
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(patched, encoding="utf-8")
    after = output_path.read_bytes()
    start_line = patched.count("\n", 0, match.start()) + 1
    end_index = match.start() + len(replacement)
    end_line = patched.count("\n", 0, end_index) + 1
    print(json.dumps({
        "schema": "qym-dynamic-v16-groupoid-patch-v1",
        "variant": variant,
        "baseline_error_headers": base_errors,
        "input_sha256": expected_sha,
        "input_blob": expected_blob,
        "candidate_sha256": sha256(after),
        "candidate_blob": git_blob(after),
        "section_start_line": start_line,
        "section_end_line": end_line,
        "forbidden": after_audit,
        "bytes": len(after),
        "lf": after.count(b"\n"),
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
