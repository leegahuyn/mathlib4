#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import hashlib
import json
import re
import sys

PARENT_SHA = "fada22264b6618467f89d436ddacff27453db1242769717d5e7a386682d4efb3"
PARENT_BLOB = "29d446743036dccd5d9ad8757c351b39d526cfa9"
SECTION_RE = re.compile(r"(?ms)^section ConditionalSmoothAtlas\n.*?^end ConditionalSmoothAtlas\n")

HEADER = '''section ConditionalSmoothAtlas

variable (hSmooth : SmoothTransitionResidual)

local instance conditionalChartedSpaceH :
    ChartedSpace ℍ GammaTwoQuotient :=
  allCoveringSheetsChartedSpaceH

/-- Compose the all-sheets atlas with the standard complex atlas on `ℍ`. -/
local instance conditionalChartedSpaceComplex :
    ChartedSpace ℂ GammaTwoQuotient :=
  ChartedSpace.comp ℂ ℍ GammaTwoQuotient
'''

INTERIORS = '''
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

EXPLICIT_HELPERS = HEADER + '''
/-- The analytic residual is passed explicitly rather than hidden in a
parameterized local instance, whose argument typeclass synthesis cannot infer. -/
private theorem conditionalHasGroupoidH
    (h : SmoothTransitionResidual) :
    HasGroupoid GammaTwoQuotient upperHalfPlaneSmoothGroupoid :=
  allCoveringSheets_hasGroupoid h

/-- Groupoid composition supplies ordinary complex smooth compatibility. -/
private theorem conditionalHasGroupoidComplex
    (h : SmoothTransitionResidual) :
    HasGroupoid GammaTwoQuotient (contDiffGroupoid ∞ 𝓘(ℂ)) := by
  letI : HasGroupoid GammaTwoQuotient upperHalfPlaneSmoothGroupoid :=
    conditionalHasGroupoidH h
''' + COMPLEX_PROOF + '''
/-- Conditional construction of the genuine smooth quotient manifold.  The
only hypothesis is `SmoothTransitionResidual`; no additional topological or
atlas premise is hidden in this theorem. -/
theorem gammaTwoQuotient_isManifold_of_smoothTransitionResidual :
    IsManifold 𝓘(ℂ) ∞ GammaTwoQuotient := by
  letI : HasGroupoid GammaTwoQuotient (contDiffGroupoid ∞ 𝓘(ℂ)) :=
    conditionalHasGroupoidComplex hSmooth
  exact IsManifold.mk' 𝓘(ℂ) ∞ GammaTwoQuotient

private theorem conditionalIsManifold
    (h : SmoothTransitionResidual) :
    IsManifold 𝓘(ℂ) ∞ GammaTwoQuotient :=
  gammaTwoQuotient_isManifold_of_smoothTransitionResidual h
''' + INTERIORS + '''
/-- Under the exact atlas-transition residual, every open-stage inclusion is
smooth. -/
theorem interiorStageInclusion_contMDiff
    {Y Z : ℝ} (hYZ : Y ≤ Z) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ (interiorStageInclusion hYZ) := by
  letI : HasGroupoid GammaTwoQuotient (contDiffGroupoid ∞ 𝓘(ℂ)) :=
    conditionalHasGroupoidComplex hSmooth
  letI : IsManifold 𝓘(ℂ) ∞ GammaTwoQuotient :=
    conditionalIsManifold hSmooth
  exact contMDiff_inclusion (interiorStage_mono hYZ)

end ConditionalSmoothAtlas
'''

FACT_BRIDGE = HEADER + '''
/-- A typeclass-safe bridge: the residual is carried by `Fact`, so every
instance argument is inferable from an instance argument. -/
private theorem conditionalHasGroupoidComplex_of_fact
    [h : Fact SmoothTransitionResidual] :
    HasGroupoid GammaTwoQuotient (contDiffGroupoid ∞ 𝓘(ℂ)) := by
  letI : HasGroupoid GammaTwoQuotient upperHalfPlaneSmoothGroupoid :=
    allCoveringSheets_hasGroupoid h.out
''' + COMPLEX_PROOF + '''
/-- Conditional construction of the genuine smooth quotient manifold.  The
only hypothesis is `SmoothTransitionResidual`; no additional topological or
atlas premise is hidden in this theorem. -/
theorem gammaTwoQuotient_isManifold_of_smoothTransitionResidual :
    IsManifold 𝓘(ℂ) ∞ GammaTwoQuotient := by
  letI : Fact SmoothTransitionResidual := ⟨hSmooth⟩
  letI : HasGroupoid GammaTwoQuotient (contDiffGroupoid ∞ 𝓘(ℂ)) :=
    conditionalHasGroupoidComplex_of_fact
  exact IsManifold.mk' 𝓘(ℂ) ∞ GammaTwoQuotient
''' + INTERIORS + '''
/-- Under the exact atlas-transition residual, every open-stage inclusion is
smooth. -/
theorem interiorStageInclusion_contMDiff
    {Y Z : ℝ} (hYZ : Y ≤ Z) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ (interiorStageInclusion hYZ) := by
  letI : Fact SmoothTransitionResidual := ⟨hSmooth⟩
  letI : HasGroupoid GammaTwoQuotient (contDiffGroupoid ∞ 𝓘(ℂ)) :=
    conditionalHasGroupoidComplex_of_fact
  letI : IsManifold 𝓘(ℂ) ∞ GammaTwoQuotient :=
    gammaTwoQuotient_isManifold_of_smoothTransitionResidual hSmooth
  exact contMDiff_inclusion (interiorStage_mono hYZ)

end ConditionalSmoothAtlas
'''

INDENTED_COMPLEX_PROOF = ''.join(
    ('  ' + line if line.strip() else line)
    for line in COMPLEX_PROOF.splitlines(True)
)
INLINE_DUPLICATE = HEADER + '''
/-- Conditional construction of the genuine smooth quotient manifold.  The
only hypothesis is `SmoothTransitionResidual`; no additional topological or
atlas premise is hidden in this theorem. -/
theorem gammaTwoQuotient_isManifold_of_smoothTransitionResidual :
    IsManifold 𝓘(ℂ) ∞ GammaTwoQuotient := by
  letI : HasGroupoid GammaTwoQuotient upperHalfPlaneSmoothGroupoid :=
    allCoveringSheets_hasGroupoid hSmooth
  letI : HasGroupoid GammaTwoQuotient (contDiffGroupoid ∞ 𝓘(ℂ)) := by
''' + INDENTED_COMPLEX_PROOF + '''  exact IsManifold.mk' 𝓘(ℂ) ∞ GammaTwoQuotient
''' + INTERIORS + '''
/-- Under the exact atlas-transition residual, every open-stage inclusion is
smooth. -/
theorem interiorStageInclusion_contMDiff
    {Y Z : ℝ} (hYZ : Y ≤ Z) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ (interiorStageInclusion hYZ) := by
  letI : HasGroupoid GammaTwoQuotient upperHalfPlaneSmoothGroupoid :=
    allCoveringSheets_hasGroupoid hSmooth
  letI : HasGroupoid GammaTwoQuotient (contDiffGroupoid ∞ 𝓘(ℂ)) := by
''' + INDENTED_COMPLEX_PROOF + '''  letI : IsManifold 𝓘(ℂ) ∞ GammaTwoQuotient :=
    IsManifold.mk' 𝓘(ℂ) ∞ GammaTwoQuotient
  exact contMDiff_inclusion (interiorStage_mono hYZ)

end ConditionalSmoothAtlas
'''

VARIANTS = {
    "explicit_helpers": EXPLICIT_HELPERS,
    "fact_bridge": FACT_BRIDGE,
    "inline_duplicate": INLINE_DUPLICATE,
}


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
    source_path = Path(sys.argv[2])
    output_path = Path(sys.argv[3])
    before = source_path.read_bytes()
    if sha(before) != PARENT_SHA or blob(before) != PARENT_BLOB:
        raise SystemExit(
            f"verified GB77-descendant mismatch sha={sha(before)} blob={blob(before)}"
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
    end_line = patched.count("\n", 0, match.start() + len(replacement)) + 1
    print(json.dumps({
        "schema": "qym-gb77-fixedorigin-v16-groupoid-patch-v1",
        "variant": variant,
        "fixed_origin_errors": 77,
        "fixed_origin_sha256": "b6f0126c27dfc08b5f81c306a7140f9531fcc3d6ca6b75dd8abbd71101d458fd",
        "fixed_origin_blob": "c6e8883353b350f22b7f48d955fc5cfa4e61f88f",
        "verified_parent_errors": 76,
        "input_sha256": PARENT_SHA,
        "input_blob": PARENT_BLOB,
        "candidate_sha256": sha(after),
        "candidate_blob": blob(after),
        "section_start_line": start_line,
        "section_end_line": end_line,
        "forbidden": after_audit,
        "bytes": len(after),
        "lf": after.count(b"\n"),
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
