#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import hashlib
import json
import re
import sys

VARIANTS = {
    "baseline",
    "gamma_decide",
    "gamma_entry_norm",
    "groupoid_explicit",
    "combined_decide_groupoid",
}

HEADER = """theorem gammaTwo_matrix_eq_one_or_neg_one_of_mem_fd_fixed
    {gamma : SL(2, ℤ)} {z : ℍ}
    (hGamma : gamma ∈ CongruenceSubgroup.Gamma 2)
    (hz : z ∈ ModularGroup.fd)
    (hfix : gamma • z = z) :
    gamma = 1 ∨ gamma = -1 := by
"""

CLASSIFY = """  rcases ModularGroup.cases_of_mem_fd_smul_mem_fd hz (hfix ▸ hz) with
    hcentral | hT | hTinv | hS | hTS | hTinvSTinv |
      hSTinv | hST | hTST | hTinvS
  · exact hcentral
"""

GAMMA_DECIDE = "set_option maxRecDepth 10000 in\nset_option maxHeartbeats 6000000 in\n" + HEADER + CLASSIFY + """  all_goals
    rcases ‹(_ ∨ _) ∧ _› with ⟨hMatrix, _⟩
    rcases hMatrix with rfl | rfl
    all_goals
      exfalso
      exact (by decide) hGamma
"""

GAMMA_ENTRY = "set_option maxHeartbeats 6000000 in\n" + HEADER + """  have h01 : ((gamma 0 1 : ℤ) : ZMod 2) = 0 :=
    (CongruenceSubgroup.Gamma_mem.mp hGamma).2.1
  have h10 : ((gamma 1 0 : ℤ) : ZMod 2) = 0 :=
    (CongruenceSubgroup.Gamma_mem.mp hGamma).2.2.1
""" + CLASSIFY + """  all_goals
    rcases ‹(_ ∨ _) ∧ _› with ⟨hMatrix, _⟩
    rcases hMatrix with rfl | rfl
    all_goals
      norm_num [ModularGroup.S, ModularGroup.T, ModularGroup.coe_T_zpow,
        Matrix.mul_apply, Fin.sum_univ_two, SL2_inv_expl] at h01 h10
"""

DECL_RE = re.compile(
    r"(?ms)^(?:set_option[^\n]+ in\n)*theorem gammaTwo_matrix_eq_one_or_neg_one_of_mem_fd_fixed\b.*?"
    r"(?=^/--|^theorem\s|^lemma\s|^noncomputable\s+def\s|^def\s|^section\s|^end\s)"
)

GROUP_REPLACEMENTS = [
("""local instance conditionalHasGroupoidH :
    HasGroupoid GammaTwoQuotient upperHalfPlaneSmoothGroupoid :=
  allCoveringSheets_hasGroupoid hSmooth
""",
"""private theorem conditionalHasGroupoidH
    (h : SmoothTransitionResidual) :
    HasGroupoid GammaTwoQuotient upperHalfPlaneSmoothGroupoid :=
  allCoveringSheets_hasGroupoid h
"""),
("""/-- Groupoid composition turns the single transition residual into the usual
complex smooth-atlas compatibility condition. -/
local instance conditionalHasGroupoidComplex :
    HasGroupoid GammaTwoQuotient (contDiffGroupoid ∞ 𝓘(ℂ)) := by
  apply StructureGroupoid.HasGroupoid.comp upperHalfPlaneSmoothGroupoid
  intro e he
  rw [isLocalStructomorphOn_contDiffGroupoid_iff]
  change
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ e e.source ∧
      ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ e.symm e.target at he
  exact he
""",
"""/-- Groupoid composition turns the single transition residual into the usual
complex smooth-atlas compatibility condition. -/
private theorem conditionalHasGroupoidComplex
    (h : SmoothTransitionResidual) :
    HasGroupoid GammaTwoQuotient (contDiffGroupoid ∞ 𝓘(ℂ)) := by
  letI : HasGroupoid GammaTwoQuotient upperHalfPlaneSmoothGroupoid :=
    conditionalHasGroupoidH h
  apply StructureGroupoid.HasGroupoid.comp upperHalfPlaneSmoothGroupoid
  intro e he
  rw [isLocalStructomorphOn_contDiffGroupoid_iff]
  change
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ e e.source ∧
      ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ e.symm e.target at he
  exact he
"""),
("""theorem gammaTwoQuotient_isManifold_of_smoothTransitionResidual :
    IsManifold 𝓘(ℂ) ∞ GammaTwoQuotient :=
  IsManifold.mk' 𝓘(ℂ) ∞ GammaTwoQuotient

local instance conditionalIsManifold :
    IsManifold 𝓘(ℂ) ∞ GammaTwoQuotient :=
  gammaTwoQuotient_isManifold_of_smoothTransitionResidual
""",
"""theorem gammaTwoQuotient_isManifold_of_smoothTransitionResidual :
    IsManifold 𝓘(ℂ) ∞ GammaTwoQuotient := by
  letI : HasGroupoid GammaTwoQuotient (contDiffGroupoid ∞ 𝓘(ℂ)) :=
    conditionalHasGroupoidComplex hSmooth
  exact IsManifold.mk' 𝓘(ℂ) ∞ GammaTwoQuotient

private theorem conditionalIsManifold
    (h : SmoothTransitionResidual) :
    IsManifold 𝓘(ℂ) ∞ GammaTwoQuotient :=
  gammaTwoQuotient_isManifold_of_smoothTransitionResidual h
"""),
("""theorem interiorStageInclusion_contMDiff
    {Y Z : ℝ} (hYZ : Y ≤ Z) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ (interiorStageInclusion hYZ) :=
  contMDiff_inclusion (interiorStage_mono hYZ)
""",
"""theorem interiorStageInclusion_contMDiff
    {Y Z : ℝ} (hYZ : Y ≤ Z) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ (interiorStageInclusion hYZ) := by
  letI : HasGroupoid GammaTwoQuotient (contDiffGroupoid ∞ 𝓘(ℂ)) :=
    conditionalHasGroupoidComplex hSmooth
  letI : IsManifold 𝓘(ℂ) ∞ GammaTwoQuotient :=
    conditionalIsManifold hSmooth
  exact contMDiff_inclusion (interiorStage_mono hYZ)
""")]


def git_blob(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def replace_gamma(text: str, proof: str) -> tuple[str, bool]:
    matches = list(DECL_RE.finditer(text))
    if len(matches) != 1:
        return text, False
    m = matches[0]
    return text[:m.start()] + proof + "\n" + text[m.end():], True


def replace_groupoid(text: str) -> tuple[str, int]:
    applied = 0
    for old, new in GROUP_REPLACEMENTS:
        if text.count(old) == 1:
            text = text.replace(old, new, 1)
            applied += 1
    return text, applied


def main() -> None:
    if len(sys.argv) != 3:
        raise SystemExit("usage: qym_probe42_adaptive.py VARIANT QYM.lean")
    variant, filename = sys.argv[1], sys.argv[2]
    if variant not in VARIANTS:
        raise SystemExit(f"unknown variant: {variant}")

    path = Path(filename)
    before = path.read_bytes()
    text = before.decode("utf-8")
    applied: list[str] = []

    if variant in {"gamma_decide", "combined_decide_groupoid"}:
        text, ok = replace_gamma(text, GAMMA_DECIDE)
        if ok:
            applied.append("gamma_decide")
    elif variant == "gamma_entry_norm":
        text, ok = replace_gamma(text, GAMMA_ENTRY)
        if ok:
            applied.append("gamma_entry_norm")

    if variant in {"groupoid_explicit", "combined_decide_groupoid"}:
        text, count = replace_groupoid(text)
        if count:
            applied.append(f"groupoid_explicit:{count}")

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

    print(json.dumps({
        "schema": "qym-probe42-adaptive-v1",
        "variant": variant,
        "applied": applied,
        "input_sha256": hashlib.sha256(before).hexdigest(),
        "input_blob": git_blob(before),
        "candidate_sha256": hashlib.sha256(after).hexdigest(),
        "candidate_blob": git_blob(after),
        "bytes": len(after),
        "lf": after.count(b"\n"),
        "forbidden": forbidden,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
