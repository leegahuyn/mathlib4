#!/usr/bin/env python3
from __future__ import annotations

from difflib import SequenceMatcher
from pathlib import Path
import hashlib
import importlib.util
import json
import os
import sys

ROOT = Path(os.environ.get("GITHUB_WORKSPACE", Path.cwd())).resolve()
CORE_PATH = ROOT / ".github/qym_repair_c2_c6_serial.py"
RESULT_PATH = ROOT / ".github/qym-frontier/C2_C6_RESULT.json"

if RESULT_PATH.is_file():
    try:
        existing = json.loads(RESULT_PATH.read_text(encoding="utf-8"))
    except Exception:
        existing = {}
    if existing.get("c2_c6_clean") is True and existing.get("strict_improvement") is True:
        print(json.dumps({"already_verified": True, "result": existing}, indent=2, sort_keys=True))
        raise SystemExit(0)

spec = importlib.util.spec_from_file_location("qym_repair_core_v4", CORE_PATH)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot import repair core from {CORE_PATH}")
core = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = core
spec.loader.exec_module(core)

_original_load_artifact = core.load_artifact
_cache = {}


def raw_load(label: str, artifact_id: int):
    key = (label, artifact_id)
    if key not in _cache:
        artifact = _original_load_artifact(label, artifact_id)
        digest = hashlib.sha256(artifact.source.encode("utf-8")).hexdigest()
        artifact.result["candidate_qym_sha256"] = digest
        _cache[key] = artifact
    return _cache[key]


def diff_hunks_with_context(base: str, candidate: str):
    base_lines = base.splitlines(keepends=True)
    candidate_lines = candidate.splitlines(keepends=True)
    matcher = SequenceMatcher(None, base_lines, candidate_lines, autojunk=False)
    changed = [
        (tag, i1, i2, j1, j2)
        for tag, i1, i2, j1, j2 in matcher.get_opcodes()
        if tag != "equal"
    ]
    if not changed:
        raise RuntimeError("candidate has no source change")
    raw_i1 = min(row[1] for row in changed)
    raw_i2 = max(row[2] for row in changed)
    raw_j1 = min(row[3] for row in changed)
    raw_j2 = max(row[4] for row in changed)
    before = min(30, raw_i1, raw_j1)
    after = min(30, len(base_lines) - raw_i2, len(candidate_lines) - raw_j2)
    i1, i2 = raw_i1 - before, raw_i2 + after
    j1, j2 = raw_j1 - before, raw_j2 + after
    if max(i2 - i1, j2 - j1) > 7000:
        raise RuntimeError("candidate repair envelope exceeds 7000 lines")
    return [
        core.Hunk(
            i1=i1,
            i2=i2,
            j1=j1,
            j2=j2,
            old="".join(base_lines[i1:i2]),
            new="".join(candidate_lines[j1:j2]),
        )
    ]


def c2_theorem_change(hx_proof: str) -> str:
    return f'''theorem actualFixedPhaseCuspHorocyclePoint_coe_contDiff
    (kappa : GammaTwoCusp) (Y : ℝ) :
    ContDiff ℝ ∞
      (fun x : ℝ =>
        ((actualFixedPhaseCuspHorocyclePoint kappa Y x : ℍ) : ℂ)) := by
  let g : GL (Fin 2) ℝ :=
    (gammaTwoCuspScaling kappa : GL (Fin 2) ℝ)
  have hg : 0 < g.det.val := by
    simp [g]
  have hx : ContDiff ℝ ∞ (fun x : ℝ => (x : ℂ)) := by
{hx_proof}
  have hz : ContDiff ℝ ∞
      (fun x : ℝ =>
        (x : ℂ) + (actualFixedPhaseCuspHeight Y : ℂ) * Complex.I) := by
    exact hx.add
      (contDiff_const : ContDiff ℝ ∞
        (fun _ : ℝ => (actualFixedPhaseCuspHeight Y : ℂ) * Complex.I))
  have hnum : ContDiff ℝ ∞
      (fun x : ℝ =>
        UpperHalfPlane.num g
          (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ)) := by
    change ContDiff ℝ ∞
      (fun x : ℝ =>
        ((g 0 0 : ℝ) : ℂ) *
            ((x : ℂ) + (actualFixedPhaseCuspHeight Y : ℂ) * Complex.I) +
          ((g 0 1 : ℝ) : ℂ))
    exact
      (((contDiff_const : ContDiff ℝ ∞
          (fun _ : ℝ => ((g 0 0 : ℝ) : ℂ))).mul hz).add
        (contDiff_const : ContDiff ℝ ∞
          (fun _ : ℝ => ((g 0 1 : ℝ) : ℂ))))
  have hdenDiff : ContDiff ℝ ∞
      (fun x : ℝ =>
        UpperHalfPlane.denom g
          (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ)) := by
    change ContDiff ℝ ∞
      (fun x : ℝ =>
        ((g 1 0 : ℝ) : ℂ) *
            ((x : ℂ) + (actualFixedPhaseCuspHeight Y : ℂ) * Complex.I) +
          ((g 1 1 : ℝ) : ℂ))
    exact
      (((contDiff_const : ContDiff ℝ ∞
          (fun _ : ℝ => ((g 1 0 : ℝ) : ℂ))).mul hz).add
        (contDiff_const : ContDiff ℝ ∞
          (fun _ : ℝ => ((g 1 1 : ℝ) : ℂ))))
  have hden : ∀ x : ℝ,
      UpperHalfPlane.denom g
        (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ) ≠ 0 := by
    intro x
    exact UpperHalfPlane.denom_ne_zero g
      (actualFixedPhaseHorizontalHorocyclePoint Y x)
  have hfrac : ContDiff ℝ ∞
      (fun x : ℝ =>
        UpperHalfPlane.num g
            (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ) /
          UpperHalfPlane.denom g
            (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ)) := by
    simpa only [div_eq_mul_inv] using
      hnum.mul (hdenDiff.inv hden)
  change ContDiff ℝ ∞
    (fun x : ℝ =>
      (↑(g • actualFixedPhaseHorizontalHorocyclePoint Y x) : ℂ))
  simpa only [UpperHalfPlane.coe_smul_of_det_pos hg] using hfrac
'''


# Recover and independently recompile the alleged 85-error authority before trusting metadata.
core.OUT.mkdir(parents=True, exist_ok=True)
c04 = raw_load("C04_mul_inv_using_bang", core.ARTIFACTS["C04_mul_inv_using_bang"])
reverified = core.run_lean(c04.source, "C04-authority-independent-full", 10000)
if int(reverified["panic_lines"]) != 0:
    raise RuntimeError("independent C04 authority compile emitted panic/internal-error lines")
if int(reverified["error_headers"]) != 85:
    raise RuntimeError(
        f"independent C04 authority compile expected 85 errors, got {reverified['error_headers']}"
    )
c04.result["error_headers"] = 85
c04.result["candidate_qym_sha256"] = hashlib.sha256(
    c04.source.encode("utf-8")
).hexdigest()

core.load_artifact = raw_load
core.diff_hunks = diff_hunks_with_context
core.C2_VARIANTS.update(
    {
        "v4_change_ofRealCLM_exact": c2_theorem_change(
            "    exact\n"
            "      ((Complex.ofRealCLM : ℝ →L[ℝ] ℂ).contDiff :\n"
            "        ContDiff ℝ ∞ (fun x : ℝ => (x : ℂ)))"
        ),
        "v4_change_ofRealCLM_simpa": c2_theorem_change(
            "    simpa using ((Complex.ofRealCLM : ℝ →L[ℝ] ℂ).contDiff)"
        ),
        "v4_change_split_fun_prop": c2_theorem_change("    fun_prop"),
        "v4_change_ofRealCLM_typed_apply": c2_theorem_change(
            "    simpa only [Complex.ofRealCLM_apply] using\n"
            "      (Complex.ofRealCLM.contDiff :\n"
            "        ContDiff ℝ ∞ (fun x : ℝ => Complex.ofRealCLM x))"
        ),
        "v4_change_ofRealCLM_convert": c2_theorem_change(
            "    convert ((Complex.ofRealCLM : ℝ →L[ℝ] ℂ).contDiff) using 1 <;> rfl"
        ),
    }
)

core.main()
