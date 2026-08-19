#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import collections
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import time

QYM = Path("PrimalitySheafVerification/QYM.lean")
SIDECAR = Path(".github/qym-frontier/QYM_GB77_BEST.lean")
RIGHT_PATCHER = Path(".github/qym_patch_gb77_v14_right_normal_im.py")
BASE_SHA = "b6f0126c27dfc08b5f81c306a7140f9531fcc3d6ca6b75dd8abbd71101d458fd"
BASE_BLOB = "c6e8883353b350f22b7f48d955fc5cfa4e61f88f"
SOURCE_ERRORS = 77
KNOWN_BEST_ERRORS = 76
VARIANTS = {"explicit_helpers", "fact_instances", "inline_duplicate"}
SECTION_RE = re.compile(r"(?ms)^section ConditionalSmoothAtlas\n.*?^end ConditionalSmoothAtlas\n")
DIAG = re.compile(
    r"^(?P<file>.*?\.lean):(?P<line>\d+):(?P<column>\d+): "
    r"(?P<severity>error|warning)(?:\((?P<code>[^)]*)\))?:\s*(?P<message>.*)$",
    re.M,
)
PANIC = re.compile(r"(?im)^.*(?:internal error|uncaught exception|panic(?:!|:|\s)).*$")

COMMON_CHARTS = r'''section ConditionalSmoothAtlas

local instance conditionalChartedSpaceH :
    ChartedSpace ℍ GammaTwoQuotient :=
  allCoveringSheetsChartedSpaceH

/-- Compose the all-sheets atlas with the standard complex atlas on `ℍ`. -/
local instance conditionalChartedSpaceComplex :
    ChartedSpace ℂ GammaTwoQuotient :=
  ChartedSpace.comp ℂ ℍ GammaTwoQuotient
'''

COMPLEX_GROUP_PROOF = r'''  apply StructureGroupoid.HasGroupoid.comp upperHalfPlaneSmoothGroupoid
  intro e he
  rw [isLocalStructomorphOn_contDiffGroupoid_iff]
  change
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ e e.source ∧
      ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ e.symm e.target at he
  exact he
'''

INTERIOR_DEFS = r'''
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

EXPLICIT_HELPERS = COMMON_CHARTS + r'''
/-- The residual supplies the intermediate smooth-groupoid compatibility.
This is an ordinary theorem because its explicit proof argument cannot be
inferred by typeclass synthesis. -/
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
''' + COMPLEX_GROUP_PROOF + r'''
/-- Conditional construction of the genuine smooth quotient manifold. -/
theorem gammaTwoQuotient_isManifold_of_smoothTransitionResidual
    (hSmooth : SmoothTransitionResidual) :
    IsManifold 𝓘(ℂ) ∞ GammaTwoQuotient := by
  letI : HasGroupoid GammaTwoQuotient (contDiffGroupoid ∞ 𝓘(ℂ)) :=
    conditionalHasGroupoidComplex hSmooth
  exact IsManifold.mk' 𝓘(ℂ) ∞ GammaTwoQuotient
''' + INTERIOR_DEFS + r'''
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

FACT_INSTANCES = COMMON_CHARTS + r'''
/-- A typeclass-safe intermediate bridge through `Fact`. -/
local instance conditionalHasGroupoidH
    [hSmooth : Fact SmoothTransitionResidual] :
    HasGroupoid GammaTwoQuotient upperHalfPlaneSmoothGroupoid :=
  allCoveringSheets_hasGroupoid hSmooth.out

/-- The complex smooth groupoid obtained from the intermediate one. -/
local instance conditionalHasGroupoidComplex
    [Fact SmoothTransitionResidual] :
    HasGroupoid GammaTwoQuotient (contDiffGroupoid ∞ 𝓘(ℂ)) := by
''' + COMPLEX_GROUP_PROOF + r'''
/-- The corresponding manifold instance, guarded by `Fact`. -/
local instance conditionalIsManifold
    [Fact SmoothTransitionResidual] :
    IsManifold 𝓘(ℂ) ∞ GammaTwoQuotient :=
  IsManifold.mk' 𝓘(ℂ) ∞ GammaTwoQuotient

/-- Conditional construction of the genuine smooth quotient manifold. -/
theorem gammaTwoQuotient_isManifold_of_smoothTransitionResidual
    (hSmooth : SmoothTransitionResidual) :
    IsManifold 𝓘(ℂ) ∞ GammaTwoQuotient := by
  letI : Fact SmoothTransitionResidual := ⟨hSmooth⟩
  exact inferInstance
''' + INTERIOR_DEFS + r'''
/-- Under the exact atlas-transition residual, every open-stage inclusion is
smooth. -/
theorem interiorStageInclusion_contMDiff
    (hSmooth : SmoothTransitionResidual) {Y Z : ℝ} (hYZ : Y ≤ Z) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ (interiorStageInclusion hYZ) := by
  letI : Fact SmoothTransitionResidual := ⟨hSmooth⟩
  exact contMDiff_inclusion (interiorStage_mono hYZ)

end ConditionalSmoothAtlas
'''

INLINE_DUPLICATE = COMMON_CHARTS + r'''
/-- Conditional construction of the genuine smooth quotient manifold. -/
theorem gammaTwoQuotient_isManifold_of_smoothTransitionResidual
    (hSmooth : SmoothTransitionResidual) :
    IsManifold 𝓘(ℂ) ∞ GammaTwoQuotient := by
  letI : HasGroupoid GammaTwoQuotient upperHalfPlaneSmoothGroupoid :=
    allCoveringSheets_hasGroupoid hSmooth
  letI : HasGroupoid GammaTwoQuotient (contDiffGroupoid ∞ 𝓘(ℂ)) := by
''' + ''.join('  ' + line if line.strip() else line for line in COMPLEX_GROUP_PROOF.splitlines(True)) + r'''  exact IsManifold.mk' 𝓘(ℂ) ∞ GammaTwoQuotient
''' + INTERIOR_DEFS + r'''
/-- Under the exact atlas-transition residual, every open-stage inclusion is
smooth. -/
theorem interiorStageInclusion_contMDiff
    (hSmooth : SmoothTransitionResidual) {Y Z : ℝ} (hYZ : Y ≤ Z) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ (interiorStageInclusion hYZ) := by
  letI : HasGroupoid GammaTwoQuotient upperHalfPlaneSmoothGroupoid :=
    allCoveringSheets_hasGroupoid hSmooth
  letI : HasGroupoid GammaTwoQuotient (contDiffGroupoid ∞ 𝓘(ℂ)) := by
''' + ''.join('  ' + line if line.strip() else line for line in COMPLEX_GROUP_PROOF.splitlines(True)) + r'''  letI : IsManifold 𝓘(ℂ) ∞ GammaTwoQuotient :=
    IsManifold.mk' 𝓘(ℂ) ∞ GammaTwoQuotient
  exact contMDiff_inclusion (interiorStage_mono hYZ)

end ConditionalSmoothAtlas
'''

SECTIONS = {
    "explicit_helpers": EXPLICIT_HELPERS,
    "fact_instances": FACT_INSTANCES,
    "inline_duplicate": INLINE_DUPLICATE,
}


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def blob(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def dump(path: Path, value: object) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


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


def parse_log(log: Path, variant: str, phase: str, returncode: int, elapsed: float) -> dict:
    raw = log.read_bytes()
    text = raw.decode("utf-8", errors="replace")
    diagnostics: list[dict] = []
    for match in DIAG.finditer(text):
        row = match.groupdict()
        row["line"] = int(row["line"])
        row["column"] = int(row["column"])
        diagnostics.append(row)
    errors = [row for row in diagnostics if row["severity"] == "error"]
    warnings = [row for row in diagnostics if row["severity"] == "warning"]
    return {
        "variant": variant,
        "phase": phase,
        "exit": returncode,
        "elapsed_seconds": round(elapsed, 3),
        "error_headers": len(errors),
        "warning_headers": len(warnings),
        "panic_lines": len(PANIC.findall(text)),
        "first_error": errors[0] if errors else None,
        "last_error": errors[-1] if errors else None,
        "errors": errors,
        "error_codes": dict(sorted(collections.Counter((r.get("code") or "uncoded") for r in errors).items())),
        "log_sha256": sha(raw),
    }


def compile_qym(out: Path, variant: str, phase: str, max_errors: int) -> dict:
    log = out / f"{phase}.log"
    olean = out / f"{phase}.olean"
    ilean = out / f"{phase}.ilean"
    cmd = ["lake", "env", "lean", f"-DmaxErrors={max_errors}", "-DwarningAsError=false",
           "-o", str(olean), "-i", str(ilean), str(QYM)]
    started = time.monotonic()
    with log.open("wb") as handle:
        proc = subprocess.run(cmd, stdout=handle, stderr=subprocess.STDOUT)
    result = parse_log(log, variant, phase, proc.returncode, time.monotonic() - started)
    result.update({
        "command": cmd,
        "olean_exists": olean.is_file() and olean.stat().st_size > 0,
        "ilean_exists": ilean.is_file() and ilean.stat().st_size > 0,
        "olean_bytes": olean.stat().st_size if olean.is_file() else 0,
        "ilean_bytes": ilean.stat().st_size if ilean.is_file() else 0,
    })
    dump(out / f"{phase.upper()}_RESULT.json", result)
    return result


def patch_candidate(original: Path, candidate: Path, variant: str, out: Path) -> dict:
    shutil.copy2(original, candidate)
    with (out / "RIGHT_NORMAL_PATCH.json").open("wb") as handle:
        subprocess.run(
            [sys.executable, "-B", str(RIGHT_PATCHER), "normsq_simpa", str(candidate), BASE_SHA],
            check=True, stdout=handle, stderr=subprocess.STDOUT,
        )
    text = candidate.read_text(encoding="utf-8")
    before_audit = audit(text)
    matches = list(SECTION_RE.finditer(text))
    if len(matches) != 1:
        raise SystemExit(f"ConditionalSmoothAtlas section matches={len(matches)}")
    match = matches[0]
    replacement = SECTIONS[variant]
    patched = text[:match.start()] + replacement + text[match.end():]
    after_audit = audit(patched)
    if after_audit != before_audit or any(after_audit.values()):
        raise SystemExit(f"forbidden-token delta: {before_audit} -> {after_audit}")
    candidate.write_text(patched, encoding="utf-8")
    raw = candidate.read_bytes()
    right_marker = "theorem conj_mul_hyperbolicRightNormal_im"
    gate_start = patched.count("\n", 0, patched.index(right_marker)) + 1
    section_start = patched.count("\n", 0, match.start()) + 1
    section_end_index = match.start() + len(replacement)
    section_end = patched.count("\n", 0, section_end_index) + 1
    next_index = patched.find("/-! ## 6. The remaining cusp-collar datum -/", section_end_index)
    next_line = patched.count("\n", 0, next_index) + 1 if next_index >= 0 else section_end + 1
    result = {
        "schema": "qym-gb77-v15-cumulative-patch-v1",
        "variant": variant,
        "source_baseline": "GB77",
        "source_baseline_error_headers": SOURCE_ERRORS,
        "known_best_before_error_headers": KNOWN_BEST_ERRORS,
        "input_sha256": BASE_SHA,
        "input_blob": BASE_BLOB,
        "candidate_sha256": sha(raw),
        "candidate_blob": blob(raw),
        "cumulative_fixes": ["right-normal-im:normsq_simpa", f"ConditionalSmoothAtlas:{variant}"],
        "gate_start_line": gate_start,
        "section_start_line": section_start,
        "section_end_line": section_end,
        "next_declaration_line": next_line,
        "forbidden": after_audit,
        "bytes": len(raw),
        "lf": raw.count(b"\n"),
    }
    dump(out / "PATCH_RESULT.json", result)
    return result


def candidate_mode(variant: str) -> int:
    if variant not in VARIANTS:
        raise SystemExit(f"unknown variant: {variant}")
    out = Path(os.environ.get("OUT_ROOT", "/tmp/qym-gb77-v15")) / variant
    out.mkdir(parents=True, exist_ok=True)
    qym_raw, sidecar_raw = QYM.read_bytes(), SIDECAR.read_bytes()
    gate = {
        "source_baseline": "GB77", "qym_sha256": sha(qym_raw), "qym_blob": blob(qym_raw),
        "sidecar_sha256": sha(sidecar_raw), "sidecar_blob": blob(sidecar_raw),
        "qym_equals_sidecar": qym_raw == sidecar_raw,
    }
    dump(out / "AUTHORITY_GATE.json", gate)
    if not (gate["qym_sha256"] == BASE_SHA and gate["qym_blob"] == BASE_BLOB and
            gate["sidecar_sha256"] == BASE_SHA and gate["sidecar_blob"] == BASE_BLOB and
            gate["qym_equals_sidecar"]):
        raise SystemExit(f"exact GB77 authority gate failed: {gate}")

    original, candidate = out / "QYM.GB77.authority.lean", out / "QYM.candidate.lean"
    shutil.copy2(QYM, original)
    run_value = os.environ.get("GITHUB_RUN_ID", "manual")
    result: dict = {
        "schema": "qym-gb77-v15-cumulative-result-v1",
        "run_id": int(run_value) if run_value.isdigit() else run_value,
        "trigger_sha": os.environ.get("GITHUB_SHA"), "branch": os.environ.get("GITHUB_REF_NAME"),
        "variant": variant, "source_baseline": "GB77", "source_baseline_error_headers": SOURCE_ERRORS,
        "source_baseline_qym_sha256": BASE_SHA, "source_baseline_qym_blob": BASE_BLOB,
        "known_best_before_error_headers": KNOWN_BEST_ERRORS,
        "full_compile_executed": False, "strict_improvement_beyond_known_best": False,
        "semantic_pass": False,
    }
    try:
        patch = patch_candidate(original, candidate, variant, out)
        result.update({"patch": patch, "forbidden": patch["forbidden"],
                       "candidate_qym_sha256": patch["candidate_sha256"],
                       "candidate_qym_blob": patch["candidate_blob"]})
        shutil.copy2(candidate, QYM)
        local = compile_qym(out, variant, "local", 16)
        lo, hi, nxt = int(patch["gate_start_line"]), int(patch["section_end_line"]), int(patch["next_declaration_line"])
        gate_errors = [e for e in local["errors"] if lo <= int(e["line"]) <= hi]
        earlier = [e for e in local["errors"] if int(e["line"]) < lo]
        first = local.get("first_error")
        advanced = first is None or int(first["line"]) >= nxt
        local_pass = int(local["panic_lines"]) == 0 and not gate_errors and not earlier and advanced
        result.update({"local": local, "gate_errors": gate_errors, "earlier_errors": earlier,
                       "local_gate_pass": local_pass,
                       "first_blocker_advanced_beyond_groupoid_section": advanced})
        if local_pass:
            full = compile_qym(out, variant, "full", 10000)
            semantic = (int(full["exit"]) == 0 and int(full["error_headers"]) == 0 and
                        int(full["panic_lines"]) == 0 and full["olean_exists"] and full["ilean_exists"])
            strict = semantic or (int(full["panic_lines"]) == 0 and int(full["error_headers"]) < KNOWN_BEST_ERRORS)
            result.update({"full_compile_executed": True, "full": full, "exit": full["exit"],
                           "error_headers": full["error_headers"], "warning_headers": full["warning_headers"],
                           "panic_lines": full["panic_lines"], "first_error": full["first_error"],
                           "last_error": full["last_error"], "error_codes": full["error_codes"],
                           "log_sha256": full["log_sha256"], "semantic_pass": semantic,
                           "strict_improvement_beyond_known_best": strict})
        dump(out / "RESULT.json", result)
        return 0
    finally:
        shutil.copy2(original, QYM)


def first_line(row: dict) -> int:
    return int(row["first_error"]["line"]) if row.get("first_error") else 10**9


def select_mode(root: Path, out: Path) -> int:
    out.mkdir(parents=True, exist_ok=True)
    rows, valid = [], []
    for result_path in sorted(root.rglob("RESULT.json")):
        try:
            row = json.loads(result_path.read_text(encoding="utf-8"))
        except Exception as exc:
            rows.append({"result_path": str(result_path), "parse_error": repr(exc)})
            continue
        candidate = result_path.parent / "QYM.candidate.lean"
        row["artifact_result_path"], row["artifact_candidate_path"] = str(result_path), str(candidate)
        rows.append(row)
        if not (row.get("source_baseline") == "GB77" and int(row.get("source_baseline_error_headers", -1)) == SOURCE_ERRORS and
                row.get("source_baseline_qym_sha256") == BASE_SHA and row.get("source_baseline_qym_blob") == BASE_BLOB and
                int(row.get("known_best_before_error_headers", -1)) == KNOWN_BEST_ERRORS and
                row.get("full_compile_executed") is True and int(row.get("panic_lines", 1)) == 0 and
                row.get("strict_improvement_beyond_known_best") is True and
                int(row.get("error_headers", KNOWN_BEST_ERRORS)) < KNOWN_BEST_ERRORS and candidate.is_file()):
            continue
        raw = candidate.read_bytes()
        forbidden = row.get("forbidden") or {}
        if sha(raw) == row.get("candidate_qym_sha256") and blob(raw) == row.get("candidate_qym_blob") and not any(int(v) for v in forbidden.values()):
            valid.append((row, candidate))
    valid.sort(key=lambda p: (int(p[0]["error_headers"]), int(p[0].get("warning_headers", 10**9)), -first_line(p[0]), str(p[0].get("variant", ""))))
    selection = {
        "schema": "qym-gb77-v15-cumulative-selection-v1",
        "source_baseline": {"name": "GB77", "error_headers": SOURCE_ERRORS, "qym_sha256": BASE_SHA, "qym_blob": BASE_BLOB},
        "known_verified_descendant_before": {"error_headers": KNOWN_BEST_ERRORS, "variant": "V14b-normsq_simpa"},
        "candidate_result_count": len(rows), "valid_strict_improvement_count": len(valid),
        "strict_improvement_beyond_76_found": bool(valid), "results": rows,
    }
    if valid:
        best, source = valid[0]
        shutil.copy2(source, out / "QYM.best.lean")
        dump(out / "BEST_RESULT.json", best)
        selection["best_variant"], selection["best"] = best["variant"], best
    dump(out / "SELECTION.json", selection)
    return 0


def main() -> int:
    if len(sys.argv) == 3 and sys.argv[1] == "candidate":
        return candidate_mode(sys.argv[2])
    if len(sys.argv) == 4 and sys.argv[1] == "select":
        return select_mode(Path(sys.argv[2]), Path(sys.argv[3]))
    raise SystemExit(f"usage: {Path(sys.argv[0]).name} candidate VARIANT | select ARTIFACT_ROOT OUTPUT_DIR")


if __name__ == "__main__":
    raise SystemExit(main())
