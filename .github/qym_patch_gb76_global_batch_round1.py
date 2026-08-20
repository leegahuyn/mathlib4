#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys
import tempfile

BASE_SHA256 = "fada22264b6618467f89d436ddacff27453db1242769717d5e7a386682d4efb3"
BASE_BLOB = "29d446743036dccd5d9ad8757c351b39d526cfa9"

GROUPING_PATCHER = Path(".github/qym_patch_gb77_fixedorigin_v16_groupoid.py")
INVERSE_ETA_PATCHER = Path(".github/qym_patch_gb77_fixedorigin_v17_inverse_eta.py")

REPLACEMENTS: list[tuple[str, str, str]] = [
    (
        "covariant_total_lift_parentheses",
        """noncomputable def covariantTotalLift
    (f : EtaCovariantLift) (tau : H) : InverseEtaTotal :=
  inverseEtaTotalMk tau (f : H -> ℂ) tau
""",
        """noncomputable def covariantTotalLift
    (f : EtaCovariantLift) (tau : H) : InverseEtaTotal :=
  inverseEtaTotalMk tau ((f : H -> ℂ) tau)
""",
    ),
    (
        "dense_extension_explicit_arguments",
        """  exact LinearMap.norm_extendOfNorm_apply_le
    (denseRange_coreMap n) C0 hC0 x
""",
        """  exact LinearMap.norm_extendOfNorm_apply_le
    (f := actualFixedPhaseSmoothCoreToProductCollarProfile n Y)
    (e := coreMap n)
    (denseRange_coreMap n) C0 hC0 x
""",
    ),
    (
        "global_projection_add_indicator",
        """  by_cases hx : x ∈ naturalStageSet n
  · simp only [globalStageProjectionRepresentative, hx,
      Set.indicator_of_mem, huv]
  · simp only [globalStageProjectionRepresentative, hx,
      Set.indicator_of_notMem, add_zero]
""",
        """  by_cases hx : x ∈ naturalStageSet n
  · simp [globalStageProjectionRepresentative, hx, huv]
  · simp [globalStageProjectionRepresentative, hx]
""",
    ),
    (
        "global_projection_smul_indicator",
        """  by_cases hx : x ∈ naturalStageSet n
  · simp only [globalStageProjectionRepresentative, hx,
      Set.indicator_of_mem, hcu]
  · simp only [globalStageProjectionRepresentative, hx,
      Set.indicator_of_notMem, smul_zero]
""",
        """  by_cases hx : x ∈ naturalStageSet n
  · simp [globalStageProjectionRepresentative, hx, hcu]
  · simp [globalStageProjectionRepresentative, hx]
""",
    ),
    (
        "global_projection_density_bound",
        """  by_cases hx : x ∈ naturalStageSet n
  · simp [globalStageProjectionErrorDensity,
      globalL2DominatingDensity,
      globalStageProjectionRepresentative, hx]
  · simp [globalStageProjectionErrorDensity,
      globalL2DominatingDensity,
      globalStageProjectionRepresentative, hx]
""",
        """  by_cases hx : x ∈ naturalStageSet n
  · simp [globalStageProjectionErrorDensity,
      globalL2DominatingDensity,
      globalStageProjectionRepresentative,
      naturalStageSet, naturalStageCutoff, hx]
  · simp [globalStageProjectionErrorDensity,
      globalL2DominatingDensity,
      globalStageProjectionRepresentative,
      naturalStageSet, naturalStageCutoff, hx]
""",
    ),
    (
        "global_projection_density_eventually_zero",
        """  filter_upwards [eventually_mem_naturalStageSet x] with n hn
  simp [globalStageProjectionErrorDensity,
    globalStageProjectionRepresentative, hn]
""",
        """  filter_upwards [eventually_mem_naturalStageSet x] with n hn
  simp [globalStageProjectionErrorDensity,
    globalStageProjectionRepresentative,
    naturalStageSet, naturalStageCutoff, hn]
""",
    ),
    (
        "global_projection_density_tendsto_pointwise",
        """  have hx : x ∈ naturalStageSet n :=
    naturalStageSet_monotone hn hN
  simp [globalStageProjectionErrorDensity,
    globalStageProjectionRepresentative, hx]
""",
        """  have hx : x ∈ naturalStageSet n :=
    naturalStageSet_monotone hn hN
  simp [globalStageProjectionErrorDensity,
    globalStageProjectionRepresentative,
    naturalStageSet, naturalStageCutoff, hx]
""",
    ),
    (
        "coordinate_form_real_part",
        """  rw [coordinateHamiltonianForm_apply,
    inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
  simp
""",
        """  rw [coordinateHamiltonianForm_apply,
    inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
  simp only [Complex.ofReal_re]
""",
    ),
]


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git_blob(data: bytes) -> str:
    return hashlib.sha1(
        b"blob " + str(len(data)).encode("ascii") + b"\0" + data
    ).hexdigest()


def audit(text: str) -> dict[str, int]:
    return {
        "sorry": len(re.findall(r"\bsorry\b", text)),
        "admit": len(re.findall(r"\badmit\b", text)),
        "native_decide": len(re.findall(r"\bnative_decide\b", text)),
        "Lean.ofReduceBool": text.count("Lean.ofReduceBool"),
        "global_axiom": len(re.findall(r"(?m)^\s*axiom\s+", text)),
        "unsafe": len(re.findall(r"(?m)^\s*unsafe\s+", text)),
        "maxHeartbeats_zero": len(
            re.findall(r"set_option\s+maxHeartbeats\s+0\b", text)
        ),
    }


def replace_once(text: str, old: str, new: str, label: str) -> str:
    count = text.count(old)
    if count != 1:
        raise SystemExit(f"{label}: expected exactly one source block, found {count}")
    return text.replace(old, new, 1)


def run_patcher(command: list[str], label: str) -> dict[str, object]:
    proc = subprocess.run(
        command,
        check=False,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if proc.returncode != 0:
        raise SystemExit(
            f"{label} failed with exit {proc.returncode}\n"
            f"stdout:\n{proc.stdout}\n"
            f"stderr:\n{proc.stderr}"
        )
    payload: dict[str, object]
    try:
        payload = json.loads(proc.stdout)
    except json.JSONDecodeError:
        payload = {"raw_stdout": proc.stdout}
    return payload


def main() -> None:
    if len(sys.argv) != 3:
        raise SystemExit(
            "usage: qym_patch_gb76_global_batch_round1.py "
            "INPUT_QYM OUTPUT_QYM"
        )

    input_path = Path(sys.argv[1])
    output_path = Path(sys.argv[2])
    before = input_path.read_bytes()
    before_sha = sha256(before)
    before_blob = git_blob(before)
    if before_sha != BASE_SHA256 or before_blob != BASE_BLOB:
        raise SystemExit(
            "exact GB76 authority mismatch: "
            f"sha256={before_sha} blob={before_blob}"
        )

    before_text = before.decode("utf-8")
    before_audit = audit(before_text)
    if any(before_audit.values()):
        raise SystemExit(f"baseline forbidden-token audit is nonzero: {before_audit}")

    if not GROUPING_PATCHER.is_file() or not INVERSE_ETA_PATCHER.is_file():
        raise SystemExit(
            "required exact-GB76 inherited patchers are missing: "
            f"{GROUPING_PATCHER}, {INVERSE_ETA_PATCHER}"
        )

    with tempfile.TemporaryDirectory(prefix="qym-gb76-global-round1-") as tmp:
        tmp_path = Path(tmp)
        groupoid_path = tmp_path / "QYM.groupoid.lean"
        inverse_eta_path = tmp_path / "QYM.inverse-eta.lean"

        groupoid_result = run_patcher(
            [
                sys.executable,
                str(GROUPING_PATCHER),
                "inline_duplicate",
                str(input_path),
                str(groupoid_path),
            ],
            "conditional-atlas groupoid patch",
        )
        inverse_eta_result = run_patcher(
            [
                sys.executable,
                str(INVERSE_ETA_PATCHER),
                "explicit_cases",
                str(groupoid_path),
                str(inverse_eta_path),
            ],
            "inverse-eta fibre patch",
        )

        text = inverse_eta_path.read_text(encoding="utf-8")

    applied: list[str] = []
    for label, old, new in REPLACEMENTS:
        text = replace_once(text, old, new, label)
        applied.append(label)

    after_audit = audit(text)
    if after_audit != before_audit or any(after_audit.values()):
        raise SystemExit(
            f"forbidden-token delta: baseline={before_audit} candidate={after_audit}"
        )

    required_markers = [
        "theorem gammaTwoQuotient_isManifold_of_smoothTransitionResidual",
        "noncomputable def inverseEtaFibreCoordinateHomeomorph",
        "theorem covariantTotalLift_invariant",
        "theorem actualFixedPhaseOldGraphToProductCollarExtension_unique",
        "theorem globalStageProjectionLinearMap_apply",
        "theorem globalStageProjectionErrorDensity_lintegral_tendsto_zero",
        "theorem coordinateHamiltonianForm_positiveShift",
    ]
    missing = [marker for marker in required_markers if marker not in text]
    if missing:
        raise SystemExit(f"post-patch structural gate missing markers: {missing}")

    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(text, encoding="utf-8")
    after = output_path.read_bytes()

    result = {
        "schema": "qym-gb76-global-batch-round1-patch-v1",
        "input_sha256": before_sha,
        "input_blob": before_blob,
        "candidate_sha256": sha256(after),
        "candidate_blob": git_blob(after),
        "candidate_bytes": len(after),
        "candidate_lf": after.count(b"\n"),
        "groupoid_variant": "inline_duplicate",
        "inverse_eta_variant": "explicit_cases",
        "groupoid_result": groupoid_result,
        "inverse_eta_result": inverse_eta_result,
        "independent_replacements": applied,
        "independent_replacement_count": len(applied),
        "forbidden": after_audit,
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
