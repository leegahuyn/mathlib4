#!/usr/bin/env python3
"""Offline fail-closed contract and exact composer for the v65 ten-lane matrix.

Every candidate is reconstructed from the official v62 ``fourier_pair`` source.
Neither a v63 candidate nor a v64 preview is ever used as a runtime base.  The
v63 and v64 packages contribute only byte-locked body replacement operations.
"""

from __future__ import annotations

import hashlib
import json
import re
from dataclasses import dataclass
from functools import lru_cache
from pathlib import Path
from typing import Any, Iterable


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
STATIC_LAYOUT = HERE.name == "v65-ci" and HERE.parent.name == "work"
PENDING_EXIT = 2
CONTRACT_EXIT = 86
DECLARATION_COUNT = 4416
TOOLCHAIN = "leanprover/lean4:v4.33.0-rc1"
TOOLCHAIN_SHA256 = "62c2d9c0fc1ec4c67e151c11eff41ca004ef38e179cf9476c230406e6defedef"
LEAN_VERSION = (
    "Lean (version 4.33.0-rc1, x86_64-unknown-linux-gnu, "
    "commit 62eed1db4d67327ec8120be05f1a1b0847d74561, Release)"
)

TRUST_TOKENS = (
    "sorry",
    "admit",
    "axiom",
    "unsafe",
    "native_decide",
    "Lean.ofReduceBool",
)
TRUST_ZERO = {token: 0 for token in TRUST_TOKENS}

DECL_RE = re.compile(
    r"(?m)^(?:protected\s+|private\s+|noncomputable\s+|local\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance|structure|class)\s+([^\s(:]+)"
)


INPUT_LOCKS: dict[str, dict[str, Any]] = {
    "v62_source": {
        "path": "work/v61-results/run-31863434345/fourier_pair/extracted/Mock2_FunctionalAnalysis-candidate.lean",
        "sha256": "1badac1451e11708114eb5438616063379558bcf0579dc82a01c2200b501d365",
        "bytes": 2812442,
        "lines": 62933,
    },
    "v62_ready": {
        "path": "work/v62-prep/v62-artifact-inputs.json",
        "sha256": "8a7f65766baf2d20713b7cfa29c7edbb0a5cff0d670256adebfb57646ce2ab51",
        "bytes": 160559,
    },
    "v63_selection_ready": {
        "path": "work/v63-ci/fa_v63_selection.READY.json",
        "sha256": "9d4313db727c3a5625d6fcfddcc2fa97a692ad99cae11957b9d8561094211367",
        "bytes": 13802,
    },
    "v63_f3930_manifest": {
        "path": "work/v63-ci/fa_v63_f3930-manifest.READY.json",
        "sha256": "cd408eeeab5be791525fc6d24b1402577e95830243c64a0c36edbcbca19e64c5",
        "bytes": 3114,
    },
    "v63_f3933_manifest": {
        "path": "work/v63-ci/fa_v63_f3933-manifest.READY.json",
        "sha256": "b95091f2140afaf36e60e26b4b09b482d32b4cd7d409751e8859384fcfca03ce",
        "bytes": 8647,
    },
    "v63_w4017_manifest": {
        "path": "work/v63-ci/fa_v63_w4017-manifest.READY.json",
        "sha256": "0285c92f68d6c4222105dfcb6c8c4483cf4f87cf67832fe9ae076698a7cae01f",
        "bytes": 11395,
    },
    "v63_final_audit": {
        "path": "work/v63-results/run-31871876992/FINAL_AUDIT.json",
        "sha256": "1d112cca286b0296e070f82e1ce9aae4c7c952ca9d286cca4de7bc29e58d5615",
        "bytes": 7794,
    },
    "v64_ready_inputs": {
        "path": "work/v64-prep/v64-artifact-inputs.json",
        "sha256": "ade268f16ba52c293cd38317bf34598aa2dd181aff93260a98ee8d99208d752a",
        "bytes": 207063,
    },
    "v64_ranking_a": {
        "path": "work/v64-prep/v64-compare-a/ranking.json",
        "sha256": "737c628ebe9684dddcb819e1e0939c80698288835ee2920279dd71ac64b85590",
        "bytes": 3352,
    },
    "v64_ranking_b": {
        "path": "work/v64-prep/v64-compare-b/ranking.json",
        "sha256": "737c628ebe9684dddcb819e1e0939c80698288835ee2920279dd71ac64b85590",
        "bytes": 3352,
    },
    "v64_queues_a": {
        "path": "work/v64-prep/v64-compare-a/winner-residual-queues.json",
        "sha256": "e5f0faae2f3ef00bbbb384362c8954dec2e2470fdd34fd01d8f7f3090327ccf7",
        "bytes": 8149,
    },
    "v64_queues_b": {
        "path": "work/v64-prep/v64-compare-b/winner-residual-queues.json",
        "sha256": "e5f0faae2f3ef00bbbb384362c8954dec2e2470fdd34fd01d8f7f3090327ccf7",
        "bytes": 8149,
    },
    "v63_winner_candidate": {
        "path": "work/v63-results/run-31871876992/w4017_full/root/Mock2_FunctionalAnalysis-candidate.lean",
        "sha256": "20ad5b01e774f1c388d2d16991e34840fdafe0f9d033038652311b29d84ae3f5",
        "bytes": 2813021,
        "lines": 62944,
    },
    "w4017_followup_manifest": {
        "path": "work/v64-workers/w4017-followup/w4017-followup-repair-manifest.json",
        "sha256": "4537056d6237121b3520a347e07a15a5f9bfe82399ec20b5883be23793657c7c",
        "bytes": 20799,
    },
    "w4017_followup_result": {
        "path": "work/v64-workers/w4017-followup/w4017-followup-result-index.json",
        "sha256": "af1d3638992b4c6bea4e4994f512c231bfc35054bd979d9f9337c742ab0d7ffc",
        "bytes": 1547,
    },
    "w4017_followup_validation": {
        "path": "work/v64-workers/w4017-followup/w4017-followup-static-validation.json",
        "sha256": "9a9d254c8e077e191c15e05bd79f19240f86d9ea9534a5776ba19d780b4af5fb",
        "bytes": 1266,
    },
    "w4017_followup_ledger": {
        "path": "work/v64-workers/w4017-followup/SHA256SUMS.w4017-followup.txt",
        "sha256": "be421e3387a24cfd0d3ee98485f23f5a0fce3204579ad2188ae0f991f0bbceac",
        "bytes": 715,
    },
    "f_followup_manifest": {
        "path": "work/v64-workers/fallback-prep/fallback-repair-manifest.json",
        "sha256": "8902b0f7b259053806aa4c7c2d1fda876189ac3782ebe0a538c6009aaa23f1f9",
        "bytes": 156683,
    },
    "f_followup_result": {
        "path": "work/v64-workers/fallback-prep/fallback-result-index.json",
        "sha256": "13acc6d58171319868f16b9774c585db8c25f0b805cd8eeea973725d77e94958",
        "bytes": 6803,
    },
    "f_followup_validation": {
        "path": "work/v64-workers/fallback-prep/fallback-static-validation.json",
        "sha256": "e67aeabc7773ed56fd8e15f9dbe9e7a2f449c17de9c5b7f97c2e7a26f9d16a18",
        "bytes": 10053,
    },
    "f_followup_ledger": {
        "path": "work/v64-workers/fallback-prep/SHA256SUMS.fallback-prep.txt",
        "sha256": "52b24725efd40c7138e27524a6ca7e08786c122aeae0b44b77b1f925ada0dd52",
        "bytes": 1616,
    },
}

# These are the only operation packages a promoted runtime may read.  They are
# byte-identical normalized copies under repo/scripts; no work/ path is allowed.
RUNTIME_MANIFEST_LOCKS: dict[str, dict[str, Any]] = {
    "v63_f3930_manifest": {"name": "fa_v65_v63_f3930-manifest.json", **{key: INPUT_LOCKS["v63_f3930_manifest"][key] for key in ("sha256", "bytes")}},
    "v63_f3933_manifest": {"name": "fa_v65_v63_f3933-manifest.json", **{key: INPUT_LOCKS["v63_f3933_manifest"][key] for key in ("sha256", "bytes")}},
    "v63_w4017_manifest": {"name": "fa_v65_v63_w4017-manifest.json", **{key: INPUT_LOCKS["v63_w4017_manifest"][key] for key in ("sha256", "bytes")}},
    "f_followup_manifest": {"name": "fa_v65_f-followup-manifest.json", **{key: INPUT_LOCKS["f_followup_manifest"][key] for key in ("sha256", "bytes")}},
    "w4017_followup_manifest": {"name": "fa_v65_w4017-followup-manifest.json", **{key: INPUT_LOCKS["w4017_followup_manifest"][key] for key in ("sha256", "bytes")}},
}

EXPECTED_CANDIDATES: dict[str, dict[str, int | str]] = {
    "winner_baseline": {"sha256": "20ad5b01e774f1c388d2d16991e34840fdafe0f9d033038652311b29d84ae3f5", "bytes": 2813021, "lines": 62944, "declaration_count": 4416},
    "w4017_primary": {"sha256": "93491e69d4e6f3d24f11ad45ecbb3a5c74aa28202c2771484a3663cdd51846fc", "bytes": 2813090, "lines": 62945, "declaration_count": 4416},
    "w4017_rfl_fallback": {"sha256": "6a2524de966143f709c92dfb992a8f2029be4648812518010a4c5639f0c4b288", "bytes": 2813031, "lines": 62945, "declaration_count": 4416},
    "f3930_field": {"sha256": "772ed2cb7295175fe9e42217e646e766b0a7b0b8b92a4c956f193c49b2d9efb4", "bytes": 2812585, "lines": 62936, "declaration_count": 4416},
    "f3930_explicit": {"sha256": "26541fa4712474c944ee4ec2ac209a1873fb07062577c9a08286876bed937ca9", "bytes": 2812774, "lines": 62939, "declaration_count": 4416},
    "f3933_invcalc": {"sha256": "44b80a7976626073cdccc326c925741fd51244932e20d4a518928c5ad09ba448", "bytes": 2813195, "lines": 62948, "declaration_count": 4416},
    "f_field_f3933": {"sha256": "12b5a0e8e359461a8f492c5acefb47a17a31fae6a89fbf52ff8b127e5a99d634", "bytes": 2813338, "lines": 62951, "declaration_count": 4416},
    "f_explicit_f3933": {"sha256": "23a4c5e517aa26cda065f98fa169342105f10cb132089b1293b0f54826e5488d", "bytes": 2813527, "lines": 62954, "declaration_count": 4416},
    "all_field_w_primary": {"sha256": "71d8eeca6cce4e520754a3e45b43bf3d61a94f4f1bac6f452d0c8ae2c1ee853b", "bytes": 2813986, "lines": 62963, "declaration_count": 4416},
    "all_explicit_w_primary": {"sha256": "a7dd32aba7182c55cb3de9986eeabef537602cbfc24cf2aa956e6b43541d0c54", "bytes": 2814175, "lines": 62966, "declaration_count": 4416},
}

RESULT_ARTIFACT_MEMBERS = [
    "AUTHORITY_REPROOF.json", "AUTHORITY_REPROOF.stdout.json", "BASE_FINAL_GATE.json",
    "BASE_FULL_DIAGNOSTICS.json", "BASE_MATERIALIZATION.json",
    "BASE_Mock2_FunctionalAnalysis-candidate.lean", "BASE_Mock2_FunctionalAnalysis.log",
    "BASE_TOOLCHAIN_PIN.json", "COLLECTOR_AUTHORITY_ATTESTATION.json",
    "DIAGNOSTIC_DECLARATION_COUNTS.json", "FINAL_GATE.json", "FINAL_GATE.stdout.json",
    "FULL_DIAGNOSTICS.json", "FULL_WARNINGS.json", "MATERIALIZATION.json",
    "MATERIALIZATION.stdout.json", "METRIC.json", "Mock2.command", "Mock2.executed",
    "Mock2.exit", "Mock2.log", "Mock2_Advanced.command", "Mock2_Advanced.executed",
    "Mock2_Advanced.exit", "Mock2_Advanced.log", "Mock2_FunctionalAnalysis-candidate.lean",
    "Mock2_FunctionalAnalysis-observed.lean", "Mock2_FunctionalAnalysis.command",
    "Mock2_FunctionalAnalysis.executed", "Mock2_FunctionalAnalysis.exit",
    "Mock2_FunctionalAnalysis.log", "PATCH_AUDIT.json", "SCAFFOLD_GATE.json",
    "SYNTHETIC_SORRY_WARNINGS.json", "TOOLCHAIN_PIN.json", "V63_ARTIFACT.json",
    "V63_JOBS.json", "V63_RUN.json", "VARIANT_INDEX.json", "cache.log",
    "candidate.after.sha256", "candidate.before-fa.sha256", "candidate.before.sha256",
    "candidate.sha256", "elan.log", "lean-version.txt", "metric-console.log", "toolchain.log",
]

BASE_AUTHORITY_COPIES = [
    {"result_member": "BASE_FINAL_GATE.json", "authority_member": "FINAL_GATE.json", "sha256": "2537e5bbc28e11dfdbcb5cc6bc7d2adbac5d571b37393087863b1215b88b9b95", "bytes": 1905},
    {"result_member": "BASE_FULL_DIAGNOSTICS.json", "authority_member": "FULL_DIAGNOSTICS.json", "sha256": "31370de532745411bd9acdc258cf5d90c9d0bb5b08b23870b00b55300000f383", "bytes": 5807},
    {"result_member": "BASE_MATERIALIZATION.json", "authority_member": "MATERIALIZATION.json", "sha256": "a3467b09c65eab27f539c0eed1c78dfc260b2bdcf1aedb971ac74d526984d781", "bytes": 2675},
    {"result_member": "BASE_Mock2_FunctionalAnalysis-candidate.lean", "authority_member": "Mock2_FunctionalAnalysis-candidate.lean", "sha256": "1badac1451e11708114eb5438616063379558bcf0579dc82a01c2200b501d365", "bytes": 2812442},
    {"result_member": "BASE_Mock2_FunctionalAnalysis.log", "authority_member": "Mock2_FunctionalAnalysis.log", "sha256": "8e27a4dcc8be79a091b8b1c2f61197fdb7c9e4d995f3e158327442969c1de60a", "bytes": 290901},
    {"result_member": "BASE_TOOLCHAIN_PIN.json", "authority_member": "TOOLCHAIN_PIN.json", "sha256": "8f54d5486b82a5fc11bc52199c89265b7e9e8eed5a3ff4131f86251894bcff07", "bytes": 393},
]

CROSS_AUDIT_LOCK = {
    "path": "work/v65-cross-audit/v65-cross-audit-final.json",
    "sha256": "f7f2f57561ef9e2d71af5db41e8249d958fdfe73131d3e6931fbb43fe889a2ab",
    "bytes": 56124,
    "schema": "fa-v65-repair-cross-audit-final-v1",
    "status": "PASS_STATIC_COMPLETE_DIRECT_LEAN_UNVERIFIED_NONCLEAN",
}
CROSS_AUDIT_FILES = [
    {"path": "work/v65-cross-audit/v65-cross-audit-preliminary.json", "sha256": "e3b6f1cd6cd4b6811d4053f2c0faf8b071e21f1edd347473234f44d3a481cacf", "bytes": 64462},
    {"path": "work/v65-cross-audit/v65-next-matrix.json", "sha256": "b88f3141d9377a58ac0dbd087dc2813611428c6c9d0c8fa3f68a7d4199a95c82", "bytes": 13524},
    {"path": "work/v65-cross-audit/v65-pairwise-audit.json", "sha256": "48ed0b98e0e6aa96fa3f405e23839eb9a1f39d84c1d542211950b943a3ad2bf5", "bytes": 143220},
    {"path": "work/v65-cross-audit/v65-cross-audit-final.json", "sha256": "f7f2f57561ef9e2d71af5db41e8249d958fdfe73131d3e6931fbb43fe889a2ab", "bytes": 56124},
    {"path": "work/v65-cross-audit/v65-cross-audit-static-validation.json", "sha256": "1e4b66ae720659f7771d26d47738f77beffc331852b27ce8c85742a8059596fb", "bytes": 1282},
    {"path": "work/v65-cross-audit/SHA256SUMS.v65-cross-audit.txt", "sha256": "07f0643d9891c6465536043203e153a88c2f117efd7b28517d6da30e68dc2c7f", "bytes": 716},
]

PENDING_BLOCKERS = [
    "FINAL_RUNTIME_SCRIPT_HASH_FREEZE_NOT_EMITTED",
    "EXPLICIT_READY_ACTIVATION_NOT_RECORDED",
    "DIRECT_LEAN_RESULTS_DO_NOT_EXIST",
    "WORKFLOW_LAST_NOT_EMITTED",
]

ACTIVATION_KEYS = [
    "materialization_allowed", "workflow_matrix_allowed", "direct_compile_allowed",
    "ready_selection_emitted", "workflow_last_emitted",
]

SELECTION_CONSTRAINTS = {
    "bounded_variant_count": 10,
    "all_variants_from_exact_authority": True,
    "hidden_cumulative_parentage": False,
    "distinct_candidate_outputs": True,
    "body_only": True,
    "declaration_count": 4416,
    "source_moves": 0,
    "maxHeartbeats_delta": 0,
    "trust_six_delta": 0,
    "runtime_evidence_fallback_allowed": False,
    "pending_exit_code": 2,
    "contract_violation_exit_code": 86,
    "FA_maxErrors": 2000,
}

COMPILE_CONTRACT = {
    "exact_job_count": 10,
    "max_parallel": 10,
    "exactly_one_job_per_variant": True,
    "each_job_runs_full_chain": ["Mock2", "Mock2_Advanced", "Mock2_FunctionalAnalysis_FA2000"],
    "each_job_uploads_one_exact_48_member_artifact": True,
    "fail_fast": False,
    "individual_axes_may_not_be_omitted": True,
}


COMPONENTS: dict[str, dict[str, Any]] = {
    "v63_f3930_precursor": {
        "owner_index": 3930,
        "depends_on": [],
        "operation_refs": [["v63_f3930_manifest", "V63-F3930-PI-NEG-APPLY-RING", "f3930-body"]],
    },
    "v64_f3930_field": {
        "owner_index": 3930,
        "depends_on": ["v63_f3930_precursor"],
        "variant_id": "idx3930_after_pi_neg_fieldsimp_ring",
    },
    "v64_f3930_explicit": {
        "owner_index": 3930,
        "depends_on": ["v63_f3930_precursor"],
        "variant_id": "idx3930_after_pi_neg_explicit_cancel",
    },
    "v63_f3933_fallback_precursor": {
        "owner_index": 3933,
        "depends_on": [],
        "operation_refs": [
            ["v63_f3933_manifest", "V63-F3933-PROGRESSION", "f3933-direct-evidence-progression"],
            ["v63_f3933_manifest", "V63-F3933-FIELDSIMP", "f3933-bounded-fieldsimp"],
        ],
    },
    "v64_f3933_invcalc": {
        "owner_index": 3933,
        "depends_on": ["v63_f3933_fallback_precursor"],
        "variant_id": "idx3933_after_fallback_inv_calc",
    },
    "v63_w4017_full_precursor": {
        "owner_index": 4017,
        "depends_on": [],
        "operation_refs": [
            ["v63_w4017_manifest", "V63-W4017-R17-BASE", "w4017-r17-boundary-unblock"],
            ["v63_w4017_manifest", "V63-W4017-P", "w4017-p-literal"],
            ["v63_w4017_manifest", "V63-W4017-P", "w4017-p-carrier"],
            ["v63_w4017_manifest", "V63-W4017-Z", "w4017-z-unfold-phi"],
            ["v63_w4017_manifest", "V63-W4017-W", "w4017-w-literal"],
            ["v63_w4017_manifest", "V63-W4017-W", "w4017-w-carrier"],
        ],
    },
    "v64_w4017_primary": {
        "owner_index": 4017,
        "depends_on": ["v63_w4017_full_precursor"],
        "variant_id": "idx4017_after_full_literal_graph_base_simp",
    },
    "v64_w4017_rfl": {
        "owner_index": 4017,
        "depends_on": ["v63_w4017_full_precursor"],
        "variant_id": "idx4017_after_full_literal_rfl",
    },
}


LANE_ORDER = [
    "winner_baseline",
    "w4017_primary",
    "w4017_rfl_fallback",
    "f3930_field",
    "f3930_explicit",
    "f3933_invcalc",
    "f_field_f3933",
    "f_explicit_f3933",
    "all_field_w_primary",
    "all_explicit_w_primary",
]

LANE_COMPONENTS: dict[str, list[str]] = {
    "winner_baseline": ["v63_w4017_full_precursor"],
    "w4017_primary": ["v63_w4017_full_precursor", "v64_w4017_primary"],
    "w4017_rfl_fallback": ["v63_w4017_full_precursor", "v64_w4017_rfl"],
    "f3930_field": ["v63_f3930_precursor", "v64_f3930_field"],
    "f3930_explicit": ["v63_f3930_precursor", "v64_f3930_explicit"],
    "f3933_invcalc": ["v63_f3933_fallback_precursor", "v64_f3933_invcalc"],
    "f_field_f3933": [
        "v63_f3930_precursor", "v64_f3930_field",
        "v63_f3933_fallback_precursor", "v64_f3933_invcalc",
    ],
    "f_explicit_f3933": [
        "v63_f3930_precursor", "v64_f3930_explicit",
        "v63_f3933_fallback_precursor", "v64_f3933_invcalc",
    ],
    "all_field_w_primary": [
        "v63_f3930_precursor", "v64_f3930_field",
        "v63_f3933_fallback_precursor", "v64_f3933_invcalc",
        "v63_w4017_full_precursor", "v64_w4017_primary",
    ],
    "all_explicit_w_primary": [
        "v63_f3930_precursor", "v64_f3930_explicit",
        "v63_f3933_fallback_precursor", "v64_f3933_invcalc",
        "v63_w4017_full_precursor", "v64_w4017_primary",
    ],
}


def sha256(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def canonical_json(value: Any) -> bytes:
    return (json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True) + "\n").encode("utf-8")


def file_lock(path: Path) -> dict[str, Any]:
    payload = path.read_bytes()
    return {"sha256": sha256(payload), "bytes": len(payload)}


@lru_cache(maxsize=None)
def read_locked(lock_id: str) -> bytes:
    if not STATIC_LAYOUT:
        raise AssertionError("local work evidence is forbidden in promoted runtime")
    lock = INPUT_LOCKS[lock_id]
    path = ROOT / lock["path"]
    if path.is_symlink() or not path.is_file():
        raise AssertionError(f"locked input is not an ordinary file: {lock_id}: {path}")
    payload = path.read_bytes()
    if len(payload) != lock["bytes"] or sha256(payload) != lock["sha256"]:
        raise AssertionError(f"locked input drift: {lock_id}")
    if "lines" in lock and len(payload.decode("utf-8").splitlines()) != lock["lines"]:
        raise AssertionError(f"locked input line drift: {lock_id}")
    return payload


@lru_cache(maxsize=None)
def read_json_locked(lock_id: str) -> dict[str, Any]:
    value = json.loads(read_locked(lock_id).decode("utf-8"))
    if not isinstance(value, dict):
        raise AssertionError(f"locked JSON is not an object: {lock_id}")
    return value


def _safe_runtime_scripts_dir(repo_root: Path) -> Path:
    if not repo_root.is_absolute():
        raise AssertionError("runtime repo root must be absolute")
    root = repo_root.resolve(strict=True)
    scripts = (root / "scripts").resolve(strict=True)
    if scripts.parent != root or scripts.name != "scripts" or scripts.is_symlink() or not scripts.is_dir():
        raise AssertionError("runtime scripts directory is not exact ordinary repo/scripts")
    return scripts


def read_runtime_manifests(repo_root: Path) -> dict[str, dict[str, Any]]:
    scripts = _safe_runtime_scripts_dir(repo_root)
    result: dict[str, dict[str, Any]] = {}
    for lock_id, lock in RUNTIME_MANIFEST_LOCKS.items():
        name = lock["name"]
        if Path(name).name != name or "/" in name or "\\" in name or ".." in name:
            raise AssertionError(f"unsafe runtime manifest name: {name}")
        path = scripts / name
        if path.is_symlink() or not path.is_file() or path.resolve(strict=True).parent != scripts:
            raise AssertionError(f"runtime manifest is not exact scripts file: {name}")
        payload = path.read_bytes()
        if len(payload) != lock["bytes"] or sha256(payload) != lock["sha256"]:
            raise AssertionError(f"runtime manifest lock mismatch: {lock_id}")
        value = json.loads(payload)
        if not isinstance(value, dict):
            raise AssertionError(f"runtime manifest is not JSON object: {lock_id}")
        result[lock_id] = value
    return result


@lru_cache(maxsize=None)
def declaration_regions(text: str) -> tuple[tuple[int, str, int, int], ...]:
    matches = list(DECL_RE.finditer(text))
    return tuple(
        (index, match.group(1), match.start(), matches[index + 1].start() if index + 1 < len(matches) else len(text))
        for index, match in enumerate(matches)
    )


def raw_header(region: str) -> str:
    cuts = [point for point in (region.find(":= by"), region.find(":="), region.find(" where\n")) if point >= 0]
    return region if not cuts else region[: min(cuts)]


def owner_region(text: str, owner_index: int, owner_name: str) -> str:
    regions = declaration_regions(text)
    if len(regions) != DECLARATION_COUNT:
        raise AssertionError(f"declaration count {len(regions)} != {DECLARATION_COUNT}")
    index, name, start, end = regions[owner_index]
    if index != owner_index or name != owner_name:
        raise AssertionError(f"owner mismatch at {owner_index}: {name} != {owner_name}")
    return text[start:end]


@lru_cache(maxsize=None)
def comments_and_attributes(text: str) -> tuple[list[str], list[str]]:
    comments: list[str] = []
    attributes: list[str] = []
    i = 0
    in_string = False
    escaped = False
    while i < len(text):
        if in_string:
            if escaped:
                escaped = False
            elif text[i] == "\\":
                escaped = True
            elif text[i] == '"':
                in_string = False
            i += 1
            continue
        if text[i] == '"':
            in_string = True
            i += 1
            continue
        if text.startswith("--", i):
            end = text.find("\n", i)
            end = len(text) if end < 0 else end
            comments.append(text[i:end])
            i = end
            continue
        if text.startswith("/-", i):
            start = i
            depth = 1
            i += 2
            while i < len(text) and depth:
                if text.startswith("/-", i):
                    depth += 1
                    i += 2
                elif text.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            comments.append(text[start:i])
            continue
        if text.startswith("@[", i):
            start = i
            depth = 1
            i += 2
            while i < len(text) and depth:
                if text[i] == "[":
                    depth += 1
                elif text[i] == "]":
                    depth -= 1
                i += 1
            attributes.append(text[start:i])
            continue
        i += 1
    return comments, attributes


@lru_cache(maxsize=None)
def strip_noncode(text: str) -> str:
    out: list[str] = []
    i = 0
    in_string = False
    escaped = False
    block_depth = 0
    while i < len(text):
        if block_depth:
            if text.startswith("/-", i):
                block_depth += 1
                i += 2
            elif text.startswith("-/", i):
                block_depth -= 1
                i += 2
            else:
                i += 1
            out.append(" ")
            continue
        if in_string:
            if escaped:
                escaped = False
            elif text[i] == "\\":
                escaped = True
            elif text[i] == '"':
                in_string = False
            out.append(" ")
            i += 1
            continue
        if text.startswith("--", i):
            end = text.find("\n", i)
            end = len(text) if end < 0 else end
            out.append(" " * (end - i))
            i = end
            continue
        if text.startswith("/-", i):
            block_depth = 1
            out.append("  ")
            i += 2
            continue
        if text[i] == '"':
            in_string = True
            out.append(" ")
            i += 1
            continue
        out.append(text[i])
        i += 1
    return "".join(out)


@lru_cache(maxsize=None)
def trust_counts(text: str) -> dict[str, int]:
    code = strip_noncode(text)
    return {token: len(re.findall(rf"(?<![A-Za-z0-9_.]){re.escape(token)}(?![A-Za-z0-9_.])", code)) for token in TRUST_TOKENS}


@lru_cache(maxsize=None)
def heartbeat_counts(text: str) -> dict[str, int]:
    code = strip_noncode(text)
    return {
        "token_count": len(re.findall(r"\bmaxHeartbeats\b", code)),
        "set_option_count": len(re.findall(r"\bset_option\s+maxHeartbeats\b", code)),
    }


@dataclass(frozen=True)
class Operation:
    operation_id: str
    component_id: str
    owner_index: int
    owner_name: str
    old: str
    new: str
    old_sha256: str
    new_sha256: str
    old_bytes: int
    new_bytes: int
    counts: dict[str, int]


def _v63_operation(manifest: dict[str, Any], repair_id: str, operation_id: str, component_id: str) -> Operation:
    repairs = [row for row in manifest["repairs"] if row["id"] == repair_id]
    if len(repairs) != 1:
        raise AssertionError(f"repair lookup failed: {repair_id}")
    repair = repairs[0]
    operations = [row for row in repair["operations"] if row["id"] == operation_id]
    if len(operations) != 1:
        raise AssertionError(f"operation lookup failed: {operation_id}")
    row = operations[0]
    return Operation(
        operation_id=row["id"], component_id=component_id,
        owner_index=repair["owner"]["declaration_index"],
        owner_name=repair["owner"]["declaration_name"],
        old=row["old"], new=row["new"], old_sha256=row["old_sha256"],
        new_sha256=row["new_sha256"], old_bytes=row["old_bytes"],
        new_bytes=row["new_bytes"], counts=row["counts"],
    )


def _f_followup_operation(manifest: dict[str, Any], variant_id: str, component_id: str) -> Operation:
    variants = [row for row in manifest["variants"] if row["variant_id"] == variant_id]
    if len(variants) != 1 or len(variants[0]["transitions"]) != 1 or len(variants[0]["transitions"][0]["steps"]) != 1:
        raise AssertionError(f"F follow-up variant shape mismatch: {variant_id}")
    variant = variants[0]
    row = variant["transitions"][0]["steps"][0]
    return Operation(
        operation_id=row["step_id"], component_id=component_id,
        owner_index=variant["owner"]["declaration_index"],
        owner_name=variant["owner"]["declaration"],
        old=row["old"], new=row["new"], old_sha256=row["old_sha256"],
        new_sha256=row["new_sha256"], old_bytes=row["old_bytes"],
        new_bytes=row["new_bytes"], counts=row["counts"],
    )


def _w_followup_operation(manifest: dict[str, Any], variant_id: str, component_id: str) -> Operation:
    variants = [row for row in manifest["variants"] if row["variant_id"] == variant_id]
    if len(variants) != 1:
        raise AssertionError(f"W follow-up variant lookup failed: {variant_id}")
    variant = variants[0]
    row = variant["operation"]
    return Operation(
        operation_id=row["operation_id"], component_id=component_id,
        owner_index=4017, owner_name="discriminantHardStageOperator_eq_weightedHard",
        old=row["old"], new=row["new"], old_sha256=row["old_sha256"],
        new_sha256=row["new_sha256"], old_bytes=row["old_bytes"],
        new_bytes=row["new_bytes"], counts=row["counts"],
    )


def _operations_from_manifests(loaded: dict[str, dict[str, Any]]) -> dict[str, list[Operation]]:
    manifests = {key: loaded[key] for key in (
        "v63_f3930_manifest", "v63_f3933_manifest", "v63_w4017_manifest")}
    f_followup = loaded["f_followup_manifest"]
    w_followup = loaded["w4017_followup_manifest"]
    result: dict[str, list[Operation]] = {}
    for component_id, spec in COMPONENTS.items():
        rows: list[Operation] = []
        for manifest_id, repair_id, operation_id in spec.get("operation_refs", []):
            rows.append(_v63_operation(manifests[manifest_id], repair_id, operation_id, component_id))
        if "variant_id" in spec:
            if component_id.startswith("v64_f"):
                rows.append(_f_followup_operation(f_followup, spec["variant_id"], component_id))
            else:
                rows.append(_w_followup_operation(w_followup, spec["variant_id"], component_id))
        if not rows or any(row.owner_index != spec["owner_index"] for row in rows):
            raise AssertionError(f"component operation mismatch: {component_id}")
        result[component_id] = rows
    return result


@lru_cache(maxsize=1)
def load_static_operations() -> dict[str, list[Operation]]:
    if not STATIC_LAYOUT:
        raise AssertionError("static operation loading forbidden in promoted runtime")
    loaded = {key: read_json_locked(key) for key in RUNTIME_MANIFEST_LOCKS}
    return _operations_from_manifests(loaded)


def load_runtime_operations(repo_root: Path) -> dict[str, list[Operation]]:
    return _operations_from_manifests(read_runtime_manifests(repo_root))


@lru_cache(maxsize=1)
def validate_input_semantics() -> int:
    for lock_id in INPUT_LOCKS:
        read_locked(lock_id)
    if read_json_locked("v62_ready").get("status") != "READY_V61_EIGHT_ARTIFACTS_EXACT_LOCKED":
        raise AssertionError("v62 READY authority status mismatch")
    selection = read_json_locked("v63_selection_ready")
    if selection.get("status") != "READY" or selection.get("variant_order")[-2:] != ["w4017_full", "combined_best"]:
        raise AssertionError("v63 READY selection mismatch")
    final_audit = read_json_locked("v63_final_audit")
    if final_audit.get("status") != "PASS_EXACT_ELEVEN_ARTIFACTS_V64_HYDRATED_FA_NONZERO":
        raise AssertionError("v63 terminal audit status mismatch")
    ready = read_json_locked("v64_ready_inputs")
    if ready.get("status") != "READY_V63_ELEVEN_ARTIFACTS_EXACT_LOCKED" or not ready.get("direct_lean_results_present"):
        raise AssertionError("v64 hydrated READY mismatch")
    ranking_a = read_json_locked("v64_ranking_a")
    ranking_b = read_json_locked("v64_ranking_b")
    if ranking_a != ranking_b or ranking_a.get("winner") != "w4017_full" or ranking_a.get("winner_clean"):
        raise AssertionError("v64 ranking authority mismatch")
    if read_locked("v64_queues_a") != read_locked("v64_queues_b"):
        raise AssertionError("v64 queue replay mismatch")
    w_result = read_json_locked("w4017_followup_result")
    if w_result.get("variant_order") != [
        "idx4017_after_full_literal_graph_base_simp", "idx4017_after_full_literal_rfl"
    ] or w_result.get("direct_lean_verified") or w_result.get("clean_claimed"):
        raise AssertionError("W package result mismatch")
    f_result = read_json_locked("f_followup_result")
    expected_composites = {
        "f3930_fieldsimp_f3933_fallback_inv_calc": "12b5a0e8e359461a8f492c5acefb47a17a31fae6a89fbf52ff8b127e5a99d634",
        "f3930_explicit_cancel_f3933_fallback_inv_calc": "23a4c5e517aa26cda065f98fa169342105f10cb132089b1293b0f54826e5488d",
    }
    if {key: value["sha256"] for key, value in f_result["composite_candidate_locks"].items()} != expected_composites:
        raise AssertionError("F package composite locks mismatch")
    if f_result.get("direct_lean_verified") or f_result.get("clean_claimed"):
        raise AssertionError("F package success claim forbidden")
    load_static_operations()
    return len(INPUT_LOCKS) + 11


def _apply_operation(text: str, operation: Operation) -> tuple[str, dict[str, Any]]:
    old = operation.old
    new = operation.new
    if sha256(old.encode()) != operation.old_sha256 or len(old.encode()) != operation.old_bytes:
        raise AssertionError(f"OLD lock mismatch: {operation.operation_id}")
    if sha256(new.encode()) != operation.new_sha256 or len(new.encode()) != operation.new_bytes:
        raise AssertionError(f"NEW lock mismatch: {operation.operation_id}")
    owner_before = owner_region(text, operation.owner_index, operation.owner_name)
    observed_before = {
        "old_global_before": text.count(old),
        "old_owner_before": owner_before.count(old),
        "new_global_before": text.count(new),
        "new_owner_before": owner_before.count(new),
    }
    expected_before = {key: operation.counts[key] for key in observed_before}
    if observed_before != expected_before:
        raise AssertionError(f"before counts mismatch: {operation.operation_id}: {observed_before} != {expected_before}")
    candidate = text.replace(old, new, 1)
    owner_after = owner_region(candidate, operation.owner_index, operation.owner_name)
    observed_after = {
        "old_global_after": candidate.count(old),
        "old_owner_after": owner_after.count(old),
        "new_global_after": candidate.count(new),
        "new_owner_after": owner_after.count(new),
    }
    expected_after = {key: operation.counts[key] for key in observed_after}
    if observed_after != expected_after:
        raise AssertionError(f"after counts mismatch: {operation.operation_id}: {observed_after} != {expected_after}")
    if candidate.replace(new, old, 1) != text:
        raise AssertionError(f"reverse replay mismatch: {operation.operation_id}")
    return candidate, {
        "operation_id": operation.operation_id,
        "component_id": operation.component_id,
        "owner_index": operation.owner_index,
        "owner_name": operation.owner_name,
        "old_sha256": operation.old_sha256,
        "old_bytes": operation.old_bytes,
        "new_sha256": operation.new_sha256,
        "new_bytes": operation.new_bytes,
        "counts": {**observed_before, **observed_after},
        "reverse_replay_exact": True,
    }


def _component_order(component_ids: Iterable[str]) -> list[str]:
    requested = list(component_ids)
    if len(requested) != len(set(requested)):
        raise AssertionError("duplicate component")
    selected = set(requested)
    for component_id in requested:
        if component_id not in COMPONENTS:
            raise AssertionError(f"unknown component: {component_id}")
        missing = set(COMPONENTS[component_id]["depends_on"]) - selected
        if missing:
            raise AssertionError(f"missing component dependency: {component_id}: {sorted(missing)}")
    return sorted(requested, key=lambda value: (COMPONENTS[value]["owner_index"], requested.index(value)))


def _invariants(base: str, candidate: str, changed_indices: list[int]) -> dict[str, Any]:
    base_regions = declaration_regions(base)
    candidate_regions = declaration_regions(candidate)
    if len(base_regions) != DECLARATION_COUNT or len(candidate_regions) != DECLARATION_COUNT:
        raise AssertionError("declaration count mismatch")
    base_names = [row[1] for row in base_regions]
    candidate_names = [row[1] for row in candidate_regions]
    if candidate_names != base_names:
        raise AssertionError("declaration order/name mismatch")
    base_headers: list[str] = []
    candidate_headers: list[str] = []
    actually_changed: list[int] = []
    for index in range(DECLARATION_COUNT):
        _, _, bs, be = base_regions[index]
        _, _, cs, ce = candidate_regions[index]
        before = base[bs:be]
        after = candidate[cs:ce]
        base_headers.append(raw_header(before))
        candidate_headers.append(raw_header(after))
        if before != after:
            actually_changed.append(index)
    if base_headers != candidate_headers:
        raise AssertionError("header/statement drift")
    if actually_changed != changed_indices:
        raise AssertionError(f"changed owner set mismatch: {actually_changed} != {changed_indices}")
    if comments_and_attributes(base) != comments_and_attributes(candidate):
        raise AssertionError("comment/attribute drift")
    if trust_counts(base) != TRUST_ZERO or trust_counts(candidate) != TRUST_ZERO:
        raise AssertionError("trust-six drift")
    if heartbeat_counts(base) != {"token_count": 8, "set_option_count": 8}:
        raise AssertionError("base heartbeat mismatch")
    if heartbeat_counts(candidate) != {"token_count": 8, "set_option_count": 8}:
        raise AssertionError("candidate heartbeat mismatch")
    owner_heartbeats: dict[str, dict[str, int]] = {}
    for index in changed_indices:
        name = base_regions[index][1]
        before = owner_region(base, index, name)
        after = owner_region(candidate, index, name)
        if heartbeat_counts(before) != {"token_count": 0, "set_option_count": 0}:
            raise AssertionError(f"base owner heartbeat mismatch: {index}")
        if heartbeat_counts(after) != {"token_count": 0, "set_option_count": 0}:
            raise AssertionError(f"candidate owner heartbeat mismatch: {index}")
        owner_heartbeats[str(index)] = {"token_count": 0, "set_option_count": 0}
    return {
        "declaration_count": DECLARATION_COUNT,
        "changed_declaration_indices": changed_indices,
        "headers_statements_order_identical": True,
        "comments_identical": True,
        "attributes_identical": True,
        "outside_changed_owners_byte_identical": True,
        "trust_six_before": TRUST_ZERO,
        "trust_six_after": TRUST_ZERO,
        "global_maxHeartbeats_before": {"token_count": 8, "set_option_count": 8},
        "global_maxHeartbeats_after": {"token_count": 8, "set_option_count": 8},
        "changed_owner_maxHeartbeats": owner_heartbeats,
        "source_moves": 0,
        "imports_options_helpers_added": False,
        "body_only": True,
    }


def _validate_authority_source(payload: bytes) -> str:
    lock = INPUT_LOCKS["v62_source"]
    if len(payload) != lock["bytes"] or sha256(payload) != lock["sha256"]:
        raise AssertionError("authority source SHA/bytes mismatch")
    text = payload.decode("utf-8")
    if len(text.splitlines()) != lock["lines"]:
        raise AssertionError("authority source line mismatch")
    if len(declaration_regions(text)) != DECLARATION_COUNT:
        raise AssertionError("authority source declaration mismatch")
    return text


def compose_lane(
    lane: str,
    *,
    authority_source: bytes | None = None,
    repo_root: Path | None = None,
) -> tuple[bytes, dict[str, Any]]:
    if lane not in LANE_COMPONENTS:
        raise AssertionError(f"unknown lane: {lane}")
    if authority_source is None:
        if repo_root is not None:
            raise AssertionError("repo_root without authority source is forbidden")
        validate_input_semantics()
        base_bytes = read_locked("v62_source")
        operations_by_component = load_static_operations()
    else:
        if repo_root is None:
            raise AssertionError("runtime repo root is required with authority source")
        base_bytes = authority_source
        operations_by_component = load_runtime_operations(repo_root)
    base = _validate_authority_source(base_bytes)
    text = base
    operation_audit: list[dict[str, Any]] = []
    component_order = _component_order(LANE_COMPONENTS[lane])
    for component_id in component_order:
        for operation in operations_by_component[component_id]:
            text, row = _apply_operation(text, operation)
            operation_audit.append(row)
    changed_indices = sorted({row["owner_index"] for row in operation_audit})
    invariants = _invariants(base, text, changed_indices)
    payload = text.encode("utf-8")
    audit = {
        "schema": "fa-v65-static-materialization-audit-v1",
        "status": "STATIC_EXACT_DIRECT_LEAN_UNVERIFIED",
        "lane": lane,
        "composition_mode": "EXACT_FROM_OFFICIAL_V62_AUTHORITY_NONCUMULATIVE",
        "authority": {key: INPUT_LOCKS["v62_source"][key] for key in ("sha256", "bytes", "lines")},
        "components": component_order,
        "operations": operation_audit,
        "candidate": {
            "sha256": sha256(payload),
            "bytes": len(payload),
            "lines": len(text.splitlines()),
            "declaration_count": DECLARATION_COUNT,
        },
        "invariants": invariants,
        "direct_lean_verified": False,
        "clean_claimed": False,
        "promotion_allowed": False,
        "runtime_fallback_used": False,
    }
    if audit["candidate"] != EXPECTED_CANDIDATES[lane]:
        raise AssertionError(f"embedded candidate lock mismatch: {lane}")
    return payload, audit


def compose_all() -> tuple[dict[str, bytes], dict[str, dict[str, Any]]]:
    payloads: dict[str, bytes] = {}
    audits: dict[str, dict[str, Any]] = {}
    for lane in LANE_ORDER:
        payloads[lane], audits[lane] = compose_lane(lane)
    digests = [audits[lane]["candidate"]["sha256"] for lane in LANE_ORDER]
    if len(digests) != len(set(digests)):
        raise AssertionError("ten candidate outputs are not distinct")
    if audits["winner_baseline"]["candidate"]["sha256"] != INPUT_LOCKS["v63_winner_candidate"]["sha256"]:
        raise AssertionError("winner baseline does not reproduce official v63 winner")
    if payloads["winner_baseline"] != read_locked("v63_winner_candidate"):
        raise AssertionError("winner baseline bytes differ from official v63 winner")
    f_result = read_json_locked("f_followup_result")["composite_candidate_locks"]
    expected = {
        "f_field_f3933": f_result["f3930_fieldsimp_f3933_fallback_inv_calc"],
        "f_explicit_f3933": f_result["f3930_explicit_cancel_f3933_fallback_inv_calc"],
    }
    for lane, lock in expected.items():
        expected_lock = {key: lock[key] for key in ("sha256", "bytes", "lines", "declaration_count")}
        if audits[lane]["candidate"] != expected_lock:
            raise AssertionError(f"composite package lock mismatch: {lane}")
    w_result = read_json_locked("w4017_followup_result")["candidate_locks"]
    for lane, variant_id in {
        "w4017_primary": "idx4017_after_full_literal_graph_base_simp",
        "w4017_rfl_fallback": "idx4017_after_full_literal_rfl",
    }.items():
        expected_lock = {key: w_result[variant_id][key] for key in ("sha256", "bytes", "lines")}
        actual_lock = {key: audits[lane]["candidate"][key] for key in ("sha256", "bytes", "lines")}
        if actual_lock != expected_lock:
            raise AssertionError(f"W package lock mismatch: {lane}")
    return payloads, audits


def lane_registry() -> dict[str, Any]:
    return {
        "schema": "fa-v65-exact-ten-lane-static-registry-v1",
        "status": "PENDING_DIRECT_LEAN_UNVERIFIED",
        "authority_source": {**INPUT_LOCKS["v62_source"], "declaration_count": DECLARATION_COUNT},
        "composition_mode": "EXACT_FROM_OFFICIAL_V62_AUTHORITY_NONCUMULATIVE",
        "variant_order": LANE_ORDER,
        "variants": [
            {
                "name": lane,
                "components": LANE_COMPONENTS[lane],
                "expected_candidate": EXPECTED_CANDIDATES[lane],
                "changed_declaration_indices": sorted({COMPONENTS[row]["owner_index"] for row in LANE_COMPONENTS[lane]}),
                "status": "STATIC_LOCKED_DIRECT_LEAN_REQUIRED",
            }
            for lane in LANE_ORDER
        ],
        "distinct_candidate_outputs": True,
        "direct_lean_verified": False,
        "clean_claimed": False,
        "promotion_allowed": False,
    }


def validate_authority_lock(authority: dict[str, Any]) -> None:
    expected_keys = {
        "schema", "status", "repository", "branch", "v63_run_id", "v63_head_sha",
        "toolchain", "official_v62_source", "v62_authority_artifact", "input_locks",
        "independent_cross_audit", "v63_winner", "constraints", "direct_lean_verified",
        "clean_claimed", "promotion_allowed",
    }
    if set(authority) != expected_keys:
        raise AssertionError("authority exact top-level key set mismatch")
    if authority["schema"] != "fa-v65-v62-core-and-v64-repair-authority-lock-v1" or authority["status"] != "STATIC_EXACT_DIRECT_LEAN_UNVERIFIED":
        raise AssertionError("authority schema/status mismatch")
    if authority["repository"] != "leegahuyn/mathlib4" or authority["branch"] != "codex/fa-exclusive-focus-20260814" or authority["v63_run_id"] != 31871876992 or authority["v63_head_sha"] != "336899ee618c4db5e88cf5c41b3a2195c3d61ba3":
        raise AssertionError("authority remote identity mismatch")
    if authority["toolchain"] != {"content": TOOLCHAIN, "sha256": TOOLCHAIN_SHA256, "bytes": 29, "terminal_lf": True}:
        raise AssertionError("authority toolchain mismatch")
    expected_source = {**INPUT_LOCKS["v62_source"], "declaration_count": 4416}
    if authority["official_v62_source"] != expected_source:
        raise AssertionError("authority source lock mismatch")
    if authority["v62_authority_artifact"] != {"id": 9241529792, "zip_sha256": "799b754b01ef17bd8326ad0d9554f6fc1e27c42d01c070d3b2271816ae248333", "zip_bytes": 1684227, "flat_member_count": 48}:
        raise AssertionError("authority artifact lock mismatch")
    if authority["input_locks"] != INPUT_LOCKS:
        raise AssertionError("authority input lock ledger mismatch")
    if authority["independent_cross_audit"] != {"primary": CROSS_AUDIT_LOCK, "files": CROSS_AUDIT_FILES}:
        raise AssertionError("authority independent cross-audit ledger mismatch")
    expected_winner = {"variant": "w4017_full", **{key: INPUT_LOCKS["v63_winner_candidate"][key] for key in ("sha256", "bytes", "lines")}, "FA_exit": 1, "errors": 8, "owners": 5, "signatures": 5, "warnings": 463, "clean": False}
    if authority["v63_winner"] != expected_winner:
        raise AssertionError("authority v63 winner mismatch")
    expected_constraints = {"composition": "EXACT_FROM_OFFICIAL_V62_AUTHORITY_NONCUMULATIVE", "declaration_count": 4416, "trust_six_zero": True, "global_maxHeartbeats": {"token_count": 8, "set_option_count": 8}, "changed_owner_maxHeartbeats": {"token_count": 0, "set_option_count": 0}, "source_moves": 0, "runtime_fallback_allowed": False}
    if authority["constraints"] != expected_constraints or authority["direct_lean_verified"] is not False or authority["clean_claimed"] is not False or authority["promotion_allowed"] is not False:
        raise AssertionError("authority invariant/claim mismatch")


def validate_dependency_graph(graph: dict[str, Any], *, require_ready: bool) -> None:
    expected_keys = {
        "schema", "status", "authority_source_sha256", "composition_mode",
        "component_order", "components", "conflict_sets", "lane_order", "lanes",
        "compile_contract", "producer_gates", "hidden_cumulative_parentage",
        "direct_lean_verified", "clean_claimed",
    }
    if set(graph) != expected_keys:
        raise AssertionError("dependency graph exact top-level key set mismatch")
    expected_status = "READY_DIRECT_LEAN_REQUIRED" if require_ready else "PENDING_DIRECT_LEAN_UNVERIFIED"
    if graph["schema"] != "fa-v65-exact-ten-lane-dependency-graph-v1" or graph["status"] != expected_status:
        raise AssertionError("dependency graph schema/status mismatch")
    expected_components = [
        {"id": key, **value, "status": "STATIC_LOCKED_DIRECT_LEAN_REQUIRED"}
        for key, value in COMPONENTS.items()
    ]
    expected_compile = {"job_count": 10, "exactly_one_independent_job_per_lane": True, "max_parallel": 10, "chain": ["M2", "M2A", "FA2000"], "individual_axes_may_not_be_omitted": True, "artifacts_independent": True}
    if graph["authority_source_sha256"] != INPUT_LOCKS["v62_source"]["sha256"] or graph["composition_mode"] != "EXACT_FROM_OFFICIAL_V62_AUTHORITY_NONCUMULATIVE" or graph["component_order"] != list(COMPONENTS) or graph["components"] != expected_components:
        raise AssertionError("dependency graph component contract mismatch")
    if graph["conflict_sets"] != [["v64_f3930_field", "v64_f3930_explicit"], ["v64_w4017_primary", "v64_w4017_rfl"]] or graph["lane_order"] != LANE_ORDER or graph["lanes"] != lane_registry()["variants"]:
        raise AssertionError("dependency graph lane/conflict contract mismatch")
    if graph["compile_contract"] != expected_compile or graph["producer_gates"] != {"idx4019": "DEFERRED_UNTIL_IDX4017_PRODUCER_CLEAN", "idx4020": "DEFERRED_UNTIL_IDX4019_PRODUCER_CLEAN", "repair_components_present": False}:
        raise AssertionError("dependency graph compile/producer contract mismatch")
    if graph["hidden_cumulative_parentage"] is not False or graph["direct_lean_verified"] is not False or graph["clean_claimed"] is not False:
        raise AssertionError("dependency graph claim mismatch")


def validate_runtime_support(repo_root: Path, selection: dict[str, Any], *, require_ready: bool) -> dict[str, Any]:
    scripts = _safe_runtime_scripts_dir(repo_root)
    results: dict[str, Any] = {}
    for label, selection_key, expected_name in (
        ("authority", "authority", "fa_v65_authority-lock.json"),
        ("dependency_graph", "dependency_graph", "fa_v65_dependency-graph.json"),
    ):
        declared = selection[selection_key]
        if declared["runtime_path"] != f"scripts/{expected_name}":
            raise AssertionError(f"unsafe runtime support path: {label}")
        path = scripts / expected_name
        if path.is_symlink() or not path.is_file() or path.resolve(strict=True).parent != scripts:
            raise AssertionError(f"runtime support not exact scripts file: {label}")
        payload = path.read_bytes()
        if sha256(payload) != declared["sha256"] or len(payload) != declared["bytes"]:
            raise AssertionError(f"runtime support declared lock mismatch: {label}")
        value = json.loads(payload)
        if label == "authority":
            validate_authority_lock(value)
        else:
            validate_dependency_graph(value, require_ready=require_ready)
        results[label] = {"sha256": sha256(payload), "bytes": len(payload)}
    read_runtime_manifests(repo_root)
    results["runtime_manifest_count"] = len(RUNTIME_MANIFEST_LOCKS)
    return results


def validate_selection(selection: dict[str, Any], *, require_ready: bool) -> None:
    expected_top_keys = {
        "schema", "status", "note", "authority", "dependency_graph",
        "independent_cross_audit", "composition_mode", "variant_order", "variants",
        "artifact_contract", "compile_contract", "activation", "blockers", "constraints",
        "direct_lean_verified", "clean_claimed", "promotion_allowed",
    }
    if set(selection) != expected_top_keys:
        raise AssertionError("selection exact top-level key set mismatch")
    expected_status = "READY" if require_ready else "PENDING"
    if selection.get("schema") != "fa-v65-direct-bounded-selection-v1" or selection.get("status") != expected_status:
        raise AssertionError("selection status/schema mismatch")
    if selection.get("variant_order") != LANE_ORDER or len(selection.get("variants", [])) != 10:
        raise AssertionError("selection lane order/count mismatch")
    registry = lane_registry()
    expected_row_status = "READY" if require_ready else "STATIC_LOCKED_DIRECT_LEAN_REQUIRED"
    expected_rows = [
        {**row, "status": expected_row_status} for row in registry["variants"]
    ]
    if selection["variants"] != expected_rows:
        raise AssertionError("selection exact ordered variant rows mismatch")
    if selection.get("composition_mode") != "EXACT_FROM_OFFICIAL_V62_AUTHORITY_NONCUMULATIVE":
        raise AssertionError("selection composition mode mismatch")
    if selection.get("direct_lean_verified") is not False or selection.get("clean_claimed") is not False or selection.get("promotion_allowed") is not False:
        raise AssertionError("selection success claim forbidden")
    if not isinstance(selection["note"], str) or "Lean" not in selection["note"] or "clean" not in selection["note"]:
        raise AssertionError("selection note contract mismatch")
    authority = selection["authority"]
    if set(authority) != {"sha256", "bytes", "runtime_path", "schema"} or authority["runtime_path"] != "scripts/fa_v65_authority-lock.json" or authority["schema"] != "fa-v65-v62-core-and-v64-repair-authority-lock-v1" or not re.fullmatch(r"[0-9a-f]{64}", authority["sha256"]) or not isinstance(authority["bytes"], int) or authority["bytes"] <= 0:
        raise AssertionError("selection authority lock contract mismatch")
    dependency = selection["dependency_graph"]
    if set(dependency) != {"sha256", "bytes", "runtime_path", "schema"} or dependency["runtime_path"] != "scripts/fa_v65_dependency-graph.json" or dependency["schema"] != "fa-v65-exact-ten-lane-dependency-graph-v1" or not re.fullmatch(r"[0-9a-f]{64}", dependency["sha256"]) or not isinstance(dependency["bytes"], int) or dependency["bytes"] <= 0:
        raise AssertionError("selection dependency graph lock contract mismatch")
    if selection["independent_cross_audit"] != CROSS_AUDIT_LOCK:
        raise AssertionError("selection independent cross-audit lock mismatch")
    expected_artifact_contract = {
        "schema": "fa-v65-exact-result-artifact-v1",
        "member_count": 48,
        "flat_members_only": True,
        "duplicate_members_allowed": False,
        "member_names": RESULT_ARTIFACT_MEMBERS,
        "base_authority_copy_count": 6,
        "base_authority_copies": BASE_AUTHORITY_COPIES,
        "v62_authority_zip_sha256": "799b754b01ef17bd8326ad0d9554f6fc1e27c42d01c070d3b2271816ae248333",
        "v62_authority_zip_bytes": 1684227,
        "v62_authority_member_count": 48,
        "result_inventory_enforced_by_final_gate": True,
        "runtime_evidence_fallback_allowed": False,
    }
    if selection["artifact_contract"] != expected_artifact_contract:
        raise AssertionError("selection artifact contract mismatch")
    if selection["compile_contract"] != COMPILE_CONTRACT:
        raise AssertionError("selection compile contract mismatch")
    if selection["constraints"] != SELECTION_CONSTRAINTS:
        raise AssertionError("selection constraints mismatch")
    expected_activation = {key: require_ready for key in ACTIVATION_KEYS}
    if selection["activation"] != expected_activation:
        raise AssertionError("selection exact activation contract mismatch")
    if require_ready:
        if selection["blockers"] != []:
            raise AssertionError("READY selection activation mismatch")
    else:
        if selection["blockers"] != PENDING_BLOCKERS:
            raise AssertionError("PENDING selection must remain fail-closed")
