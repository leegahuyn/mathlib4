#!/usr/bin/env python3
from __future__ import annotations

import argparse
import copy
import importlib.util
import json
import sys
from pathlib import Path


GENERIC = Path(".github/scripts/codex-warning-mechanical-matrix-runner.py")
MANIFEST = Path(".github/scripts/codex-warning-mechanical-edit-manifest.json")
ORIGINAL_SOURCE_SHA256 = (
    "69f0703cc03fd0efde38b9d7018424cc62b724e0afaab7b66e3ccafb4d9f0311"
)
KERNEL_SOURCE_SHA256 = (
    "25eb501aea633b950fc5b7296b5b752aa4ac9c0812ee96fde120f3076e0ca34f"
)
KERNEL_SOURCE_GIT_BLOB = "769c0fa447408ef28d5acf4a151561950f56815e"
KERNEL_SOURCE_BYTES = 4_426_099
KERNEL_SOURCE_LINES = 90_566
INVALID_SIMPA_LINES = {35, 2084}
ZERO_FORBIDDEN = {
    "sorry": 0,
    "admit": 0,
    "new_global_axiom": 0,
    "unsafe": 0,
    "native_decide": 0,
    "Lean.ofReduceBool": 0,
}


VARIANTS = {
    "direct_full": {
        "entropy_finish": (
            "  simp [EntropyGrowth, EntropyModel, exactEntropyCoeff, "
            "log_abs_exp]\n\n\n"
        ),
        "candidate_sha256": (
            "d92aea3bd42b5d4d133311d0965a9409d1ebe4acfbfba2125c2a0d7d945040b1"
        ),
        "candidate_git_blob_sha1": "ce571b3138c2f35a78c90901f4532e37cda08393",
        "candidate_bytes": 4_425_904,
    },
    "direct_trim": {
        "entropy_finish": (
            "  simp [EntropyGrowth, EntropyModel, exactEntropyCoeff]\n\n\n"
        ),
        "candidate_sha256": (
            "8a4d482e7422fa606ea20caf63c88446fe03b82cc5dd2be03bc4b43abf4b6ff0"
        ),
        "candidate_git_blob_sha1": "cfea89dc7dd25197e3379a6e00fdb5bb27620fe9",
        "candidate_bytes": 4_425_891,
    },
}


OLD_IM = "    simpa using tau.im_pos"
NEW_IM = "    simp"
OLD_ENTROPY = """  simpa [EntropyGrowth, EntropyModel, exactEntropyCoeff, log_abs_exp]
    using
      (tendsto_const_nhds :
        Filter.Tendsto (fun _ : Nat => (0 : Real)) Filter.atTop (nhds (0 : Real)))"""


def load_generic():
    spec = importlib.util.spec_from_file_location("warning_generic_m1a", GENERIC)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {GENERIC}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--native-source", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--variant", choices=sorted(VARIANTS), required=True)
    parser.add_argument("--prepare-only", action="store_true")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    generic = load_generic()
    native_source = args.native_source.resolve()
    native_data = native_source.read_bytes()
    if generic.sha256_bytes(native_data) != KERNEL_SOURCE_SHA256:
        raise RuntimeError("the decide +kernel Mock1_Advanced source drifted")
    if generic.git_blob_sha1(native_data) != KERNEL_SOURCE_GIT_BLOB:
        raise RuntimeError("the decide +kernel Git blob identity drifted")

    document = json.loads(MANIFEST.read_text(encoding="utf-8"))
    expected = document["modules"]["Mock1_Advanced"]
    if expected["source_sha256"] != ORIGINAL_SOURCE_SHA256:
        raise RuntimeError("the original Mock1_Advanced warning profile drifted")
    invalid = [
        edit
        for edit in expected["edits"]
        if int(edit["line"]) in INVALID_SIMPA_LINES
    ]
    if {int(edit["line"]) for edit in invalid} != INVALID_SIMPA_LINES:
        raise RuntimeError("the two invalid unnecessarySimpa edits drifted")
    if any(
        edit.get("expected") != "simpa"
        or edit.get("replacement") != "simp"
        or edit.get("category") != "unnecessarySimpa"
        for edit in invalid
    ):
        raise RuntimeError("the invalid simpa-to-simp edit shapes drifted")

    original_apply = generic.apply_manifest_edits
    choice = VARIANTS[args.variant]

    def corrected_apply(source: str, edits: list[dict]) -> str:
        ordinary = [
            edit
            for edit in edits
            if int(edit["line"]) not in INVALID_SIMPA_LINES
        ]
        candidate = original_apply(source, ordinary)
        if candidate.count(OLD_IM) != 1:
            raise RuntimeError("the translateOne proof block drifted")
        if candidate.count(OLD_ENTROPY) != 1:
            raise RuntimeError("the exactEntropyCoeff proof block drifted")
        candidate = candidate.replace(OLD_IM, NEW_IM, 1)
        candidate = candidate.replace(
            OLD_ENTROPY,
            choice["entropy_finish"],
            1,
        )
        return candidate

    generic.apply_manifest_edits = corrected_apply
    generic.resolve_source = lambda _repo, _path, _module: native_source

    derived = copy.deepcopy(document)
    m1a = derived["modules"]["Mock1_Advanced"]
    m1a["source_sha256"] = KERNEL_SOURCE_SHA256
    m1a["source_git_blob_sha1"] = KERNEL_SOURCE_GIT_BLOB
    m1a["source_bytes"] = KERNEL_SOURCE_BYTES
    m1a["source_lines"] = KERNEL_SOURCE_LINES
    m1a["baseline_forbidden_counts"] = ZERO_FORBIDDEN
    m1a["candidate_sha256"] = choice["candidate_sha256"]
    m1a["candidate_git_blob_sha1"] = choice["candidate_git_blob_sha1"]
    m1a["candidate_bytes"] = choice["candidate_bytes"]
    m1a["candidate_lines"] = KERNEL_SOURCE_LINES
    m1a["candidate_forbidden_counts"] = ZERO_FORBIDDEN

    derived_path = args.out.parent / (
        f"mock1-advanced-warning-kernel-{args.variant}-manifest.json"
    )
    derived_path.parent.mkdir(parents=True, exist_ok=True)
    derived_path.write_text(
        json.dumps(derived, ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
    )

    argv = [
        str(GENERIC),
        "--manifest",
        str(derived_path),
        "--module",
        "Mock1_Advanced",
        "--repo-root",
        str(args.repo_root),
        "--out",
        str(args.out),
    ]
    if args.prepare_only:
        argv.append("--prepare-only")
    prior_argv = sys.argv
    try:
        sys.argv = argv
        return generic.main()
    finally:
        sys.argv = prior_argv


if __name__ == "__main__":
    raise SystemExit(main())
