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
SOURCE_SHA256 = "1bcb9a5c18e0dd5ba115541ba806090daf7800ff0324a3db9e1da4d4eb32c1bd"
OLD_FAILED_CANDIDATE_SHA256 = (
    "9cfea40a077d67c29ef99c031a1ef4ae004e73210aa1e02656a50224634f4315"
)
CORRECTED_CANDIDATE_SHA256 = (
    "96587e63714b23a31e01471b6d50942db2058204f8b68f8af357e107ee706484"
)
CORRECTED_CANDIDATE_GIT_BLOB = "64489bb843c5f99077693b0d58e2583e93790f58"
CORRECTED_CANDIDATE_BYTES = 425110
CORRECTED_CANDIDATE_LINES = 9830
SIMPA_LINES = {917, 3972, 4818, 5960}


FULL_REPLACEMENTS = (
    (
        "  simpa [paperClaimInventoryEntry_id] using "
        "paperClaimInventoryEntry_status id",
        "  simp [paperClaimInventoryEntry_id]",
    ),
    (
        "  simpa [reduceRatZModPrimePow] using\n"
        "    ratReduceZModPrimePow_denominator_witness_independent p k "
        "hpprime hk x\n"
        "    (pIntegral_denominator_coprime_prime_pow hpprime hk hx) hden",
        "  simp [reduceRatZModPrimePow]\n\n",
    ),
    (
        "  simpa [MahlerInverseMatrix] using\n"
        "    (Matrix.mul_inv_of_invertible (A := MahlerMatrix N R))",
        "  simp [MahlerInverseMatrix]\n",
    ),
    (
        "  simpa [qParam] using Complex.exp_ne_zero "
        "((2 * Real.pi : ℂ) * Complex.I * (tau : ℂ))",
        "  simp [qParam]",
    ),
)


def load_generic():
    spec = importlib.util.spec_from_file_location("warning_generic", GENERIC)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {GENERIC}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--prepare-only", action="store_true")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    generic = load_generic()
    document = json.loads(MANIFEST.read_text(encoding="utf-8"))
    expected = document["modules"]["Mock1"]
    if expected["source_sha256"] != SOURCE_SHA256:
        raise RuntimeError("Mock1 source profile drifted")
    if expected["candidate_sha256"] != OLD_FAILED_CANDIDATE_SHA256:
        raise RuntimeError("the failed Mock1 candidate profile drifted")

    simpa_edits = [
        edit for edit in expected["edits"] if int(edit["line"]) in SIMPA_LINES
    ]
    if {int(edit["line"]) for edit in simpa_edits} != SIMPA_LINES:
        raise RuntimeError("the four guarded unnecessarySimpa edits drifted")
    if any(
        edit.get("expected") != "simpa"
        or edit.get("replacement") != "simp"
        or edit.get("category") != "unnecessarySimpa"
        for edit in simpa_edits
    ):
        raise RuntimeError("the failed simpa-to-simp edit shapes drifted")

    original_apply = generic.apply_manifest_edits

    def corrected_apply(source: str, edits: list[dict]) -> str:
        ordinary = [
            edit for edit in edits if int(edit["line"]) not in SIMPA_LINES
        ]
        candidate = original_apply(source, ordinary)
        for old, new in FULL_REPLACEMENTS:
            count = candidate.count(old)
            if count != 1:
                raise RuntimeError(
                    "expected one exact full unnecessarySimpa block, "
                    f"found {count}"
                )
            candidate = candidate.replace(old, new, 1)
        return candidate

    generic.apply_manifest_edits = corrected_apply

    derived = copy.deepcopy(document)
    mock1 = derived["modules"]["Mock1"]
    mock1["candidate_sha256"] = CORRECTED_CANDIDATE_SHA256
    mock1["candidate_git_blob_sha1"] = CORRECTED_CANDIDATE_GIT_BLOB
    mock1["candidate_bytes"] = CORRECTED_CANDIDATE_BYTES
    mock1["candidate_lines"] = CORRECTED_CANDIDATE_LINES
    derived_path = args.out.parent / "mock1-warning-followup-manifest.json"
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
        "Mock1",
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
