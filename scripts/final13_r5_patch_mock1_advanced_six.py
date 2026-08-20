#!/usr/bin/env python3
"""Patch only the six VERIFIED residual Mock1_Advanced proof bodies.

The input must be the immutable 6-error authority source. Statements and all
other declarations are byte-preserved. The first five proofs use the locally
verified explicit `List.range 11` reduction; the sixth closes the already
normalized scalar identity.
"""
from __future__ import annotations

import argparse
import hashlib
from pathlib import Path

EXPECTED_INPUT_SHA256 = (
    "d2cf9f101e04d58e0fd87e62d1f102b8eb910d4cc5e3e9d2b903e5c7df0f98f2"
)
RANGE11 = "[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]"
HRANGE = f"  have hrange : List.range 11 = {RANGE11} := by rfl\n"

PROOFS = {
    "advanced_claims_ii_paper_t1t2_full_solution_table": (
        "by\n"
        + HRANGE
        + "  norm_num [AdvancedClaimsIIPaperT1T2FullSolution,\n"
          "    AdvancedClaimsIIPaperT1T2FullDepth, referenceMock1MList,\n"
          "    AdvancedClaimsIIRatCoordinateVector, hrange]"
    ),
    "advanced_claims_ii_paper_t1t2_full_matvec": (
        "by\n"
        "  rw [advanced_claims_ii_paper_t1t2_full_matrix_formula,\n"
        "    advanced_claims_ii_paper_t1t2_full_solution_table,\n"
        "    advanced_claims_ii_paper_t1t2_full_rhs_table]\n"
        + HRANGE
        + "  norm_num [MatVecRat, dotRat, AdvancedClaimsIISignedIdentityMatrix,\n"
          "    AdvancedClaimsIISignedIdentityRow, AdvancedClaimsIIRatCoordinateVector,\n"
          "    hrange]"
    ),
    "advanced_claims_ii_paper_t1t2_full_pair_targets": (
        "by\n"
        "  rw [advanced_claims_ii_paper_t1t2_full_rhs_table]\n"
        + HRANGE
        + "  norm_num [AdvancedClaimsIISignedPairTargets,\n"
          "    AdvancedClaimsIIPaperT1T2FullPairSolution,\n"
          "    AdvancedClaimsIIPaperT1T2FullDepth, referenceMock1MList, hrange]"
    ),
    "advanced_claims_ii_paper_t1t2_full_pair_flatten": (
        "by\n"
        "  rw [advanced_claims_ii_paper_t1t2_full_solution_table]\n"
        + HRANGE
        + "  norm_num [AdvancedClaimsIIFlattenSignedPairs,\n"
          "    AdvancedClaimsIIPaperT1T2FullPairSolution,\n"
          "    AdvancedClaimsIIPaperT1T2FullDepth, referenceMock1MList, hrange]"
    ),
    "advanced_claims_ii_paper_t1t2_full_pair_squared_norm": (
        "by\n"
        + HRANGE
        + "  norm_num [AdvancedClaimsIISignedPairSquaredNorm,\n"
          "    AdvancedClaimsIIPaperT1T2FullPairSolution,\n"
          "    AdvancedClaimsIIPaperT1T2FullDepth, referenceMock1MList, hrange]"
    ),
}


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def declaration_span(text: str, name: str) -> tuple[int, int, int]:
    marker = f"theorem {name}"
    start = text.find(marker)
    if start < 0:
        raise ValueError(f"missing declaration: {name}")
    if text.find(marker, start + 1) >= 0:
        raise ValueError(f"duplicate theorem declaration: {name}")
    body = text.find(" := by", start)
    if body < 0:
        raise ValueError(f"missing := by for {name}")
    next_decl_candidates = [
        position
        for token in ("\ntheorem ", "\ndef ", "\nstructure ", "\nnamespace ", "\nend ")
        if (position := text.find(token, body + 1)) >= 0
    ]
    if not next_decl_candidates:
        raise ValueError(f"cannot find end of declaration: {name}")
    end = min(next_decl_candidates) + 1
    return start, body + len(" := "), end


def replace_proof(text: str, name: str, proof: str) -> str:
    _start, proof_start, end = declaration_span(text, name)
    old = text[proof_start:end]
    if not old.startswith("by"):
        raise ValueError(f"unexpected proof start for {name}: {old[:40]!r}")
    return text[:proof_start] + proof + "\n\n" + text[end:]


def patch_fixed_shadow(text: str) -> str:
    old = (
        "  fixed_shadow_scale_link := by\n"
        "    change (1 : Rat) =\n"
        "      AdvancedClaimsIIPaperT3BlockSum * (1 : Rat)\n"
        "    rw [advanced_claims_ii_paper_t3_block_sum]\n"
    )
    if text.count(old) != 1:
        raise ValueError("fixed_shadow_scale_link authority body changed or duplicated")
    return text.replace(old, old + "    norm_num\n", 1)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("variant", choices=["hrange-rfl-norm"])
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()

    raw = args.input.read_bytes()
    actual = sha256(raw)
    if actual != EXPECTED_INPUT_SHA256:
        raise SystemExit(
            f"refusing non-authority input: expected {EXPECTED_INPUT_SHA256}, got {actual}"
        )
    text = raw.decode("utf-8")
    for name, proof in PROOFS.items():
        text = replace_proof(text, name, proof)
    text = patch_fixed_shadow(text)

    if "native_decide" in text:
        raise SystemExit("forbidden native_decide remains in candidate")
    if text.count("set_option maxHeartbeats 0"):
        raise SystemExit("forbidden maxHeartbeats=0 bypass remains in candidate")

    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(text, encoding="utf-8")
    output_raw = args.output.read_bytes()
    print(
        f"variant={args.variant}\n"
        f"input_sha256={actual}\n"
        f"output_sha256={sha256(output_raw)}\n"
        f"line_count={len(output_raw.splitlines())}\n"
    )


if __name__ == "__main__":
    main()
