#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import re
import subprocess
import sys
from pathlib import Path

SPT1_BLOB = "ed554b8268e9504281572d0cea27e40d5ba06a19"
MOCK1A_BLOB = "2dc68bb04df549064b41fc318d18ea02d4d40679"
VARIANTS = {
    "norm-defs",
    "simp-norm-defs",
    "unfold-norm",
    "rw-structural",
}

COMMAND_RE = re.compile(
    r"(?m)^(?:(?:noncomputable|private|protected|public|local)\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque|namespace|end)\b"
)

DEFS: dict[str, list[str]] = {
    "advanced_claims_ii_paper_t1t2_full_solution_table": [
        "AdvancedClaimsIIPaperT1T2FullSolution",
        "AdvancedClaimsIIPaperT1T2FullDepth",
        "referenceMock1MList",
        "AdvancedClaimsIIRatCoordinateVector",
    ],
    "advanced_claims_ii_paper_t1t2_full_matvec": [
        "MatVecRat",
        "dotRat",
        "AdvancedClaimsIIPaperT1T2FullMatrix",
        "AdvancedClaimsIIPaperT1T2FullSolution",
        "AdvancedClaimsIIPaperT1T2FullRHS",
        "AdvancedClaimsIIPaperT1T2FullDepth",
        "referenceMock1MList",
        "AdvancedClaimsIISignedIdentityMatrix",
        "AdvancedClaimsIISignedIdentityRow",
        "AdvancedClaimsIIRatCoordinateVector",
    ],
    "advanced_claims_ii_paper_t1t2_full_solution_squared_norm": [
        "AdvancedClaimsIIRatSquaredNorm",
        "AdvancedClaimsIIPaperT1T2FullSolution",
        "AdvancedClaimsIIPaperT1T2FullDepth",
        "referenceMock1MList",
        "AdvancedClaimsIIRatCoordinateVector",
    ],
    "advanced_claims_ii_paper_t1t2_full_rhs_squared_norm": [
        "AdvancedClaimsIIRatSquaredNorm",
        "AdvancedClaimsIIPaperT1T2FullRHS",
        "AdvancedClaimsIIPaperT1T2FullDepth",
        "referenceMock1MList",
        "AdvancedClaimsIIRatCoordinateVector",
    ],
    "advanced_claims_ii_paper_t1t2_full_pair_targets": [
        "AdvancedClaimsIISignedPairTargets",
        "AdvancedClaimsIIPaperT1T2FullPairSolution",
        "AdvancedClaimsIIPaperT1T2FullRHS",
        "AdvancedClaimsIIPaperT1T2FullDepth",
        "referenceMock1MList",
        "AdvancedClaimsIIRatCoordinateVector",
    ],
    "advanced_claims_ii_paper_t1t2_full_pair_flatten": [
        "AdvancedClaimsIIFlattenSignedPairs",
        "AdvancedClaimsIIPaperT1T2FullPairSolution",
        "AdvancedClaimsIIPaperT1T2FullSolution",
        "AdvancedClaimsIIPaperT1T2FullDepth",
        "referenceMock1MList",
        "AdvancedClaimsIIRatCoordinateVector",
    ],
    "advanced_claims_ii_paper_t1t2_full_pair_squared_norm": [
        "AdvancedClaimsIISignedPairSquaredNorm",
        "AdvancedClaimsIIPaperT1T2FullPairSolution",
        "AdvancedClaimsIIPaperT1T2FullDepth",
        "referenceMock1MList",
    ],
    "advanced_claims_ii_appell_lerch_leading_exponent_table": [
        "referenceAdvancedClaimsIIAppellLerchRidgeParameters",
        "referenceAdvancedClaimsIIAppellLerchLeadingExponents",
        "AdvancedClaimsIIAppellLerchTotalExponent",
        "AdvancedClaimsIIAppellLerchBaseExponent",
        "AdvancedClaimsIIAppellLerchRidgeIndex",
    ],
    "advanced_claims_ii_unary_theta_raw_term_table": [
        "referenceAdvancedClaimsIIUnaryThetaRawIndices",
        "referenceAdvancedClaimsIIUnaryThetaRawTerms",
        "AdvancedClaimsIIUnaryThetaRawTerm",
        "AdvancedClaimsIIUnaryThetaQExponent",
        "AdvancedClaimsIIUnaryThetaHalfLatticePoint",
        "AdvancedClaimsIIUnaryThetaCharacteristicA",
    ],
    "advanced_claims_ii_unary_theta_coefficient_one_eighth": [
        "AdvancedClaimsIIUnaryThetaFiniteCoefficientAt",
        "referenceAdvancedClaimsIIUnaryThetaRawIndices",
        "AdvancedClaimsIIUnaryThetaQExponent",
        "AdvancedClaimsIIUnaryThetaHalfLatticePoint",
        "AdvancedClaimsIIUnaryThetaCharacteristicA",
    ],
    "advanced_claims_ii_unary_theta_coefficient_nine_eighths": [
        "AdvancedClaimsIIUnaryThetaFiniteCoefficientAt",
        "referenceAdvancedClaimsIIUnaryThetaRawIndices",
        "AdvancedClaimsIIUnaryThetaQExponent",
        "AdvancedClaimsIIUnaryThetaHalfLatticePoint",
        "AdvancedClaimsIIUnaryThetaCharacteristicA",
    ],
    "advanced_claims_ii_unary_theta_coefficient_twenty_five_eighths": [
        "AdvancedClaimsIIUnaryThetaFiniteCoefficientAt",
        "referenceAdvancedClaimsIIUnaryThetaRawIndices",
        "AdvancedClaimsIIUnaryThetaQExponent",
        "AdvancedClaimsIIUnaryThetaHalfLatticePoint",
        "AdvancedClaimsIIUnaryThetaCharacteristicA",
    ],
    "advanced_claims_ii_paper_t3_block_sum": [
        "AdvancedClaimsIIPaperT3BlockSum",
        "referenceAdvancedClaimsIIPaperT3WeightedBlocks",
    ],
    "advanced_claims_ii_paper_t3_completion_correction_scale": [
        "AdvancedClaimsIIPaperT3CompletionCorrectionScale",
        "AdvancedClaimsIIPaperT3BlockSum",
        "referenceAdvancedClaimsIIPaperT3WeightedBlocks",
    ],
}


def git_blob(path: Path) -> str:
    return subprocess.check_output(["git", "hash-object", str(path)], text=True).strip()


def formatted_names(names: list[str], indent: str = "    ") -> str:
    if not names:
        return ""
    lines: list[str] = []
    current = ""
    for name in names:
        part = name if not current else ", " + name
        if len(current) + len(part) > 78:
            lines.append(current + ",")
            current = name
        else:
            current += part
    if current:
        lines.append(current)
    return ("\n" + indent).join(lines)


def generic_proof(variant: str, names: list[str]) -> list[str]:
    joined = formatted_names(names)
    if variant == "norm-defs":
        return [f"  norm_num [{joined}]"]
    if variant == "simp-norm-defs":
        return [f"  simp [{joined}] <;> norm_num"]
    if variant == "unfold-norm":
        return [f"  unfold {' '.join(names)}", "  norm_num"]
    raise AssertionError(variant)


def structural_proofs() -> dict[str, list[str]]:
    return {
        "advanced_claims_ii_paper_t1t2_full_solution_table": [
            "  norm_num [AdvancedClaimsIIPaperT1T2FullSolution,",
            "    AdvancedClaimsIIPaperT1T2FullDepth, referenceMock1MList,",
            "    AdvancedClaimsIIRatCoordinateVector]",
        ],
        "advanced_claims_ii_paper_t1t2_full_matvec": [
            "  rw [advanced_claims_ii_paper_t1t2_full_matrix_formula,",
            "    advanced_claims_ii_paper_t1t2_full_solution_table,",
            "    advanced_claims_ii_paper_t1t2_full_rhs_table]",
            "  norm_num [MatVecRat, dotRat, AdvancedClaimsIISignedIdentityMatrix,",
            "    AdvancedClaimsIISignedIdentityRow, AdvancedClaimsIIRatCoordinateVector]",
        ],
        "advanced_claims_ii_paper_t1t2_full_solution_squared_norm": [
            "  rw [advanced_claims_ii_paper_t1t2_full_solution_table]",
            "  norm_num [AdvancedClaimsIIRatSquaredNorm]",
        ],
        "advanced_claims_ii_paper_t1t2_full_rhs_squared_norm": [
            "  rw [advanced_claims_ii_paper_t1t2_full_rhs_table]",
            "  norm_num [AdvancedClaimsIIRatSquaredNorm]",
        ],
        "advanced_claims_ii_paper_t1t2_full_pair_targets": [
            "  rw [advanced_claims_ii_paper_t1t2_full_rhs_table]",
            "  norm_num [AdvancedClaimsIISignedPairTargets,",
            "    AdvancedClaimsIIPaperT1T2FullPairSolution,",
            "    AdvancedClaimsIIPaperT1T2FullDepth, referenceMock1MList]",
        ],
        "advanced_claims_ii_paper_t1t2_full_pair_flatten": [
            "  rw [advanced_claims_ii_paper_t1t2_full_solution_table]",
            "  norm_num [AdvancedClaimsIIFlattenSignedPairs,",
            "    AdvancedClaimsIIPaperT1T2FullPairSolution,",
            "    AdvancedClaimsIIPaperT1T2FullDepth, referenceMock1MList]",
        ],
        "advanced_claims_ii_paper_t1t2_full_pair_squared_norm": [
            "  norm_num [AdvancedClaimsIISignedPairSquaredNorm,",
            "    AdvancedClaimsIIPaperT1T2FullPairSolution,",
            "    AdvancedClaimsIIPaperT1T2FullDepth, referenceMock1MList]",
        ],
        "advanced_claims_ii_appell_lerch_leading_exponent_table": [
            "  norm_num [referenceAdvancedClaimsIIAppellLerchRidgeParameters,",
            "    referenceAdvancedClaimsIIAppellLerchLeadingExponents,",
            "    advanced_claims_ii_appell_lerch_ridge_total_exponent]",
        ],
        "advanced_claims_ii_unary_theta_raw_term_table": [
            "  norm_num [referenceAdvancedClaimsIIUnaryThetaRawIndices,",
            "    referenceAdvancedClaimsIIUnaryThetaRawTerms,",
            "    AdvancedClaimsIIUnaryThetaRawTerm, AdvancedClaimsIIUnaryThetaQExponent,",
            "    AdvancedClaimsIIUnaryThetaHalfLatticePoint,",
            "    AdvancedClaimsIIUnaryThetaCharacteristicA]",
        ],
        "advanced_claims_ii_unary_theta_coefficient_one_eighth": [
            "  norm_num [AdvancedClaimsIIUnaryThetaFiniteCoefficientAt,",
            "    referenceAdvancedClaimsIIUnaryThetaRawIndices,",
            "    AdvancedClaimsIIUnaryThetaQExponent,",
            "    AdvancedClaimsIIUnaryThetaHalfLatticePoint,",
            "    AdvancedClaimsIIUnaryThetaCharacteristicA]",
        ],
        "advanced_claims_ii_unary_theta_coefficient_nine_eighths": [
            "  norm_num [AdvancedClaimsIIUnaryThetaFiniteCoefficientAt,",
            "    referenceAdvancedClaimsIIUnaryThetaRawIndices,",
            "    AdvancedClaimsIIUnaryThetaQExponent,",
            "    AdvancedClaimsIIUnaryThetaHalfLatticePoint,",
            "    AdvancedClaimsIIUnaryThetaCharacteristicA]",
        ],
        "advanced_claims_ii_unary_theta_coefficient_twenty_five_eighths": [
            "  norm_num [AdvancedClaimsIIUnaryThetaFiniteCoefficientAt,",
            "    referenceAdvancedClaimsIIUnaryThetaRawIndices,",
            "    AdvancedClaimsIIUnaryThetaQExponent,",
            "    AdvancedClaimsIIUnaryThetaHalfLatticePoint,",
            "    AdvancedClaimsIIUnaryThetaCharacteristicA]",
        ],
        "advanced_claims_ii_paper_t3_block_sum": [
            "  norm_num [AdvancedClaimsIIPaperT3BlockSum,",
            "    referenceAdvancedClaimsIIPaperT3WeightedBlocks]",
        ],
        "advanced_claims_ii_paper_t3_completion_correction_scale": [
            "  norm_num [AdvancedClaimsIIPaperT3CompletionCorrectionScale,",
            "    AdvancedClaimsIIPaperT3BlockSum,",
            "    referenceAdvancedClaimsIIPaperT3WeightedBlocks]",
        ],
    }


def replace_theorem_proof(text: str, name: str, proof: list[str]) -> str:
    start_match = re.search(rf"(?m)^theorem\s+{re.escape(name)}\b", text)
    if start_match is None:
        raise SystemExit(f"missing theorem {name}")
    next_match = COMMAND_RE.search(text, start_match.end())
    end = next_match.start() if next_match else len(text)
    block = text[start_match.start():end]
    needle = ":= by\n  decide"
    if block.count(needle) != 1:
        raise SystemExit(f"{name}: expected one decide proof, found {block.count(needle)}")
    block = block.replace(needle, ":= by\n" + "\n".join(proof), 1)
    return text[:start_match.start()] + block + text[end:]


def generate_spt1(source: Path, output: Path) -> None:
    observed = git_blob(source)
    if observed != SPT1_BLOB:
        raise SystemExit(f"wrong Spt1 blob: {observed}")
    text = source.read_text().replace("native_decide", "decide")
    if "native_decide" in text:
        raise SystemExit("Spt1 cleanup incomplete")
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(text)


def generate_mock1a(variant: str, source: Path, output: Path) -> None:
    if variant not in VARIANTS:
        raise SystemExit(f"unknown variant {variant}; choices={sorted(VARIANTS)}")
    observed = git_blob(source)
    if observed != MOCK1A_BLOB:
        raise SystemExit(f"wrong Mock1_Advanced blob: {observed}")
    text = source.read_text()
    if text.count("native_decide") != 60:
        raise SystemExit(f"expected 60 native_decide tokens, found {text.count('native_decide')}")
    text = text.replace("native_decide", "decide")
    marker = "import Mathlib\n"
    if text.count(marker) != 1:
        raise SystemExit("unexpected import marker count")
    text = text.replace(marker, marker + "\nset_option maxRecDepth 200000\n", 1)

    proofs = structural_proofs() if variant == "rw-structural" else {
        name: generic_proof(variant, defs) for name, defs in DEFS.items()
    }
    for name, proof in proofs.items():
        text = replace_theorem_proof(text, name, proof)

    field_block = """  fixed_shadow_block_sum_link := by
    decide
  fixed_shadow_scale_link := by
    decide
"""
    field_replacement = """  fixed_shadow_block_sum_link := by
    change (1 : Rat) = AdvancedClaimsIIPaperT3BlockSum
    exact advanced_claims_ii_paper_t3_block_sum.symm
  fixed_shadow_scale_link := by
    change (1 : Rat) =
      AdvancedClaimsIIPaperT3BlockSum * (1 : Rat)
    rw [advanced_claims_ii_paper_t3_block_sum]
"""
    if text.count(field_block) != 1:
        raise SystemExit(f"expected one fixed-shadow field block, found {text.count(field_block)}")
    text = text.replace(field_block, field_replacement, 1)
    if "native_decide" in text:
        raise SystemExit("Mock1_Advanced cleanup incomplete")
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(text)
    print(f"variant={variant}")
    print(f"candidate_sha256={hashlib.sha256(output.read_bytes()).hexdigest()}")
    print(f"candidate_blob={git_blob(output)}")


def main() -> None:
    if len(sys.argv) != 6:
        raise SystemExit(
            "usage: native_decide_cleanup_r3_generate.py VARIANT SPT1_IN MOCK1A_IN SPT1_OUT MOCK1A_OUT"
        )
    generate_spt1(Path(sys.argv[2]), Path(sys.argv[4]))
    generate_mock1a(sys.argv[1], Path(sys.argv[3]), Path(sys.argv[5]))


if __name__ == "__main__":
    main()
