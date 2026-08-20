#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import re
import sys
from pathlib import Path

SPT1_BLOB = "ed554b8268e9504281572d0cea27e40d5ba06a19"
MOCK1A_BLOB = "2dc68bb04df549064b41fc318d18ea02d4d40679"

RAT_DECLS = [
    "advanced_claims_ii_paper_t1t2_full_solution_table",
    "advanced_claims_ii_paper_t1t2_full_matvec",
    "advanced_claims_ii_paper_t1t2_full_solution_squared_norm",
    "advanced_claims_ii_paper_t1t2_full_rhs_squared_norm",
    "advanced_claims_ii_paper_t1t2_full_pair_targets",
    "advanced_claims_ii_paper_t1t2_full_pair_flatten",
    "advanced_claims_ii_paper_t1t2_full_pair_squared_norm",
    "advanced_claims_ii_appell_lerch_leading_exponent_table",
    "advanced_claims_ii_unary_theta_raw_term_table",
    "advanced_claims_ii_unary_theta_coefficient_one_eighth",
    "advanced_claims_ii_unary_theta_coefficient_nine_eighths",
    "advanced_claims_ii_unary_theta_coefficient_twenty_five_eighths",
    "advanced_claims_ii_paper_t3_block_sum",
    "advanced_claims_ii_paper_t3_completion_correction_scale",
]

RECURSION_DECLS = [
    "advanced_claims_ii_ramanujan_f_outside_prefix_table",
    "advanced_claims_ii_ramanujan_psi_prefix_table",
    "advanced_claims_ii_ramanujan_explicit_correction_prefix_table",
    "advanced_claims_ii_ramanujan_dictionary_correction_prefix_table",
]

VARIANTS = {
    "all-decide-depth": ("decide", "decide", "decide"),
    "all-norm-depth": ("norm_num", "norm_num", "norm_num"),
    "targeted-norm-depth": ("decide", "norm_num", "decide"),
    "targeted-all20-norm-depth": ("decide", "norm_num", "norm_num"),
}

COMMAND_RE = re.compile(
    r"(?m)^(?:(?:noncomputable|private|protected|public|local)\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque|namespace|end)\b"
)


def git_blob(path: Path) -> str:
    import subprocess
    return subprocess.check_output(["git", "hash-object", str(path)], text=True).strip()


def replace_decl_tactic(text: str, name: str, tactic: str) -> str:
    start_match = re.search(rf"(?m)^theorem\s+{re.escape(name)}\b", text)
    if start_match is None:
        raise SystemExit(f"missing theorem {name}")
    next_match = COMMAND_RE.search(text, start_match.end())
    end = next_match.start() if next_match else len(text)
    block = text[start_match.start():end]
    count = len(re.findall(r"(?<![A-Za-z0-9_])decide(?![A-Za-z0-9_])", block))
    if count != 1:
        raise SystemExit(f"{name}: expected one decide after base replacement, found {count}")
    block = re.sub(
        r"(?<![A-Za-z0-9_])decide(?![A-Za-z0-9_])",
        tactic,
        block,
        count=1,
    )
    return text[:start_match.start()] + block + text[end:]


def insert_depth_option(text: str) -> str:
    marker = "import Mathlib\n"
    if text.count(marker) != 1:
        raise SystemExit(f"expected one import marker, found {text.count(marker)}")
    return text.replace(
        marker,
        marker + "\nset_option maxRecDepth 200000\n",
        1,
    )


def generate_spt1(source: Path, output: Path) -> None:
    if git_blob(source) != SPT1_BLOB:
        raise SystemExit(f"wrong Spt1 blob: {git_blob(source)}")
    text = source.read_text()
    executable_count = len(re.findall(r"(?m)^.*\bnative_decide\b", text))
    if executable_count < 1:
        raise SystemExit("Spt1 native_decide token not found")
    text = text.replace("native_decide", "decide")
    if "native_decide" in text:
        raise SystemExit("Spt1 cleanup incomplete")
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(text)


def generate_mock1a(variant: str, source: Path, output: Path) -> None:
    if variant not in VARIANTS:
        raise SystemExit(f"unknown variant {variant}; choices={sorted(VARIANTS)}")
    if git_blob(source) != MOCK1A_BLOB:
        raise SystemExit(f"wrong Mock1_Advanced blob: {git_blob(source)}")
    default_tactic, rat_tactic, recursion_tactic = VARIANTS[variant]
    text = source.read_text()
    before = text.count("native_decide")
    if before != 60:
        raise SystemExit(f"expected 60 native_decide tokens, found {before}")
    text = text.replace("native_decide", default_tactic)
    text = insert_depth_option(text)

    if default_tactic == "decide":
        for name in RAT_DECLS:
            if rat_tactic != "decide":
                text = replace_decl_tactic(text, name, rat_tactic)
        for name in RECURSION_DECLS:
            if recursion_tactic != "decide":
                text = replace_decl_tactic(text, name, recursion_tactic)

        for field in ("fixed_shadow_block_sum_link", "fixed_shadow_scale_link"):
            old = f"  {field} := by\n    decide"
            new = f"  {field} := by\n    {rat_tactic}"
            if text.count(old) != 1:
                raise SystemExit(f"{field}: expected one field proof")
            text = text.replace(old, new, 1)

    if "native_decide" in text:
        raise SystemExit("Mock1_Advanced cleanup incomplete")
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(text)
    print(f"variant={variant}")
    print(f"source_native_decide_count={before}")
    print(f"candidate_sha256={hashlib.sha256(output.read_bytes()).hexdigest()}")
    print(f"candidate_blob={git_blob(output)}")


def main() -> None:
    if len(sys.argv) != 6:
        raise SystemExit(
            "usage: native_decide_cleanup_r2_generate.py VARIANT SPT1_IN MOCK1A_IN SPT1_OUT MOCK1A_OUT"
        )
    variant = sys.argv[1]
    generate_spt1(Path(sys.argv[2]), Path(sys.argv[4]))
    generate_mock1a(variant, Path(sys.argv[3]), Path(sys.argv[5]))


if __name__ == "__main__":
    main()
