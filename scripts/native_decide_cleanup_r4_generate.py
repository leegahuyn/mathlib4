#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import re
import subprocess
import sys
from pathlib import Path

R3_SHA256 = "d2cf9f101e04d58e0fd87e62d1f102b8eb910d4cc5e3e9d2b903e5c7df0f98f2"
R3_BLOB = "da99c78fdc2f6f894b55dd79af1438fa2d51a1b6"
VARIANTS = {
    "decide-tail",
    "rfl-tail",
    "simp-range",
    "norm-range",
}
TARGETS = [
    "advanced_claims_ii_paper_t1t2_full_solution_table",
    "advanced_claims_ii_paper_t1t2_full_matvec",
    "advanced_claims_ii_paper_t1t2_full_pair_targets",
    "advanced_claims_ii_paper_t1t2_full_pair_flatten",
    "advanced_claims_ii_paper_t1t2_full_pair_squared_norm",
]
COMMAND_RE = re.compile(
    r"(?m)^(?:(?:noncomputable|private|protected|public|local)\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque|namespace|end)\b"
)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git_blob(path: Path) -> str:
    return subprocess.check_output(["git", "hash-object", str(path)], text=True).strip()


def append_to_theorem(text: str, name: str, tactic_lines: list[str]) -> str:
    start = re.search(rf"(?m)^theorem\s+{re.escape(name)}\b", text)
    if start is None:
        raise SystemExit(f"missing theorem {name}")
    nxt = COMMAND_RE.search(text, start.end())
    end = nxt.start() if nxt else len(text)
    block = text[start.start():end]
    stripped = block.rstrip()
    block = stripped + "\n" + "\n".join(tactic_lines) + "\n\n"
    return text[:start.start()] + block + text[end:]


def tactic_for(variant: str, name: str) -> list[str]:
    if variant == "decide-tail":
        return ["  decide"]
    if variant == "rfl-tail":
        return ["  rfl"]
    common = (
        "List.range_succ, AdvancedClaimsIISignedIdentityRow, "
        "AdvancedClaimsIIRatCoordinateVector, dotRat"
    )
    if variant == "simp-range":
        if name == "advanced_claims_ii_paper_t1t2_full_matvec":
            return [f"  simp [{common}] <;> norm_num"]
        return ["  simp [List.range_succ] <;> norm_num"]
    if variant == "norm-range":
        if name == "advanced_claims_ii_paper_t1t2_full_matvec":
            return [f"  norm_num [{common}]"]
        return ["  norm_num [List.range_succ]"]
    raise AssertionError(variant)


def main() -> None:
    if len(sys.argv) != 7:
        raise SystemExit(
            "usage: native_decide_cleanup_r4_generate.py VARIANT R3_GENERATOR SPT1_IN MOCK1A_IN SPT1_OUT MOCK1A_OUT"
        )
    variant = sys.argv[1]
    if variant not in VARIANTS:
        raise SystemExit(f"unknown variant {variant}; choices={sorted(VARIANTS)}")
    r3_generator = Path(sys.argv[2])
    spt1_in = Path(sys.argv[3])
    mock1a_in = Path(sys.argv[4])
    spt1_out = Path(sys.argv[5])
    mock1a_out = Path(sys.argv[6])
    intermediate = mock1a_out.with_suffix(".r3.lean")

    subprocess.run(
        [
            sys.executable,
            "-B",
            str(r3_generator),
            "rw-structural",
            str(spt1_in),
            str(mock1a_in),
            str(spt1_out),
            str(intermediate),
        ],
        check=True,
    )
    actual_sha = sha256(intermediate)
    actual_blob = git_blob(intermediate)
    if actual_sha != R3_SHA256 or actual_blob != R3_BLOB:
        raise SystemExit(
            f"failed to reproduce R3 best: sha256={actual_sha} blob={actual_blob}"
        )

    text = intermediate.read_text()
    for name in TARGETS:
        text = append_to_theorem(text, name, tactic_for(variant, name))
    old = """  fixed_shadow_scale_link := by
    change (1 : Rat) =
      AdvancedClaimsIIPaperT3BlockSum * (1 : Rat)
    rw [advanced_claims_ii_paper_t3_block_sum]
"""
    new = old + "    norm_num\n"
    if text.count(old) != 1:
        raise SystemExit(f"fixed-shadow scale block count={text.count(old)}")
    text = text.replace(old, new, 1)
    mock1a_out.write_text(text)
    intermediate.unlink(missing_ok=True)
    if "native_decide" in text or "native_decide" in spt1_out.read_text():
        raise SystemExit("forbidden native_decide remains")
    print(f"variant={variant}")
    print(f"r3_sha256={R3_SHA256}")
    print(f"candidate_sha256={sha256(mock1a_out)}")
    print(f"candidate_blob={git_blob(mock1a_out)}")


if __name__ == "__main__":
    main()
