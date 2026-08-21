#!/usr/bin/env python3
"""Apply the deterministic source repair batch before the v6 actual-Lean sweep."""
from __future__ import annotations

import hashlib
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

PROTECTED_BLOBS = {
    "PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean":
        "28f614d48e02a0f28d3f5a758e813350b3ea89cf",
    "PrimalitySheafVerification/Mock2_FunctionalAnalysis_Integrated.lean":
        "464f5dd095876b20165d12690c8127ef9d909e6a",
    "PrimalitySheafVerification/QYM.lean":
        "7afb309d7c4da97da7bc6b922931734d72830d41",
    "PrimalitySheafVerification/Mock1_Advanced.lean":
        "3b6596bbc0790c7d6e427c44e2b0b18b8af3efa6",
}

ROOTS = [
    "PrimalitySheafVerification/Spt1.lean",
    "PrimalitySheafVerification/Spt2.lean",
    "PrimalitySheafVerification/Spt3.lean",
    "PrimalitySheafVerification/Spt4.lean",
    "PrimalitySheafVerification/Spt5.lean",
    "PrimalitySheafVerification/Spt6.lean",
    "PrimalitySheafVerification/Spt7.lean",
    "PrimalitySheafVerification/Mock1.lean",
    "PrimalitySheafVerification/Mock1_Advanced.lean",
    "PrimalitySheafVerification/Mock2.lean",
    "PrimalitySheafVerification/Mock2_Advanced.lean",
    "PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean",
    "PrimalitySheafVerification/QYM.lean",
    "PrimalitySheafVerification/Mock2_FunctionalAnalysis_Integrated.lean",
    "PrimalitySheafVerification/Mock3.lean",
    "PrimalitySheafVerification/BuildAll.lean",
]

MOCK3_FIXED = """import PrimalitySheafVerification.QYM

/-!
# Canonical Mock3 bridge

The project's third Mock development is the frozen `QYM` module. This checked-in
bridge gives that development a canonical `Mock3` module path without copying,
replacing, or altering any QYM declaration.

It is intentionally a transparent integration boundary: all mathematical content
remains in the source-identical golden `PrimalitySheafVerification.QYM` module.
-/
"""

SPT1_OLD = (
    "example : Fintype.card {x : ZMod 9 // (12 : ZMod 9) * x = 0} = 3 "
    ":= by native_decide"
)
SPT1_NEW = """example : Fintype.card {x : ZMod 9 // (12 : ZMod 9) * x = 0} = 3 := by
  rw [← Nat.card_eq_fintype_card]
  change Nat.card (AddMonoidHom.mulLeft (12 : ZMod 9)).ker = 3
  simpa using (card_ker_mulLeft 9 12)"""


def git(*args: str) -> str:
    return subprocess.check_output(["git", *args], cwd=ROOT, text=True).strip()


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def verify_protected() -> None:
    for rel, expected in PROTECTED_BLOBS.items():
        actual = git("hash-object", "--no-filters", rel)
        if actual != expected:
            raise RuntimeError(f"protected source drift: {rel}: {actual} != {expected}")


def apply_sources() -> None:
    spt1 = ROOT / "PrimalitySheafVerification/Spt1.lean"
    text = spt1.read_text(encoding="utf-8")
    if text.count(SPT1_OLD) == 1:
        text = text.replace(SPT1_OLD, SPT1_NEW, 1)
        spt1.write_text(text, encoding="utf-8")
    elif text.count(SPT1_NEW) != 1:
        raise RuntimeError("Spt1 native_decide target changed, missing, or duplicated")

    mock3 = ROOT / "PrimalitySheafVerification/Mock3.lean"
    if mock3.read_text(encoding="utf-8") != MOCK3_FIXED:
        mock3.write_text(MOCK3_FIXED, encoding="utf-8")


def forbidden_scan() -> None:
    executable_patterns = {
        "sorry": re.compile(r"\bsorry\b"),
        "admit": re.compile(r"\badmit\b"),
        "native_decide": re.compile(r"\bnative_decide\b"),
        "maxHeartbeats_zero": re.compile(r"set_option\s+maxHeartbeats\s+0\b"),
    }
    failures: list[str] = []
    for rel in ROOTS:
        path = ROOT / rel
        text = path.read_text(encoding="utf-8")
        # Strip comments for this bootstrap scan. The final authority controller
        # performs the canonical policy audit again after actual Lean compilation.
        stripped = re.sub(r"/-.*?-/", "", text, flags=re.S)
        stripped = re.sub(r"--[^\n]*", "", stripped)
        for label, pattern in executable_patterns.items():
            count = len(pattern.findall(stripped))
            if count:
                failures.append(f"{rel}: {label}={count}")
    if failures:
        raise RuntimeError("forbidden executable constructs remain:\n" + "\n".join(failures))


def main() -> int:
    verify_protected()
    apply_sources()
    verify_protected()
    forbidden_scan()
    print("SOURCE_PATCH_V6=PASS")
    for rel in PROTECTED_BLOBS:
        path = ROOT / rel
        print(
            f"{rel}\tblob={git('hash-object', '--no-filters', rel)}"
            f"\tsha256={sha256(path)}"
        )
    for rel in (
        "PrimalitySheafVerification/Spt1.lean",
        "PrimalitySheafVerification/Mock3.lean",
    ):
        path = ROOT / rel
        print(
            f"{rel}\tblob={git('hash-object', '--no-filters', rel)}"
            f"\tsha256={sha256(path)}"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
