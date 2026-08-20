#!/usr/bin/env python3
"""Apply the two independent final-authority source repairs as one batch.

Repairs:
1. Spt1: replace the sole project-forbidden `native_decide` example with the
   already-proved `card_ker_mulLeft` theorem.
2. Spt3: rename the project-local formal-log wrapper so it no longer declares
   the global name `PowerSeries.logOf`, which collides with Mathlib when the
   aggregate BuildAll environment imports both modules.

The script is deterministic and idempotent.  It refuses to modify protected
FA, Integrated, QYM, or the actual-Lean-verified Mock1_Advanced source.
"""
from __future__ import annotations

import hashlib
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SPT1 = ROOT / "PrimalitySheafVerification/Spt1.lean"
SPT3 = ROOT / "PrimalitySheafVerification/Spt3.lean"
M1A = ROOT / "PrimalitySheafVerification/Mock1_Advanced.lean"
FA = ROOT / "PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean"
INTEGRATED = ROOT / "PrimalitySheafVerification/Mock2_FunctionalAnalysis_Integrated.lean"
QYM = ROOT / "PrimalitySheafVerification/QYM.lean"

EXPECTED_BLOBS = {
    FA: "28f614d48e02a0f28d3f5a758e813350b3ea89cf",
    INTEGRATED: "464f5dd095876b20165d12690c8127ef9d909e6a",
    QYM: "7afb309d7c4da97da7bc6b922931734d72830d41",
    M1A: "3b6596bbc0790c7d6e427c44e2b0b18b8af3efa6",
}
EXPECTED_QYM_SHA256 = "ab7c394f68b812046bcfae109b274a2d4fa42479bf8e76461c73a9c190fb3204"


def git_blob(path: Path) -> str:
    return subprocess.check_output(
        ["git", "hash-object", "--no-filters", str(path.relative_to(ROOT))],
        cwd=ROOT,
        text=True,
    ).strip()


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def verify_frozen_sources() -> None:
    for path, expected in EXPECTED_BLOBS.items():
        actual = git_blob(path)
        if actual != expected:
            raise RuntimeError(
                f"protected source drift: {path.relative_to(ROOT)}: {actual} != {expected}"
            )
    actual_qym_sha = sha256(QYM)
    if actual_qym_sha != EXPECTED_QYM_SHA256:
        raise RuntimeError(
            f"QYM SHA256 drift: {actual_qym_sha} != {EXPECTED_QYM_SHA256}"
        )


def replace_once_or_already(text: str, old: str, new: str, label: str) -> tuple[str, bool]:
    old_count = text.count(old)
    new_count = text.count(new)
    if old_count == 1 and new_count == 0:
        return text.replace(old, new, 1), True
    if old_count == 0 and new_count == 1:
        return text, False
    raise RuntimeError(
        f"{label}: expected one old block or one already-patched block; "
        f"old={old_count}, new={new_count}"
    )


def patch_spt1() -> bool:
    old = (
        "example : Fintype.card {x : ZMod 9 // (12 : ZMod 9) * x = 0} = 3 := by native_decide"
    )
    new = """example : Fintype.card {x : ZMod 9 // (12 : ZMod 9) * x = 0} = 3 := by
  rw [← Nat.card_eq_fintype_card]
  change Nat.card (AddMonoidHom.mulLeft (12 : ZMod 9)).ker = 3
  simpa using (card_ker_mulLeft 9 12)"""
    text = SPT1.read_text(encoding="utf-8")
    patched, changed = replace_once_or_already(text, old, new, "Spt1 native_decide")
    if changed:
        SPT1.write_text(patched, encoding="utf-8")
    if "by native_decide" in SPT1.read_text(encoding="utf-8"):
        raise RuntimeError("Spt1 still contains an executable `by native_decide`")
    return changed


def patch_spt3() -> bool:
    old_wrapper = """variable {A}

/-- The formal logarithm supplied by `PowerSeries.LogInterface`. -/
noncomputable def logOf [LogInterface A] : A⟦X⟧ → A⟦X⟧ :=
  LogInterface.logOf

/-- [INTERFACE] Product additivity of the formal logarithm. -/
theorem logOf_mul [LogInterface A] {f g : A⟦X⟧}
    (hf : constantCoeff f = 1) (hg : constantCoeff g = 1) :
    logOf (f * g) = logOf f + logOf g :=
  LogInterface.logOf_mul hf hg"""
    new_wrapper = """variable {A}

/-- The project-specific formal logarithm supplied by `PowerSeries.LogInterface`.
The distinct name avoids colliding with Mathlib's global `PowerSeries.logOf`
when all project roots are imported into one aggregate environment. -/
noncomputable def interfaceLogOf [LogInterface A] : A⟦X⟧ → A⟦X⟧ :=
  LogInterface.logOf

/-- [INTERFACE] Product additivity of the project-specific formal logarithm. -/
theorem logOf_mul [LogInterface A] {f g : A⟦X⟧}
    (hf : constantCoeff f = 1) (hg : constantCoeff g = 1) :
    interfaceLogOf (f * g) = interfaceLogOf f + interfaceLogOf g :=
  LogInterface.logOf_mul hf hg"""
    old_qp = """    PowerSeries.logOf (f * g) = PowerSeries.logOf f + PowerSeries.logOf g :=
  PowerSeries.logOf_mul hf hg"""
    new_qp = """    PowerSeries.interfaceLogOf (f * g) =
      PowerSeries.interfaceLogOf f + PowerSeries.interfaceLogOf g :=
  PowerSeries.logOf_mul hf hg"""

    text = SPT3.read_text(encoding="utf-8")
    text, changed_wrapper = replace_once_or_already(
        text, old_wrapper, new_wrapper, "Spt3 formal-log wrapper"
    )
    text, changed_qp = replace_once_or_already(
        text, old_qp, new_qp, "Spt3 Qp formal-log specialization"
    )
    if changed_wrapper != changed_qp:
        raise RuntimeError(
            "Spt3 patch is not atomic: wrapper and specialization states differ"
        )
    if changed_wrapper:
        SPT3.write_text(text, encoding="utf-8")

    final = SPT3.read_text(encoding="utf-8")
    forbidden_decl = "noncomputable def logOf [LogInterface A]"
    if forbidden_decl in final:
        raise RuntimeError("Spt3 still declares the colliding PowerSeries.logOf wrapper")
    if final.count("noncomputable def interfaceLogOf [LogInterface A]") != 1:
        raise RuntimeError("Spt3 interfaceLogOf wrapper count is not exactly one")
    return changed_wrapper


def main() -> None:
    verify_frozen_sources()
    before = {"Spt1": git_blob(SPT1), "Spt3": git_blob(SPT3)}
    changed_spt1 = patch_spt1()
    changed_spt3 = patch_spt3()
    verify_frozen_sources()
    after = {"Spt1": git_blob(SPT1), "Spt3": git_blob(SPT3)}
    print(f"changed_spt1={str(changed_spt1).lower()}")
    print(f"changed_spt3={str(changed_spt3).lower()}")
    print(f"Spt1_before_blob={before['Spt1']}")
    print(f"Spt1_after_blob={after['Spt1']}")
    print(f"Spt1_after_sha256={sha256(SPT1)}")
    print(f"Spt3_before_blob={before['Spt3']}")
    print(f"Spt3_after_blob={after['Spt3']}")
    print(f"Spt3_after_sha256={sha256(SPT3)}")
    print(f"M1A_verified_blob={git_blob(M1A)}")
    print("protected_sources=PASS")


if __name__ == "__main__":
    main()
