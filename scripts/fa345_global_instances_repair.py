from __future__ import annotations

from hashlib import sha256
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
EXPECTED_INPUT_SHA256 = "59d4bcc02ff615190da0691c9bef52fe3d8bfcb0b8cdf573c300e258757376b6"
EXPECTED_OUTPUT_SHA256 = "a847847aa1ed548a69e3b76e061f4ebfebfeb99cb0538ca491f83ca867d42479"

ALIAS = """/-- Canonical fixed-phase core at orbit index `n`. -/
noncomputable abbrev InverseEtaFixedPhaseCore (n : ℤ) : Type :=
  ↥(inverseEtaFixedPhaseStableCoreSubmodule n)
"""

GLOBAL_INSTANCES = """/-- Canonical fixed-phase core at orbit index `n`. -/
noncomputable abbrev InverseEtaFixedPhaseCore (n : ℤ) : Type :=
  ↥(inverseEtaFixedPhaseStableCoreSubmodule n)

/- The all-word stable core is a complex submodule whose carrier is closed
under negation.  Install its additive-group and module structures immediately
after the public alias so every later linear map is elaborated against one
coherent instance family. -/
private noncomputable def inverseEtaFixedPhaseStableCoreAddSubgroup (n : ℤ) :
    AddSubgroup SmoothQuotientCompactFunction where
  carrier := inverseEtaFixedPhaseStableCoreSubmodule n
  zero_mem' := (inverseEtaFixedPhaseStableCoreSubmodule n).zero_mem
  add_mem' := by
    intro x y hx hy
    exact (inverseEtaFixedPhaseStableCoreSubmodule n).add_mem hx hy
  neg_mem' := by
    intro x hx
    have h :=
      (inverseEtaFixedPhaseStableCoreSubmodule n).smul_mem (-1 : ℂ) hx
    simpa only [neg_one_smul] using h

noncomputable instance inverseEtaFixedPhaseCoreAddCommGroup (n : ℤ) :
    AddCommGroup (InverseEtaFixedPhaseCore n) := by
  let S := inverseEtaFixedPhaseStableCoreAddSubgroup n
  change AddCommGroup ↥S
  exact S.toAddCommGroup

noncomputable instance inverseEtaFixedPhaseCoreModule (n : ℤ) :
    Module ℂ (InverseEtaFixedPhaseCore n) where
  one_smul x := by
    apply Subtype.ext
    simp
  mul_smul a b x := by
    apply Subtype.ext
    simp [mul_smul]
  smul_zero a := by
    apply Subtype.ext
    simp
  smul_add a x y := by
    apply Subtype.ext
    simp [smul_add]
  add_smul a b x := by
    apply Subtype.ext
    simp [add_smul]
  zero_smul x := by
    apply Subtype.ext
    simp
"""

GRAPH_START = """/- The stable core was defined while its ambient function space exposed only
an additive monoid instance. Repackage the same carrier as an additive
subgroup, then rebuild the compatible complex-module laws on that carrier. -/
"""
GRAPH_END = """/-- The three concrete shifted Petersson coordinates on the canonical
fixed-phase differential core. -/
"""
DENSITY_START = """/- Reuse the same carrier repair in the density namespace. -/
"""
DENSITY_END = """/-- Forget the bundled covariance of a smooth compact weight section while
retaining its actual function, real smoothness, and quotient-compact support. -/
"""


def digest(text: str) -> str:
    return sha256(text.encode("utf-8")).hexdigest()


def replace_once(text: str, old: str, new: str, label: str) -> str:
    count = text.count(old)
    print(f"{label}: expected=1 actual={count}")
    if count != 1:
        raise RuntimeError(f"{label}: expected one occurrence, found {count}")
    return text.replace(old, new, 1)


def remove_between(text: str, start: str, end: str, label: str) -> str:
    start_count = text.count(start)
    end_count = text.count(end)
    print(
        f"{label}: start_expected=1 start_actual={start_count} "
        f"end_expected=1 end_actual={end_count}"
    )
    if start_count != 1 or end_count != 1:
        raise RuntimeError(
            f"{label}: expected unique boundaries; "
            f"start={start_count}, end={end_count}"
        )
    begin = text.index(start)
    finish = text.index(end, begin)
    return text[:begin] + text[finish:]


def main() -> int:
    text = TARGET.read_text(encoding="utf-8")
    input_sha = digest(text)
    print(f"input_sha256={input_sha}")
    if input_sha == EXPECTED_OUTPUT_SHA256:
        print("[pass345-global] already applied")
        return 0
    if input_sha != EXPECTED_INPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass345-global input sha256: {input_sha}; "
            f"expected {EXPECTED_INPUT_SHA256}"
        )

    text = replace_once(
        text,
        ALIAS,
        GLOBAL_INSTANCES,
        "install coherent fixed-phase instances at public alias",
    )
    text = remove_between(
        text,
        GRAPH_START,
        GRAPH_END,
        "remove late graph-local instance family",
    )
    text = remove_between(
        text,
        DENSITY_START,
        DENSITY_END,
        "remove late density-local instance family",
    )

    output_sha = digest(text)
    print(f"output_sha256={output_sha}")
    if output_sha != EXPECTED_OUTPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass345-global output sha256: {output_sha}; "
            f"expected {EXPECTED_OUTPUT_SHA256}"
        )
    TARGET.write_text(text, encoding="utf-8")
    print("[pass345-global] coherent fixed-phase instances installed at alias")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
