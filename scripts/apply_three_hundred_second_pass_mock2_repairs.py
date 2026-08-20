from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
M2 = ROOT / "PrimalitySheafVerification" / "Mock2.lean"


def first_line(text: str) -> str:
    lines = text.splitlines()
    return lines[0] if lines else ""


def replace_exact(
    text: str,
    old: str,
    new: str,
    label: str,
    expected: int = 1,
) -> str:
    actual = text.count(old)
    print(
        f"{label}: expected={expected} actual={actual} "
        f"before={first_line(old)!r} after={first_line(new)!r}"
    )
    if actual != expected:
        raise RuntimeError(
            f"{label}: expected {expected} matches, found {actual}"
        )
    return text.replace(old, new)


def main() -> int:
    text = M2.read_text(encoding="utf-8")

    old_unique = """  apply ConcreteCategory.hom_ext
  intro x
  apply Subtype.ext
  change (m x).1 = T.ι x
  simpa only [CategoryTheory.comp_apply] using
    ConcreteCategory.congr_hom hm x
"""
    actual = text.count(old_unique)
    print(
        "Mock2 equalizer uniqueness blocks: "
        f"expected=2 actual={actual} before={first_line(old_unique)!r}"
    )
    if actual != 2:
        raise RuntimeError(
            f"Mock2 equalizer uniqueness blocks: expected 2, found {actual}"
        )
    source_unique = """  apply ConcreteCategory.hom_ext
  intro x
  apply Subtype.ext
  change ((m ≫ (sourceEqualizerFork S U).ι) x) = T.ι x
  exact ConcreteCategory.congr_hom hm x
"""
    target_unique = """  apply ConcreteCategory.hom_ext
  intro x
  apply Subtype.ext
  change ((m ≫ (targetEqualizerFork S U).ι) x) = T.ι x
  exact ConcreteCategory.congr_hom hm x
"""
    i = text.index(old_unique)
    text = text[:i] + source_unique + text[i + len(old_unique):]
    i = text.index(old_unique)
    text = text[:i] + target_unique + text[i + len(old_unique):]
    print(
        "Mock2 equalizer uniqueness blocks: applied source then target | "
        f"after_source={first_line(source_unique)!r} "
        f"after_target={first_line(target_unique)!r}"
    )

    text = replace_exact(
        text,
        """structure StandaloneZeroProfileCertificate
    (M N : ℕ) (hM : M ≠ 0) : Prop where
""",
        """structure StandaloneZeroProfileCertificate
    (M N : ℕ) (hM : M ≠ 0) : Type where
""",
        "Mock2 standalone certificate carries universal-property data",
    )
    text = replace_exact(
        text,
        "theorem standaloneZeroProfile_certificate (M N : ℕ) (hM : M ≠ 0) :",
        "noncomputable def standaloneZeroProfile_certificate (M N : ℕ) (hM : M ≠ 0) :",
        "Mock2 standalone certificate constructor",
    )
    text = replace_exact(
        text,
        """structure PaperElementaryConclusions
    (D : PaperElementaryInputData) (P : PaperElementaryModel D) : Prop where
""",
        """structure PaperElementaryConclusions
    (D : PaperElementaryInputData) (P : PaperElementaryModel D) : Type where
""",
        "Mock2 paper conclusions carry certificate data",
    )
    text = replace_exact(
        text,
        "theorem canonicalZeroBridgeModel_certificate (D : PaperElementaryInputData) :",
        "noncomputable def canonicalZeroBridgeModel_certificate (D : PaperElementaryInputData) :",
        "Mock2 canonical zero bridge certificate constructor",
    )
    text = replace_exact(
        text,
        "structure StaticAcceptanceCertificate (D : PaperElementaryInputData) : Prop where",
        "structure StaticAcceptanceCertificate (D : PaperElementaryInputData) : Type where",
        "Mock2 static acceptance carries certificate data",
    )
    text = replace_exact(
        text,
        "theorem staticAcceptance_certificate (D : PaperElementaryInputData) :",
        "noncomputable def staticAcceptance_certificate (D : PaperElementaryInputData) :",
        "Mock2 static acceptance constructor",
    )

    M2.write_text(text, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
