from __future__ import annotations

from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
MOCK2 = ROOT / "PrimalitySheafVerification" / "Mock2.lean"


def replace_once(text: str, old: str, new: str, label: str) -> str:
    count = text.count(old)
    if count == 0:
        if new in text:
            print(f"{label}: already applied")
            return text
        raise RuntimeError(f"{label}: expected source pattern not found")
    if count != 1:
        raise RuntimeError(f"{label}: expected one source pattern, found {count}")
    print(f"{label}: applied 1")
    return text.replace(old, new, 1)


def main() -> int:
    text = MOCK2.read_text(encoding="utf-8")

    text = replace_once(
        text,
        """def qGaugeVariablesPresheaf {Open : Type u} [Preorder Open]
""",
        """noncomputable def qGaugeVariablesPresheaf {Open : Type u} [Preorder Open]
""",
        "Mock2 mark the legacy q-gauge presheaf noncomputable",
    )

    text = replace_once(
        text,
        """def actualQGaugeVariablesPresheaf
""",
        """noncomputable def actualQGaugeVariablesPresheaf
""",
        "Mock2 mark the actual q-gauge presheaf noncomputable",
    )

    text = replace_once(
        text,
        """    (QGaugeVariable.restrict hUV x).mockPart =
      (Mmock.actualBundle K).res hUV x.mockPart :=
""",
        """    (QGaugeVariable.restrict
        (Lq := Lq) (Mmock := Mmock.actualBundle K) hUV x).mockPart =
      (Mmock.actualBundle K).res hUV x.mockPart :=
""",
        "Mock2 pin both presheaf parameters in actual restriction",
    )

    text = replace_once(
        text,
        """def AqPresheaf
""",
        """noncomputable def AqPresheaf
""",
        "Mock2 mark AqPresheaf noncomputable",
    )

    MOCK2.write_text(text, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
