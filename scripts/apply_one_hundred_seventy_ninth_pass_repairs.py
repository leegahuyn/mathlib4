from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
M2 = ROOT / "PrimalitySheafVerification" / "Mock2.lean"


def replace_exact(text: str, old: str, new: str, label: str, expected: int = 1) -> str:
    count = text.count(old)
    if count != expected:
        raise RuntimeError(f"{label}: expected exactly {expected} match(es), found {count}")
    print(f"{label}: applied {expected}")
    return text.replace(old, new, expected)


def main() -> int:
    m2 = M2.read_text(encoding="utf-8")
    m2 = replace_exact(
        m2,
        """def Bq : QGaugePresheaf.{0, v} Opens where
  Field U := LocallyConstant U (BoundaryDatum A)
  res hUV s := LocallyConstant.comap
    (LocallyConstantValueSheaf.openInclusion hUV) s
  res_id := by
    intro U s
    apply LocallyConstant.ext
    intro x
    rfl
  res_comp := by
    intro U W Z hUW hWZ s
    apply LocallyConstant.ext
    intro x
    rfl
""",
        """def Bq : QGaugePresheaf Opens :=
  locallyConstantQGaugePresheaf (BoundaryDatum A)
""",
        "Mock2 restore the inferred boundary-presheaf fibre universe",
    )
    M2.write_text(m2, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
