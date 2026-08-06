from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
M2A = ROOT / "PrimalitySheafVerification" / "Mock2_Advanced.lean"


def replace_exact(text: str, old: str, new: str, label: str) -> str:
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f"{label}: expected exactly 1 match, found {count}")
    print(f"{label}: applied 1")
    return text.replace(old, new, 1)


def main() -> int:
    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        """    have hpre :
        τ ∈ (fun w : UpperHalfPlane => gR • w) ⁻¹' frontier s := by
      rw [(Homeomorph.smul gR).preimage_frontier s]
""",
        """    have hpre :
        τ ∈ (fun w : UpperHalfPlane => gR • w) ⁻¹' frontier s := by
      change τ ∈ ⇑(Homeomorph.smul gR) ⁻¹' frontier s
      rw [(Homeomorph.smul gR).preimage_frontier s]
""",
        "Mock2_Advanced expose the smul homeomorph before pulling back a frontier",
    )
    m2a = replace_exact(
        m2a,
        """    have hpre :
        τ ∈ (fun w : UpperHalfPlane => gR • w) ⁻¹'
          frontier ModularGroup.fd := by
      rw [(Homeomorph.smul gR).preimage_frontier ModularGroup.fd]
""",
        """    have hpre :
        τ ∈ (fun w : UpperHalfPlane => gR • w) ⁻¹'
          frontier ModularGroup.fd := by
      change τ ∈ ⇑(Homeomorph.smul gR) ⁻¹' frontier ModularGroup.fd
      rw [(Homeomorph.smul gR).preimage_frontier ModularGroup.fd]
""",
        "Mock2_Advanced expose the smul homeomorph for the standard frontier",
    )
    M2A.write_text(m2a, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
