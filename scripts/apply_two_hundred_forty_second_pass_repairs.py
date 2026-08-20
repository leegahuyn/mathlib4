from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
M2A = ROOT / "PrimalitySheafVerification" / "Mock2_Advanced.lean"


def main() -> int:
    text = M2A.read_text(encoding="utf-8")
    start_marker = "theorem left_S_rep_decomposition"
    end_marker = "theorem exists_rep_mul_generated"
    start = text.index(start_marker)
    end = text.index(end_marker, start)
    block = text[start:end]
    old = "Matrix.mul_fin_two]"
    new = "Matrix.mul_fin_two, Matrix.vecMul, dotProduct, Fin.sum_univ_two]"
    count = block.count(old)
    if count != 8:
        raise RuntimeError(
            f"Mock2 Advanced finite transition matrix reductions: expected 8 matches, found {count}")
    block = block.replace(old, new)
    print(f"Mock2 Advanced finite transition matrix reductions: applied {count}")
    M2A.write_text(text[:start] + block + text[end:], encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
