from __future__ import annotations

from pathlib import Path


def main() -> int:
    path = Path("PrimalitySheafVerification/Mock2_Advanced.lean")
    text = path.read_text(encoding="utf-8")
    old = """  change DenseRange (Set.inclusion M.core.le_topologicalClosure)
  simpa [-SetLike.coe_sort_coe]
"""
    new = """  change DenseRange (Set.inclusion M.core.le_topologicalClosure)
  simp [-SetLike.coe_sort_coe]
"""
    count = text.count(old)
    if count:
        text = text.replace(old, new)
        path.write_text(text, encoding="utf-8", newline="\n")
        print(f"Mock2Advanced dense-range simp normalization: applied {count}")
    elif new in text:
        print("Mock2Advanced dense-range simp normalization: already applied")
    else:
        print("Mock2Advanced dense-range simp normalization: source changed; skipped")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
