from pathlib import Path

src = Path('scripts/codex_fa_after3394_weighted_closed_v1.sh').read_text()
src = src.replace('codex-fa-after3394-weighted-closed-v1', 'codex-fa-after3394-weighted-change-v2-min')
old = """new='''    ext x
    simp [weightedWeakSubmodule]'''"""
new = """new='''    ext x
    change (x ∈ weakRaisingSubmodule n ⊓ weakLoweringSubmodule n) ↔
      (x ∈ weakRaisingSubmodule n ∧ x ∈ weakLoweringSubmodule n)
    exact Submodule.mem_inf'''"""
assert src.count(old) == 1, src.count(old)
src = src.replace(old, new, 1)
Path('/tmp/codex_fa_after3394_weighted_change_v2_min.sh').write_text(src)
