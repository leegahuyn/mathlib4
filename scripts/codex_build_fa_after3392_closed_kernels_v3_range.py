from pathlib import Path

src = Path('scripts/codex_fa_after3392_closed_kernels_v1.sh').read_text()
src = src.replace('codex-fa-after3392-closed-kernels-v1', 'codex-fa-after3392-closed-kernels-v3-range')

old_r = '''new_r='''  rw [show (weakRaisingSubmodule n : Set (WeakCoordinateAmbient n)) =
      ⋂ v : Mock2FA.PaperCorrections.AutomorphicSobolev.HalfWeightDifferentialOperators.InverseEtaFixedPhaseCore ((n + 1) + 1),
        ((raisingDefect n v).ker : Set (WeakCoordinateAmbient n)) by
    ext x
    simpa only [Set.mem_iInter, LinearMap.mem_ker,
      ContinuousLinearMap.coe_coe] using
        (mem_weakRaisingSubmodule_iff n x)]
  exact isClosed_iInter fun v ↦
    ContinuousLinearMap.isClosed_ker (raisingDefect n v)''' '''
new_r = '''new_r='''  unfold weakRaisingSubmodule
  exact isClosed_iInter fun s ↦
    isClosed_iInter fun hs ↦ by
      rcases hs with ⟨v, rfl⟩
      exact ContinuousLinearMap.isClosed_ker (raisingDefect n v)''' '''
old_l = '''new_l='''  rw [show (weakLoweringSubmodule n : Set (WeakCoordinateAmbient n)) =
      ⋂ v : Mock2FA.PaperCorrections.AutomorphicSobolev.HalfWeightDifferentialOperators.InverseEtaFixedPhaseCore n,
        ((loweringDefect n v).ker : Set (WeakCoordinateAmbient n)) by
    ext x
    simpa only [Set.mem_iInter, LinearMap.mem_ker,
      ContinuousLinearMap.coe_coe] using
        (mem_weakLoweringSubmodule_iff n x)]
  exact isClosed_iInter fun v ↦
    ContinuousLinearMap.isClosed_ker (loweringDefect n v)''' '''
new_l = '''new_l='''  unfold weakLoweringSubmodule
  exact isClosed_iInter fun s ↦
    isClosed_iInter fun hs ↦ by
      rcases hs with ⟨v, rfl⟩
      exact ContinuousLinearMap.isClosed_ker (loweringDefect n v)''' '''

assert src.count(old_r) == 1, src.count(old_r)
src = src.replace(old_r, new_r, 1)
assert src.count(old_l) == 1, src.count(old_l)
src = src.replace(old_l, new_l, 1)
Path('/tmp/codex_fa_after3392_closed_kernels_v3_range.sh').write_text(src)
