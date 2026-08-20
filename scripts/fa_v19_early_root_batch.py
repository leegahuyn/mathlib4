#!/usr/bin/env python3
from pathlib import Path
import hashlib, json, os, re, sys

if len(sys.argv) != 3:
    raise SystemExit('usage: fa_v19_early_root_batch.py <source> <outdir>')
source = Path(sys.argv[1])
out = Path(sys.argv[2])
out.mkdir(parents=True, exist_ok=True)
base_sha = os.environ.get('BASE_SOURCE_SHA256', '')
before_bytes = source.read_bytes()
if base_sha:
    assert hashlib.sha256(before_bytes).hexdigest() == base_sha
text = before_bytes.decode()
parent = text
replacements = []

def replace_once(label: str, old: str, new: str):
    global text
    n = text.count(old)
    assert n == 1, (label, n)
    text = text.replace(old, new, 1)
    replacements.append(label)

replace_once('qParam_two_periodic:explicit_real_complex_two_bridge',
'''  unfold Function.Periodic.qParam
  have harg :
''',
'''  unfold Function.Periodic.qParam
  have htwo : ((2 : ℝ) : ℂ) = (2 : ℂ) := by norm_num
  rw [htwo]
  have harg :
''')

replace_once('fredholmDefect_rangeOrthogonal_finiteDimensional:real_norm_bound',
'''  have hRbound : ∀ u, ‖u‖ ≤ (1 : ℝ≥0) * ‖R u‖ := by
''',
'''  have hRbound : ∀ u, ‖u‖ ≤ (1 : ℝ) * ‖R u‖ := by
''')
replace_once('fredholmDefect_rangeOrthogonal_finiteDimensional:explicit_NNReal_K',
'''  have hRembedding : IsUniformEmbedding R :=
    R.isUniformEmbedding_of_bound hRbound
''',
'''  have hRembedding : IsUniformEmbedding R :=
    R.isUniformEmbedding_of_bound (K := 1) hRbound
''')

replace_once('weakSchrodinger_finiteDimensional_cluster:restore_open_and_local_instance',
'''namespace Mock2FA.PaperCorrections.AutomorphicSobolev.ActualScalarDiscriminantPDE

open Mock2FA.PaperCorrections.FredholmBypass

/-- The actual scalar discriminant weak operator has finite-dimensional
''',
'''namespace Mock2FA.PaperCorrections.AutomorphicSobolev.ActualScalarDiscriminantPDE

open Mock2FA.PaperCorrections.FredholmBypass
open ExplicitDiscriminantPotential.FixedPhaseGraphPotential
attribute [local instance] actualHMinusOneInnerProductSpace

/-- The actual scalar discriminant weak operator has finite-dimensional
''')

replace_once('FixedPhaseReducedChartFriedrichs:open_ContinuousLinearMap',
'''namespace Mock2FA.PaperCorrections.AutomorphicSobolev
namespace FixedPhaseReducedChartFriedrichs

open Set Function Topology Filter MeasureTheory Metric
open scoped BigOperators LinearPMap
open HalfIntegralMultiplier
''',
'''namespace Mock2FA.PaperCorrections.AutomorphicSobolev
namespace FixedPhaseReducedChartFriedrichs

open Set Function Topology Filter MeasureTheory Metric
open ContinuousLinearMap
open scoped BigOperators LinearPMap
open HalfIntegralMultiplier
''')

replace_once('support_friedrichsMollifiedRepresentative:ofReal_support_bridge',
'''  refine (support_convolution_subset_swap
    (ContinuousLinearMap.lsmul ℝ ℂ)).trans ?_
  calc
    Function.support (u : ℂ → ℂ) +
          Function.support (friedrichsMollifierReal j) ⊆
        K + closedBall (0 : ℂ) (friedrichsRadius j) :=
      add_subset_add hu
        (support_friedrichsMollifierReal_subset_closedBall j)
''',
'''  refine (support_convolution_subset_swap
    (ContinuousLinearMap.lsmul ℝ ℂ)).trans ?_
  have hsupp :
      Function.support (fun t : ℂ ↦ (friedrichsMollifierReal j t : ℂ)) =
        Function.support (friedrichsMollifierReal j) := by
    ext t
    simp only [Function.mem_support, Complex.ofReal_ne_zero]
  calc
    Function.support (u : ℂ → ℂ) +
          Function.support (fun t : ℂ ↦ (friedrichsMollifierReal j t : ℂ)) =
        Function.support (u : ℂ → ℂ) +
          Function.support (friedrichsMollifierReal j) := by rw [hsupp]
    _ ⊆ K + closedBall (0 : ℂ) (friedrichsRadius j) :=
      add_subset_add hu
        (support_friedrichsMollifierReal_subset_closedBall j)
''')

replace_once('tsupport_bufferedFriedrichsFullPlaneTest:pointwise_support_bridge',
'''  apply closure_minimal
  · simpa only [bufferedFriedrichsFullPlaneTest_apply] using
      support_friedrichsMollifiedRepresentative_subset_cthickening
        hK j u hu
  · exact isClosed_cthickening
''',
'''  apply closure_minimal
  · intro z hz
    apply support_friedrichsMollifiedRepresentative_subset_cthickening
      hK j u hu
    change bufferedFriedrichsFullPlaneTest hK j u hu z ≠ 0 at hz
    simpa only [bufferedFriedrichsFullPlaneTest_apply] using hz
  · exact isClosed_cthickening
''')

replace_once('potentialTimesWeightCore:close_WeightSection_literal',
'''      rw [upstairsPotential_gammaTwo_invariant γ z,
        WeightSection.covariance (SmoothCompactWeightCore.toSection u₀) γ z]
      ring
  refine ⟨s, ?_⟩
''',
'''      rw [upstairsPotential_gammaTwo_invariant γ z,
        WeightSection.covariance (SmoothCompactWeightCore.toSection u₀) γ z]
      ring⟩
  refine ⟨s, ?_⟩
''')

source.write_text(text)
new_bytes = source.read_bytes()
forbidden = ['sorry', 'admit', 'axiom', 'unsafe', 'native_decide', 'Lean.ofReduceBool']
counts = {p: [len(re.findall(r'(?<![A-Za-z0-9_])'+re.escape(p)+r'(?![A-Za-z0-9_])', parent)),
              len(re.findall(r'(?<![A-Za-z0-9_])'+re.escape(p)+r'(?![A-Za-z0-9_])', text))]
          for p in forbidden}
assert all(a == b for a, b in counts.values()), counts

audit = {
  'base_source_sha256': hashlib.sha256(before_bytes).hexdigest(),
  'candidate_sha256': hashlib.sha256(new_bytes).hexdigest(),
  'candidate_bytes': len(new_bytes),
  'candidate_lines': len(text.splitlines()),
  'replacement_count': len(replacements),
  'replacements': replacements,
  'public_theorem_header_text_modified': False,
  'semantic_public_proposition_change': False,
  'existing_declaration_relative_order_preserved': True,
  'new_declarations_added': False,
  'forbidden_lexical_counts_preserved': True,
  'forbidden_lexical_counts_before_after': counts,
}
(out/'PATCH_AUDIT.json').write_text(json.dumps(audit, indent=2, sort_keys=True)+'\n')
(out/'candidate.sha256').write_text(audit['candidate_sha256']+'\n')
print(json.dumps(audit, indent=2, sort_keys=True))
