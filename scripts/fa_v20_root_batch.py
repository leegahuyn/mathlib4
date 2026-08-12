#!/usr/bin/env python3
from pathlib import Path
import hashlib, json, os, re, sys

if len(sys.argv) != 3:
    raise SystemExit('usage: fa_v20_root_batch.py <source> <outdir>')
source = Path(sys.argv[1])
out = Path(sys.argv[2])
out.mkdir(parents=True, exist_ok=True)
expected_base = os.environ.get('BASE_SOURCE_SHA256', '')
before_bytes = source.read_bytes()
base_sha = hashlib.sha256(before_bytes).hexdigest()
if expected_base:
    assert base_sha == expected_base, (base_sha, expected_base)
text = before_bytes.decode()
parent = text
replacements = []

def replace_once(label: str, old: str, new: str):
    global text
    n = text.count(old)
    assert n == 1, (label, n)
    text = text.replace(old, new, 1)
    replacements.append(label)

# decl 3584: make the inherited submodule norm explicit before reusing the X-valued bound.
replace_once(
    'fredholmDefect_rangeOrthogonal_finiteDimensional:explicit_subtype_norm_change',
'''  have hRbound : ∀ u, ‖u‖ ≤ (1 : ℝ) * ‖R u‖ := by
    intro u
    simpa only [one_mul, R, compactCokernelControl_apply] using
      norm_le_compact_apply_of_mem_fredholmDefect_range_orthogonal K u
''',
'''  have hRbound : ∀ u, ‖u‖ ≤ (1 : ℝ) * ‖R u‖ := by
    intro u
    change ‖(u : X)‖ ≤ (1 : ℝ) * ‖R u‖
    simpa only [one_mul, R, compactCokernelControl_apply] using
      norm_le_compact_apply_of_mem_fredholmDefect_range_orthogonal K u
''')

# decls 3621/3624: this reopened namespace lacked the CLM namespace, so bare lsmul was autoImplicit.
replace_once(
    'FixedPhaseReducedChartFriedrichs:P3_26_open_ContinuousLinearMap',
'''namespace Mock2FA.PaperCorrections.AutomorphicSobolev
namespace FixedPhaseReducedChartFriedrichs

open Set Function Topology Filter MeasureTheory Metric
open scoped Convolution ContDiff
open FixedPhaseAffineFriedrichs
open FixedPhaseNormalizedFriedrichs
''',
'''namespace Mock2FA.PaperCorrections.AutomorphicSobolev
namespace FixedPhaseReducedChartFriedrichs

open Set Function Topology Filter MeasureTheory Metric
open ContinuousLinearMap
open scoped Convolution ContDiff
open FixedPhaseAffineFriedrichs
open FixedPhaseNormalizedFriedrichs
''')

# decls 3667/3671/3676 and siblings use the same unqualified lsmul/lsmul_apply API family.
replace_once(
    'FixedPhaseNormalizedFriedrichs:open_ContinuousLinearMap',
'''namespace Mock2FA.PaperCorrections.AutomorphicSobolev
namespace FixedPhaseNormalizedFriedrichs

open Set Function Topology Filter MeasureTheory Metric
open scoped Convolution ContDiff Distributions
open FixedPhaseAffineFriedrichs

noncomputable section

/-! ### Compact smooth tests as planar `L²` vectors -/
''',
'''namespace Mock2FA.PaperCorrections.AutomorphicSobolev
namespace FixedPhaseNormalizedFriedrichs

open Set Function Topology Filter MeasureTheory Metric
open ContinuousLinearMap
open scoped Convolution ContDiff Distributions
open FixedPhaseAffineFriedrichs

noncomputable section

/-! ### Compact smooth tests as planar `L²` vectors -/
''')

# Later P3 reopening has the same missing namespace root; batch the safe name-resolution sibling.
replace_once(
    'FixedPhaseReducedChartFriedrichs:essential_support_open_ContinuousLinearMap',
'''namespace Mock2FA.PaperCorrections.AutomorphicSobolev
namespace FixedPhaseReducedChartFriedrichs

open Set Function Topology Filter MeasureTheory Metric
open scoped Convolution ContDiff Distributions
open FixedPhaseAffineFriedrichs
open FixedPhaseNormalizedFriedrichs
open FixedPhasePlanarLocalization

noncomputable section

/-- Representative-independent compact support for a planar `L2` class. -/
''',
'''namespace Mock2FA.PaperCorrections.AutomorphicSobolev
namespace FixedPhaseReducedChartFriedrichs

open Set Function Topology Filter MeasureTheory Metric
open ContinuousLinearMap
open scoped Convolution ContDiff Distributions
open FixedPhaseAffineFriedrichs
open FixedPhaseNormalizedFriedrichs
open FixedPhasePlanarLocalization

noncomputable section

/-- Representative-independent compact support for a planar `L2` class. -/
''')

# decl 3628: support membership is definitionally pointwise nonzeroness, but simpa did not change the goal.
replace_once(
    'tsupport_bufferedFriedrichsFullPlaneTest:explicit_support_membership_change',
'''    change bufferedFriedrichsFullPlaneTest hK j u hu z ≠ 0 at hz
    simpa only [bufferedFriedrichsFullPlaneTest_apply] using hz
''',
'''    change bufferedFriedrichsFullPlaneTest hK j u hu z ≠ 0 at hz
    change friedrichsMollifiedRepresentative j u z ≠ 0
    simpa only [bufferedFriedrichsFullPlaneTest_apply] using hz
''')

source.write_text(text)
after_bytes = source.read_bytes()

# Structural/trust audit.
decl_re = re.compile(r'(?m)^(?:protected\s+|private\s+|noncomputable\s+|local\s+)*(?:theorem|lemma|def|abbrev|instance|structure|class)\s+([^\s(:]+)')
before_decls = decl_re.findall(parent)
after_decls = decl_re.findall(text)
assert before_decls == after_decls, 'declaration sequence changed'
forbidden = ['sorry', 'admit', 'axiom', 'unsafe', 'native_decide', 'Lean.ofReduceBool']
counts = {}
for p in forbidden:
    pat = r'(?<![A-Za-z0-9_])' + re.escape(p) + r'(?![A-Za-z0-9_])'
    counts[p] = [len(re.findall(pat, parent)), len(re.findall(pat, text))]
assert all(a == b for a, b in counts.values()), counts

audit = {
    'schema': 'fa-v20-root-batch',
    'base_source_sha256': base_sha,
    'candidate_sha256': hashlib.sha256(after_bytes).hexdigest(),
    'candidate_bytes': len(after_bytes),
    'candidate_lines': len(text.splitlines()),
    'replacement_count': len(replacements),
    'replacements': replacements,
    'public_theorem_header_text_modified': False,
    'semantic_public_proposition_change': False,
    'existing_declaration_relative_order_preserved': True,
    'declaration_sequence_identical': True,
    'new_declarations_added': False,
    'forbidden_lexical_counts_preserved': True,
    'forbidden_lexical_counts_before_after': counts,
}
(out/'PATCH_AUDIT.json').write_text(json.dumps(audit, indent=2, sort_keys=True)+'\n')
(out/'candidate.sha256').write_text(audit['candidate_sha256']+'\n')
print(json.dumps(audit, indent=2, sort_keys=True))

# Trigger marker: v20-registered-highcap-1
