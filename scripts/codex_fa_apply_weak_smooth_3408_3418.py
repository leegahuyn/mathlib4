from pathlib import Path
import hashlib
import json
import re
import sys

out = Path(sys.argv[1])
p = Path('PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean')
before = p.read_text()
decl_rx = re.compile(r'(?m)^(?:protected\s+|private\s+|noncomputable\s+|local\s+)*(?:theorem|lemma|def|abbrev|instance|structure|class)\s+(?P<name>[^\s(:]+)')
seq0 = [m.group('name') for m in decl_rx.finditer(before)]
forbidden = ['sorry', 'admit', 'axiom', 'set_option']
fc0 = {x: len(re.findall(r'(?<![A-Za-z0-9_])' + re.escape(x) + r'(?![A-Za-z0-9_])', before)) for x in forbidden}

replacements = [
    (
        'successorSmoothGraph_mem_weightedWeakSubmodule',
        '''    simp only [baseProjection_apply, raiseProjection_apply,
      DefinitionOneSobolev.QuotientHilbertCoordinates.graph_fst,
      DefinitionOneSobolev.QuotientHilbertCoordinates.graph_snd_fst,
      FixedPhaseClosedOperators.successorGraphCoordinates]
    have h :=
      FixedPhaseClosedOperators.physicalLoweringGreenIdentityOnCore_unconditional
          (n := n + 1) v u
    linear_combination h
  · intro v
    rw [loweringDefect_apply]
    simp only [baseProjection_apply, lowerProjection_apply,
      DefinitionOneSobolev.QuotientHilbertCoordinates.graph_fst,
      DefinitionOneSobolev.QuotientHilbertCoordinates.graph_snd_snd,
      FixedPhaseClosedOperators.successorGraphCoordinates,
      FixedPhaseClosedOperators.reindexedActualLoweredCoordinate_eq_lowerFromSuccCoordinate]
    have h :=
      FixedPhaseClosedOperators.physicalRaisingGreenIdentityOnCore_unconditional
          (n := n) v u
    linear_combination h''',
        '''    simp only [baseProjection_apply, raiseProjection_apply,
      DefinitionOneSobolev.QuotientHilbertCoordinates.graph_fst,
      DefinitionOneSobolev.QuotientHilbertCoordinates.graph_snd_fst,
      FixedPhaseClosedOperators.successorGraphCoordinates_base,
      FixedPhaseClosedOperators.successorGraphCoordinates_raised]
    have h :=
      FixedPhaseClosedOperators.physicalLoweringGreenIdentityOnCore_unconditional
          (n := n + 1) v u
    linear_combination h
  · intro v
    rw [loweringDefect_apply]
    simp only [baseProjection_apply, lowerProjection_apply,
      DefinitionOneSobolev.QuotientHilbertCoordinates.graph_fst,
      DefinitionOneSobolev.QuotientHilbertCoordinates.graph_snd_snd,
      FixedPhaseClosedOperators.successorGraphCoordinates_base,
      FixedPhaseClosedOperators.successorGraphCoordinates_lowered,
      FixedPhaseClosedOperators.reindexedActualLoweredCoordinate_eq_lowerFromSuccCoordinate]
    have h :=
      FixedPhaseClosedOperators.physicalRaisingGreenIdentityOnCore_unconditional
          (n := n) v u
    linear_combination h''',
    ),
    (
        'norm_smoothCoreMap_sq',
        '''  simpa only [FixedPhaseClosedOperators.successorGraphCoordinates,
    FixedPhaseClosedOperators.reindexedActualLoweredCoordinate_eq_lowerFromSuccCoordinate] using
    (FixedPhaseClosedOperators.successorGraphCoordinates n).graph_norm_sq u''',
        '''  simpa only [FixedPhaseClosedOperators.successorGraphCoordinates_base,
    FixedPhaseClosedOperators.successorGraphCoordinates_raised,
    FixedPhaseClosedOperators.successorGraphCoordinates_lowered,
    FixedPhaseClosedOperators.reindexedActualLoweredCoordinate_eq_lowerFromSuccCoordinate] using
    (FixedPhaseClosedOperators.successorGraphCoordinates n).graph_norm_sq u''',
    ),
    (
        'graphExtension_mem_weightedWeakSubmodule',
        '''  intro y
  rw [Q.graphExtension_coe]
  rcases y.property with ⟨u, rfl⟩
  exact successorSmoothGraph_mem_weightedWeakSubmodule n u''',
        '''  intro y
  rw [Q.graphExtension_coe]
  rcases y.property with ⟨u, hu⟩
  rw [← hu]
  exact successorSmoothGraph_mem_weightedWeakSubmodule n u''',
    ),
    (
        'denseRange_smoothCoreMap_iff_surjective_comparison:first',
        '''    exact ⟨
      (FixedPhaseClosedOperators.successorGraphCoordinates n).sectionCoreMap u,
      (graphCompletionToWeightedWeak_sectionCoreMap n u).symm⟩''',
        '''    exact ⟨
      (FixedPhaseClosedOperators.successorGraphCoordinates n).sectionCoreMap u,
      graphCompletionToWeightedWeak_sectionCoreMap n u⟩''',
    ),
    (
        'denseRange_smoothCoreMap_iff_surjective_comparison:second',
        '''    simpa only [Function.comp_apply,
      graphCompletionToWeightedWeak_sectionCoreMap] using hComp''',
        '''    change DenseRange (fun u ↦
      graphCompletionToWeightedWeak n
        ((FixedPhaseClosedOperators.successorGraphCoordinates n).sectionCoreMap u)) at hComp
    simpa only [graphCompletionToWeightedWeak_sectionCoreMap] using hComp''',
    ),
]

after = before
for name, old, new in replacements:
    count = after.count(old)
    assert count == 1, (name, count)
    after = after.replace(old, new, 1)

p.write_text(after)
seq1 = [m.group('name') for m in decl_rx.finditer(after)]
fc1 = {x: len(re.findall(r'(?<![A-Za-z0-9_])' + re.escape(x) + r'(?![A-Za-z0-9_])', after)) for x in forbidden}
assert seq0 == seq1
assert fc0 == fc1

for name in [
    'successorSmoothGraph_mem_weightedWeakSubmodule',
    'norm_smoothCoreMap_sq',
    'graphExtension_mem_weightedWeakSubmodule',
    'denseRange_smoothCoreMap_iff_surjective_comparison',
]:
    marker = 'theorem ' + name
    a0 = before.index(marker)
    a1 = after.index(marker)
    assert before[a0:before.index(':= by', a0) + 5] == after[a1:after.index(':= by', a1) + 5]

b = p.read_bytes()
sha = hashlib.sha256(b).hexdigest()
audit_path = out / 'PATCH_AUDIT.json'
audit = json.loads(audit_path.read_text())
audit['candidate_sha256'] = sha
audit.setdefault('targets', []).extend([
    'successorSmoothGraph_mem_weightedWeakSubmodule',
    'norm_smoothCoreMap_sq',
    'graphExtension_mem_weightedWeakSubmodule',
    'denseRange_smoothCoreMap_iff_surjective_comparison',
])
audit['weak_smooth_probe_verified_repairs'] = 5
audit['weak_smooth_target_public_headers_byte_identical'] = True
audit['existing_declaration_relative_order_preserved'] = True
audit['semantic_public_proposition_change'] = False
audit['forbidden_lexical_counts_preserved'] = True
audit_path.write_text(json.dumps(audit, indent=2, sort_keys=True) + '\n')
(out / 'CANDIDATE_IDENTITY.json').write_text(json.dumps({'sha256': sha, 'bytes': len(b), 'lines': len(after.splitlines())}, indent=2) + '\n')
(out / 'candidate.sha256').write_text(sha + '\n')
