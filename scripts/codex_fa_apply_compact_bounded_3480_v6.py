from pathlib import Path
import hashlib, json, re, sys

out = Path(sys.argv[1])
p = Path('PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean')
before = p.read_text()
decl_rx = re.compile(r'(?m)^(?:protected\s+|private\s+|noncomputable\s+|local\s+)*(?:theorem|lemma|def|abbrev|instance|structure|class)\s+(?P<name>[^\s(:]+)')
seq0 = [m.group('name') for m in decl_rx.finditer(before)]
forbidden = ['sorry','admit','axiom','set_option']
fc0 = {x: len(re.findall(r'(?<![A-Za-z0-9_])'+re.escape(x)+r'(?![A-Za-z0-9_])', before)) for x in forbidden}

start = before.index('theorem graphPotentialOperator_isCompact_of_literalStageFactorization')
end = before.index('end HardStageFactorization', start)
block = before[start:end]
old_start = block.index('  apply isCompactOperator_of_tendsto')
old_end_marker = '''  · exact Filter.Eventually.of_forall fun N ↦
      hardStagePotentialFactor_isCompact n
        (stageRestriction N) (stagePotentialPairing N) (hStage N)
'''
old_end = block.index(old_end_marker, old_start) + len(old_end_marker)
old = block[old_start:old_end]
new = '''  apply isCompactOperator_of_tendsto
    (l := (Filter.atTop : Filter ℕ))
    (F := fun N ↦ (stagePotentialPairing N).comp (stageRestriction N))
    (f := graphPotentialOperator n)
  · have hzero : Filter.Tendsto
        (fun N ↦ (stagePotentialPairing N).comp (stageRestriction N) -
          graphPotentialOperator n)
        Filter.atTop (nhds 0) := by
      rw [(ContinuousLinearMap.hasBasis_nhds_zero_of_basis
        (𝕜₁ := ℂ)
        (E := GraphSobolevCompletion n)
        (F := StrongAntiDual (GraphSobolevCompletion n))
        Metric.nhds_basis_ball).tendsto_right_iff]
      rintro ⟨s, δ⟩ ⟨hs, hδ⟩
      rcases (NormedSpace.isVonNBounded_iff' ℂ).1 hs with ⟨r, hr⟩
      let R : ℝ := max r 0
      have hrR : ∀ x ∈ s, ‖x‖ ≤ R := by
        intro x hx
        exact (hr x hx).trans (le_max_left _ _)
      have hRconst : Filter.Tendsto (fun _ : ℕ ↦ R) Filter.atTop (nhds R) :=
        tendsto_const_nhds
      have hscaled : Filter.Tendsto
          (fun N ↦ discriminantCuspEpsilon N * R)
          Filter.atTop (nhds 0) := by
        simpa using discriminantCuspEpsilon_tendsto_zero.mul hRconst
      filter_upwards [(tendsto_order.1 hscaled).2 δ hδ] with N hN
      intro x hx
      have heN : 0 ≤ discriminantCuspEpsilon N :=
        (norm_nonneg
          ((stagePotentialPairing N).comp (stageRestriction N) -
            graphPotentialOperator n)).trans (hTail N)
      have hpoint :
          ‖(((stagePotentialPairing N).comp (stageRestriction N) -
            graphPotentialOperator n) x)‖ < δ := by
        calc
          ‖(((stagePotentialPairing N).comp (stageRestriction N) -
              graphPotentialOperator n) x)‖ ≤
              ‖(stagePotentialPairing N).comp (stageRestriction N) -
                graphPotentialOperator n‖ * ‖x‖ :=
            ((stagePotentialPairing N).comp (stageRestriction N) -
              graphPotentialOperator n).le_opNorm x
          _ ≤ discriminantCuspEpsilon N * R :=
            mul_le_mul (hTail N) (hrR x hx) (norm_nonneg x) heN
          _ < δ := hN
      simpa [Metric.mem_ball, dist_zero_right] using hpoint
    have hconst : Filter.Tendsto
        (fun _ : ℕ ↦ graphPotentialOperator n)
        Filter.atTop (nhds (graphPotentialOperator n)) :=
      tendsto_const_nhds
    have hadd := hzero.add hconst
    simpa using hadd
  · exact Filter.Eventually.of_forall fun N ↦
      hardStagePotentialFactor_isCompact n
        (stageRestriction N) (stagePotentialPairing N) (hStage N)
'''
block = block[:old_start] + new + block[old_end:]
after = before[:start] + block + before[end:]
p.write_text(after)

seq1 = [m.group('name') for m in decl_rx.finditer(after)]
fc1 = {x: len(re.findall(r'(?<![A-Za-z0-9_])'+re.escape(x)+r'(?![A-Za-z0-9_])', after)) for x in forbidden}
assert seq0 == seq1
assert fc0 == fc1
name='graphPotentialOperator_isCompact_of_literalStageFactorization'; marker='theorem '+name
a0=before.index(marker); a1=after.index(marker)
assert before[a0:before.index(':= by',a0)+5] == after[a1:after.index(':= by',a1)+5]

b=p.read_bytes(); sha=hashlib.sha256(b).hexdigest()
audit_path=out/'PATCH_AUDIT.json'; audit=json.loads(audit_path.read_text())
audit['candidate_sha256']=sha
audit.setdefault('targets',[]).append(name+':direct_bounded_convergence')
audit['compactness_bounded_repair']='prove_CLM_bounded_convergence_nhds_directly_from_opNorm_tail'
audit['compactness_bounded_probe_run_id']=31604164707
audit['existing_declaration_relative_order_preserved']=True
audit['semantic_public_proposition_change']=False
audit['forbidden_lexical_counts_preserved']=True
audit_path.write_text(json.dumps(audit,indent=2,sort_keys=True)+'\n')
(out/'candidate.sha256').write_text(sha+'\n')
