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
forbidden = ['sorry','admit','axiom','set_option']
fc0 = {x: len(re.findall(r'(?<![A-Za-z0-9_])'+re.escape(x)+r'(?![A-Za-z0-9_])', before)) for x in forbidden}
after = before

old1 = '''theorem reciprocalFourierTail_tendsto_zero (C : ℝ) :
    Filter.Tendsto (reciprocalFourierTail C) Filter.atTop (nhds 0) := by
  unfold reciprocalFourierTail
  simpa only [div_eq_mul_inv, one_div, mul_zero] using
    tendsto_const_nhds.mul
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Filter.Tendsto (fun N : ℕ ↦ (1 : ℝ) / (N + 1)) Filter.atTop (nhds 0))'''
new1 = '''theorem reciprocalFourierTail_tendsto_zero (C : ℝ) :
    Filter.Tendsto (reciprocalFourierTail C) Filter.atTop (nhds 0) := by
  unfold reciprocalFourierTail
  have hconst :
      Filter.Tendsto (fun _ : ℕ => C) Filter.atTop (nhds C) :=
    tendsto_const_nhds
  simpa only [div_eq_mul_inv, one_div, one_mul, mul_zero] using
    hconst.mul
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Filter.Tendsto (fun N : ℕ => (1 : ℝ) / (N + 1)) Filter.atTop (nhds 0))'''
assert after.count(old1) == 1, after.count(old1)
after = after.replace(old1,new1,1)

old2 = '''theorem rankin_origin_power_integrable_iff
    {β T : ℝ} (hT : 0 < T) :
    IntegrableOn (fun y : ℝ => y ^ (β - 2)) (Set.Ioo 0 T) ↔
      1 < β := by
  rw [intervalIntegral.integrableOn_Ioo_rpow_iff hT]
  linarith'''
new2 = '''theorem rankin_origin_power_integrable_iff
    {β T : ℝ} (hT : 0 < T) :
    IntegrableOn (fun y : ℝ => y ^ (β - 2)) (Set.Ioo 0 T) ↔
      1 < β := by
  rw [intervalIntegral.integrableOn_Ioo_rpow_iff hT]
  constructor <;> intro h <;> linarith'''
assert after.count(old2) == 1, after.count(old2)
after = after.replace(old2,new2,1)

p.write_text(after)
seq1=[m.group('name') for m in decl_rx.finditer(after)]
fc1={x:len(re.findall(r'(?<![A-Za-z0-9_])'+re.escape(x)+r'(?![A-Za-z0-9_])',after)) for x in forbidden}
assert seq0==seq1 and fc0==fc1
for name in ['reciprocalFourierTail_tendsto_zero','rankin_origin_power_integrable_iff']:
    marker='theorem '+name; a0=before.index(marker); a1=after.index(marker)
    assert before[a0:before.index(':= by',a0)+5] == after[a1:after.index(':= by',a1)+5]

b=p.read_bytes(); sha=hashlib.sha256(b).hexdigest()
audit_path=out/'PATCH_AUDIT.json'; audit=json.loads(audit_path.read_text())
audit['candidate_sha256']=sha
audit.setdefault('targets',[]).extend(['reciprocalFourierTail_tendsto_zero:typed_constant_tendsto','rankin_origin_power_integrable_iff:split_iff_directions'])
audit['post3519_scalar_repair']='typed_constant_tendsto_and_explicit_iff_directions'
audit['post3519_scalar_probe_run_id']=31601629317
audit['existing_declaration_relative_order_preserved']=True
audit['semantic_public_proposition_change']=False
audit['forbidden_lexical_counts_preserved']=True
audit_path.write_text(json.dumps(audit,indent=2,sort_keys=True)+'\n')
(out/'candidate.sha256').write_text(sha+'\n')
