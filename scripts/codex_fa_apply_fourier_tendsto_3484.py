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

start = before.index('theorem twoTorusFiniteFourierProjection_tendsto')
end = before.index('end P5LocalFourierRellich', start)
block = before[start:end]
old = '''  simpa only [Function.comp_apply, twoTorusFiniteFourierProjection_apply] using
    (UnitAddTorus.hasSum_mFourier_series_L2 f).comp
      twoTorusCanonicalModes_tendsto_atTop'''
new = '''  simp only [twoTorusFiniteFourierProjection_apply]
  change Filter.Tendsto
    ((fun s => ∑ k ∈ s,
      UnitAddTorus.mFourierCoeff (f : TwoTorusFun) k •
        UnitAddTorus.mFourierLp 2 k) ∘ twoTorusCanonicalModes)
    Filter.atTop (nhds f)
  exact (UnitAddTorus.hasSum_mFourier_series_L2 f).comp
    twoTorusCanonicalModes_tendsto_atTop'''
assert block.count(old) == 1, block.count(old)
block = block.replace(old, new, 1)
after = before[:start] + block + before[end:]
p.write_text(after)

seq1 = [m.group('name') for m in decl_rx.finditer(after)]
fc1 = {x: len(re.findall(r'(?<![A-Za-z0-9_])' + re.escape(x) + r'(?![A-Za-z0-9_])', after)) for x in forbidden}
assert seq0 == seq1
assert fc0 == fc1
name = 'twoTorusFiniteFourierProjection_tendsto'
marker = 'theorem ' + name
a0 = before.index(marker)
a1 = after.index(marker)
assert before[a0:before.index(':= by', a0) + 5] == after[a1:after.index(':= by', a1) + 5]

b = p.read_bytes()
sha = hashlib.sha256(b).hexdigest()
audit_path = out / 'PATCH_AUDIT.json'
audit = json.loads(audit_path.read_text())
audit['candidate_sha256'] = sha
audit.setdefault('targets', []).append(name + ':explicit_tendsto_composition')
audit['fourier_tendsto_repair'] = 'change_lambda_sum_to_explicit_composition_before_HasSum_comp'
audit['fourier_tendsto_probe_run_id'] = 31597593334
audit['existing_declaration_relative_order_preserved'] = True
audit['semantic_public_proposition_change'] = False
audit['forbidden_lexical_counts_preserved'] = True
audit_path.write_text(json.dumps(audit, indent=2, sort_keys=True) + '\n')
(out / 'candidate.sha256').write_text(sha + '\n')
