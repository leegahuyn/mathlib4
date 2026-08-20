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

old = '''noncomputable def embeddedMassForm (J : V →L[ℂ] H) :
    ContinuousSesquilinearForm V :=
  (embeddedMassLinear J).mkContinuous₂ (‖J‖ ^ 2)
    (embeddedMassLinear_bound J)'''
new = '''noncomputable def embeddedMassForm (J : V →L[ℂ] H) :
    ContinuousSesquilinearForm V :=
  LinearMap.mkContinuous₂
    ({ toFun := fun u => (embeddedMassLinear J u).toLinearMap
       map_add' := by
         intro u w
         ext v
         simp
       map_smul' := by
         intro c u
         ext v
         simp } : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)
    (‖J‖ ^ 2)
    (by
      intro u v
      simpa using embeddedMassLinear_bound J u v)'''
assert before.count(old) == 1, before.count(old)
after = before.replace(old, new, 1)
p.write_text(after)

seq1 = [m.group('name') for m in decl_rx.finditer(after)]
fc1 = {x: len(re.findall(r'(?<![A-Za-z0-9_])' + re.escape(x) + r'(?![A-Za-z0-9_])', after)) for x in forbidden}
assert seq0 == seq1
assert fc0 == fc1
marker = 'noncomputable def embeddedMassForm'
a0 = before.index(marker)
a1 = after.index(marker)
assert before[a0:before.index(':=', a0) + 2] == after[a1:after.index(':=', a1) + 2]

b = p.read_bytes()
sha = hashlib.sha256(b).hexdigest()
audit_path = out / 'PATCH_AUDIT.json'
audit = json.loads(audit_path.read_text())
audit['candidate_sha256'] = sha
audit.setdefault('targets', []).append('embeddedMassForm')
audit['embedded_mass_repair'] = 'inline_raw_semilinear_layer_for_LinearMap_mkContinuous2'
audit['embedded_mass_probe_run_id'] = 31593915141
audit['embedded_mass_public_header_byte_identical'] = True
audit['existing_declaration_relative_order_preserved'] = True
audit['semantic_public_proposition_change'] = False
audit['forbidden_lexical_counts_preserved'] = True
audit_path.write_text(json.dumps(audit, indent=2, sort_keys=True) + '\n')
(out / 'candidate.sha256').write_text(sha + '\n')
