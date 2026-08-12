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

old = '''namespace Mock2FA.PaperCorrections.AutomorphicSobolev.ActualScalarDiscriminantPDE

open Mock2FA.PaperCorrections.FredholmBypass'''
new = '''namespace Mock2FA.PaperCorrections.AutomorphicSobolev.ActualScalarDiscriminantPDE

open Mock2FA.PaperCorrections.FredholmBypass
open Mock2FA.PaperCorrections.AutomorphicSobolev.ExplicitDiscriminantPotential.FixedPhaseGraphPotential'''
assert before.count(old) == 1, before.count(old)
after = before.replace(old,new,1)
p.write_text(after)

seq1=[m.group('name') for m in decl_rx.finditer(after)]
fc1={x:len(re.findall(r'(?<![A-Za-z0-9_])'+re.escape(x)+r'(?![A-Za-z0-9_])',after)) for x in forbidden}
assert seq0==seq1 and fc0==fc1
b=p.read_bytes(); sha=hashlib.sha256(b).hexdigest()
audit_path=out/'PATCH_AUDIT.json'; audit=json.loads(audit_path.read_text())
audit['candidate_sha256']=sha
audit.setdefault('targets',[]).append('ActualScalarDiscriminantPDE:reopen_FixedPhaseGraphPotential')
audit['actual_scalar_open_repair']='reopen_FixedPhaseGraphPotential_for_graphPotentialOperator'
audit['v10_diagnostic_run_id']=31602395683
audit['existing_declaration_relative_order_preserved']=True
audit['semantic_public_proposition_change']=False
audit['forbidden_lexical_counts_preserved']=True
audit_path.write_text(json.dumps(audit,indent=2,sort_keys=True)+'\n')
(out/'candidate.sha256').write_text(sha+'\n')
