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
        'weakRaisingSubmodule_isClosed',
        '''  exact isClosed_iInter fun v ↦\n    ContinuousLinearMap.isClosed_ker (raisingDefect n v)''',
        '''  exact isClosed_iInter fun\n      (v : Mock2FA.PaperCorrections.AutomorphicSobolev.HalfWeightDifferentialOperators.InverseEtaFixedPhaseCore ((n + 1) + 1)) ↦\n    ContinuousLinearMap.isClosed_ker (raisingDefect n v)''',
    ),
    (
        'weakLoweringSubmodule_isClosed',
        '''  exact isClosed_iInter fun v ↦\n    ContinuousLinearMap.isClosed_ker (loweringDefect n v)''',
        '''  exact isClosed_iInter fun\n      (v : Mock2FA.PaperCorrections.AutomorphicSobolev.HalfWeightDifferentialOperators.InverseEtaFixedPhaseCore n) ↦\n    ContinuousLinearMap.isClosed_ker (loweringDefect n v)''',
    ),
    (
        'norm_eq_zero_iff_coordinates',
        '''    have hx0 : x = 0 := norm_eq_zero.mp hx\n    simp only [hx0, map_zero]''',
        '''    have hx0 : x = 0 := norm_eq_zero.mp hx\n    simpa [hx0]''',
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

for name, _, _ in replacements:
    marker = 'theorem ' + name
    a0 = before.index(marker)
    a1 = after.index(marker)
    assert before[a0:before.index(':= by', a0) + 5] == after[a1:after.index(':= by', a1) + 5]

b = p.read_bytes()
sha = hashlib.sha256(b).hexdigest()
audit_path = out / 'PATCH_AUDIT.json'
audit = json.loads(audit_path.read_text())
audit['candidate_sha256'] = sha
audit['downstream_probe_verified_targets'] = [x[0] for x in replacements]
audit['downstream_target_public_headers_byte_identical'] = True
audit['existing_declaration_relative_order_preserved'] = True
audit['semantic_public_proposition_change'] = False
audit['forbidden_lexical_counts_preserved'] = True
audit_path.write_text(json.dumps(audit, indent=2, sort_keys=True) + '\n')
(out / 'CANDIDATE_IDENTITY.json').write_text(json.dumps({'sha256': sha, 'bytes': len(b), 'lines': len(after.splitlines())}, indent=2) + '\n')
(out / 'candidate.sha256').write_text(sha + '\n')
