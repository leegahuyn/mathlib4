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

old = 'inner_add_right, inner_smul_right, map_ofReal]'
assert before.count(old) == 2, before.count(old)
after = before.replace(old, 'inner_add_right, inner_smul_right, Complex.conj_ofReal]', 2)

oldd = '''          _ = inner ℂ ((c : ℂ) • (z : H) + A z) y -
                inner ℂ ((c : ℂ) • (z : H) + A z) (x : H) := by
              rw [d, inner_sub_right]'''
newd = '''          _ = inner ℂ ((c : ℂ) • (z : H) + A z) y -
                inner ℂ ((c : ℂ) • (z : H) + A z) (x : H) := by
              change inner ℂ ((c : ℂ) • (z : H) + A z) (y - (x : H)) =
                inner ℂ ((c : ℂ) • (z : H) + A z) y -
                  inner ℂ ((c : ℂ) • (z : H) + A z) (x : H)
              rw [inner_sub_right]'''
assert after.count(oldd) == 1, after.count(oldd)
after = after.replace(oldd, newd, 1)
p.write_text(after)

seq1 = [m.group('name') for m in decl_rx.finditer(after)]
fc1 = {x: len(re.findall(r'(?<![A-Za-z0-9_])' + re.escape(x) + r'(?![A-Za-z0-9_])', after)) for x in forbidden}
assert seq0 == seq1
assert fc0 == fc1
name = 'LinearPMap.isSelfAdjoint_of_realShift_surjective'
marker = 'theorem ' + name
a0 = before.index(marker)
a1 = after.index(marker)
assert before[a0:before.index(':= by', a0) + 5] == after[a1:after.index(':= by', a1) + 5]

b = p.read_bytes()
sha = hashlib.sha256(b).hexdigest()
audit_path = out / 'PATCH_AUDIT.json'
audit = json.loads(audit_path.read_text())
audit['candidate_sha256'] = sha
audit.setdefault('targets', []).append(name)
audit['real_shift_repair'] = 'Complex.conj_ofReal_and_explicit_local_d_change'
audit['real_shift_probe_run_id'] = 31593247644
audit['existing_declaration_relative_order_preserved'] = True
audit['semantic_public_proposition_change'] = False
audit['forbidden_lexical_counts_preserved'] = True
audit_path.write_text(json.dumps(audit, indent=2, sort_keys=True) + '\n')
(out / 'candidate.sha256').write_text(sha + '\n')
