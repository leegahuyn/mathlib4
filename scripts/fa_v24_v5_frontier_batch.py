#!/usr/bin/env python3
from pathlib import Path
import base64,gzip,hashlib,json,os,re,subprocess,sys
if len(sys.argv)!=3: raise SystemExit('usage: fa_v24_v5_frontier_batch.py <source> <outdir>')
source=Path(sys.argv[1]); out=Path(sys.argv[2]); out.mkdir(parents=True,exist_ok=True)
base_locked='a26135f6674fb4111307c471b92b036b2d2f4a529dba3bb67bbfd7a7e35a90ce'
patch_locked='b590a8598fbb45bc7c83707157487e788730e739cf4ca949b40e0fb22d46a93c'
candidate_locked='eadf1d9b129babe4a67f1cd5352f82a72fc844f3c0c0aa1578fdb35e7dc89d5f'
PATCH_GZ_B64='H4sIAH04fWoC/+1Y3W7bNhS+91OcS7mynDlbnR8gQIKuxga0qBcP20VhqLRMWcRokiOp2M7VMOxJ+mh9kh6Kkq00bSz3Qt5fgBiSLPJ85+c7/I6jKAJyMtZsSTizm0lGSfoL1SxlCbFMipPXMvntNB7lInG3hN/g/8Yw0+eUiE4YhjD7+uXX1xB9dz58ftY7/RbC8uoCrq87sPsLcriEyVJKm/2US8uosC/kUpHEVtt24R7C3ZJTeAacKE4SektWECiiqH6jZ8y+XCspcD2I7uEWLq9gtumEAJxaIHjrrgEKD0c3/bGz8kJqTYsVpn+TW7mUWmUsmciZ5PSu/wPh6a+ULTL7PUtTqtEQI/wNLiRWatP/UdxRbehLS0ZsTefjjBiKW9I+lyuqR1ouJ3mSgPCWEXgrxjVhhoKAvFt5P2vX+wKA836s6bxt74vQb73PyB2FbJLPIFjDBsumDQxYrnBZeY22+wbtO/NX+BlCEA0QyIe//uzChz/eO1RVpQIQpfjGrbEbRft0bf3jJCNiQbeBXO+v/wiCzf63rqotm236CHsDG96CYUsFbzEOMf09JvN5LOhi6jitV/jYaikW2JVEwhThLoRxEYhpJ9r6HhUgg6CMp78vnlURznfPWi22Gs9rANpne7dbC8pRiH6c+Hvn2+a2L8taRdYKEUjX9dz2Wq5HVYZ+38mItIf4EbManalRrcKC/yDFWi2ymqf7U3qEzDzB/vb5//fNjCNb6A86L0Qetomelyd4M33YVoIg7w++5kwmDZbVBcqh+8+awLrcKYvGISpEghQogN62Uj1WPgltusX0OeHileWrW6fe2qv1uCBdnCJMqdl9MbS5+of7HabbV61h8mg8si9g4kxQouNELmdM+O9c1EKHsxwozwbf9AYXbqA8Gwx7p8PtQBkEXhpOkkzLOUNiaE9CsJC3yvjGfEdJXb75CHrdLk62mhrjI+Wcqc2r/88s/5iZ5ZPCrKaWnffwcGqB4DOzjh9WdydnYOtwlbQ+h69zbpni5S8124XHoMHBh149JFGd2Y8CcZxzvLnw3SXn2YNxJwj2JOpYAuWAeeDJWTxWkgm7wn7f89s/4W/Fg7AMzRervpHAqfH9EyYfSJWDdMu/TrX0wCxzHruPacXNJtlukmjXFLELdqADJ1EEt5SJOV3jE7AZhUIfRHglIj9KoRhQ0rBCDJBES2PgXSDCQTcaXIl3ZaMwpTo4fz7sDZ04OB9e9M5KbYCnDNxVvThBJGNqMVxGipHUCRquI8NXlkTF91TLHjAhUKy461i76PtYpLzCvt0IFGHOKQNkQZgwtvAFI50TjqF0KYDUpSZSLjfgUIChimACsfGXb5iqBAB+xuVKS5mCpcYaWDH83u05LwsgocCsoTwFIubuGyxag3H4CKn97Z/1FwAA'
before=source.read_bytes(); bt=before.decode(); base=hashlib.sha256(before).hexdigest(); assert base==base_locked,(base,base_locked)
expected=os.environ.get('BASE_SOURCE_SHA256')
if expected: assert base==expected,(base,expected)
pb=gzip.decompress(base64.b64decode(PATCH_GZ_B64)); ps=hashlib.sha256(pb).hexdigest(); assert ps==patch_locked,(ps,patch_locked)
(out/'decoded.patch').write_bytes(pb)
p=subprocess.run(['patch','-p1','--batch','--forward'],input=pb,capture_output=True)
(out/'patch.stdout').write_bytes(p.stdout); (out/'patch.stderr').write_bytes(p.stderr)
if p.returncode: raise SystemExit(f'patch failed {p.returncode}: {p.stdout.decode(errors="replace")} {p.stderr.decode(errors="replace")}')
after=source.read_bytes(); at=after.decode(); cand=hashlib.sha256(after).hexdigest(); assert cand==candidate_locked,(cand,candidate_locked)
assert len(at.splitlines())==61442
decl_re=re.compile(r'(?m)^(?:protected\s+|private\s+|noncomputable\s+|local\s+)*(?:theorem|lemma|def|abbrev|instance|structure|class)\s+([^\s(:]+)')
assert decl_re.findall(bt)==decl_re.findall(at),'declaration sequence changed'
th_re=re.compile(r'(?m)^(?:protected\s+|private\s+|noncomputable\s+|local\s+)*(theorem|lemma)\s+([^\s(:]+)')
def headers(s):
    starts=[m.start() for m in decl_re.finditer(s)]; r=[]
    for m in th_re.finditer(s):
        nxt=next((x for x in starts if x>m.start()),len(s)); block=s[m.start():nxt]; cut=block.find(':= by')
        if cut<0: cut=block.find(':=')
        r.append((m.group(2),re.sub(r'\s+',' ',block if cut<0 else block[:cut]).strip()))
    return r
assert headers(bt)==headers(at),'theorem/lemma proposition header changed'
forbidden=['sorry','admit','axiom','unsafe','native_decide','Lean.ofReduceBool','set_option']; counts={}
for w in forbidden:
    pat=r'(?<![A-Za-z0-9_])'+re.escape(w)+r'(?![A-Za-z0-9_])'; counts[w]=[len(re.findall(pat,bt)),len(re.findall(pat,at))]
assert all(a==b for a,b in counts.values()),counts
audit={'schema':'fa-v24-v5-inline-b590-strict-v2','base_source_sha256':base,'patch_sha256':ps,'candidate_sha256':cand,'candidate_bytes':len(after),'candidate_lines':len(at.splitlines()),'repairs':['strongPrincipalCore_apply_pointwise_v5_canonical_sub_bridge','strongSchrodingerCore_apply_pointwise_v5_canonical_sub_bridge','corePeterssonForcing_zero_application'],'semantic_public_proposition_change':False,'theorem_lemma_headers_identical':True,'declaration_sequence_identical':True,'forbidden_lexical_counts_preserved':True,'forbidden_lexical_counts_before_after':counts,'patch_transport':'inline_gzip_base64_locked'}
(out/'PATCH_AUDIT.json').write_text(json.dumps(audit,indent=2,sort_keys=True)+'\n');(out/'candidate.sha256').write_text(cand+'\n');print(json.dumps(audit,indent=2,sort_keys=True))
