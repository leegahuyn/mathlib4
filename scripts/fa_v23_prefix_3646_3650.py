#!/usr/bin/env python3
import base64, hashlib, json, os, re, subprocess, sys, zlib
from pathlib import Path

if len(sys.argv) != 3:
    raise SystemExit("usage: fa_v23_prefix_3646_3650.py <source> <outdir>")
source=Path(sys.argv[1]); out=Path(sys.argv[2]); out.mkdir(parents=True,exist_ok=True)
before=source.read_bytes(); before_text=before.decode("utf-8")
base_sha=hashlib.sha256(before).hexdigest()
expected_base="6b73cb7d68157c861830dbefd30ae7bb0ddcc68b911fc89b49802836752bc965"
assert base_sha==expected_base,(base_sha,expected_base)
PATCH_B64="eNrlV11P2zAUfe+vOPKtk4B0taibVDSNB1ofpgkJX9A+WjpxUtuN6zjQiP++aRtKp4r2Zcx9znXvw9e+Yw1z44xI1q4HwIqtp1hVX/dIlY3ZyZ2FsyODHgLyhJW4cd1VIvkqiOR19jt91vgc/gN3Zsdw8B4lC0GJYo1OU6CMseJXezDGAVgeet8kt9MX0bKuUql03OruFHbGyj5p8Dl6+kyaVJleBbuc7oAXRCu24zXBfLvpDGt3jQM+aofRj8BrRTqYbFcoVwjBE0ESQhqqSwhZzM9y0vt88vBL6jb+r7i3EEHd3mh+dX7JNbdRhH6HHQu6brIghsiNx4Ro/EMl50bMEC/I5JniKYxgKfngXR2ABGjOX19LeIf+cpPQh5SFiRHtHlAfSIJVBxnyVPbkprduJmwfyISXbsxZtQsBe/LVsfuas0i5QYNrbmGtgSSWP71cVtNOACu4u0nhA106/o5LmQ2N2wWb2Zddc0a79t5tdx9pZ81vRrOzV8eH/uqz+VOWcpZ6zDKn9COIafNjZDkyxe5TtWOazRfDndHeKNXh8Fkx+jYPgzEc5RBwdMkxueHraF5O9RA67qoas+pzqdyBl2UrwvgGbSCYLzFoDBeZ4PejNg7rFs2djYp0pa54RUtXe+s1k8bdMRxFSNoZ4XFjNRqoLjqaMnsYMjS+C48n1cR7nR40XDLo6Nuuh1cTF4cN5D0ge42Bg5/98yHBifWZMkK6xlmVGxZUeahqUYqTmGp8bwqEunYjOjcoAKZHnepxIpk7tQb5rb6KZDqz2U9NJIW1UmLaj3wmNOD0MI3SItdwgL8ESJ1rllf1qzd6lZGpyq4u1e+4cNlMx+jZhZYZvPCc8y89ePHM138Mlbf+32p/8w/s5NfXO8u7yD2Kfb72Hzp+Vvr8A7q1v4M="
assert PATCH_B64.isascii()
patch=zlib.decompress(base64.b64decode(PATCH_B64)).decode("utf-8")
proc=subprocess.run(["patch","-p1","--batch","--forward"],input=patch,text=True,capture_output=True)
(out/"patch.stdout").write_text(proc.stdout); (out/"patch.stderr").write_text(proc.stderr)
if proc.returncode != 0: raise SystemExit(f"patch failed {proc.returncode}\n{proc.stdout}\n{proc.stderr}")
after=source.read_bytes(); after_text=after.decode("utf-8"); candidate=hashlib.sha256(after).hexdigest()
expected_candidate="2b1e61dbc0b25aa6b76d5e6bfcc95044eb5f05550314575ca1aa18810d70cca1"
assert candidate==expected_candidate,(candidate,expected_candidate)
decl_re=re.compile(r"(?m)^(?:protected\s+|private\s+|noncomputable\s+|local\s+)*(?:theorem|lemma|def|abbrev|instance|structure|class)\s+([^\s(:]+)")
assert decl_re.findall(before_text)==decl_re.findall(after_text)
def headers(text):
  tr=re.compile(r"(?m)^(?:protected\s+|private\s+|noncomputable\s+|local\s+)*(theorem|lemma)\s+([^\s(:]+)")
  starts=[m.start() for m in decl_re.finditer(text)]; out=[]
  for m in tr.finditer(text):
    nxt=next((x for x in starts if x>m.start()),len(text)); block=text[m.start():nxt]; cut=block.find(":= by")
    if cut<0: cut=block.find(":=")
    h=block if cut<0 else block[:cut]
    out.append((m.group(2),re.sub(r"\s+"," ",h).strip()))
  return out
assert headers(before_text)==headers(after_text)
forbidden=["sorry","admit","axiom","unsafe","native_decide","Lean.ofReduceBool"]; counts={}
for w in forbidden:
  pat=r"(?<![A-Za-z0-9_])"+re.escape(w)+r"(?![A-Za-z0-9_])"
  counts[w]=[len(re.findall(pat,before_text)),len(re.findall(pat,after_text))]
assert all(a==b for a,b in counts.values()),counts
audit={"schema":"fa-v23-prefix-3646-3650","base_source_sha256":base_sha,"candidate_sha256":candidate,"candidate_lines":len(after_text.splitlines()),"repairs":["strongPrincipalCore_pointwise_explicit_Sub_sub","strongSchrodingerCore_pointwise_explicit_Sub_sub"],"semantic_public_proposition_change":False,"theorem_lemma_headers_identical":True,"declaration_sequence_identical":True,"forbidden_lexical_counts_preserved":True,"forbidden_lexical_counts_before_after":counts}
(out/"PATCH_AUDIT.json").write_text(json.dumps(audit,indent=2,sort_keys=True)+"\n"); (out/"candidate.sha256").write_text(candidate+"\n"); print(json.dumps(audit,indent=2,sort_keys=True))
