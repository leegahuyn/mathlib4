#!/usr/bin/env python3
from __future__ import annotations
import argparse, hashlib, json, re
from pathlib import Path

BASE_SHA = 'a9eaa27bc3ce2d84f735191a2cf74379cc1920bf5b45081350bdb673b0786084'
BASE_BYTES = 2796831
BASE_LINES = 62579
BASE_DECLS = 4416
TRUST = ('sorry', 'admit', 'axiom', 'unsafe', 'native_decide', 'Lean.ofReduceBool')
DECL_RE = re.compile(r'(?m)^(?:protected\s+|private\s+|noncomputable\s+|local\s+)*(?:theorem|lemma|def|abbrev|instance|structure|class)\s+([^\s(:]+)')
HEADER_RE = re.compile(r'(?m)^(?:protected\s+|private\s+|noncomputable\s+|local\s+)*(?:theorem|lemma|def|abbrev|instance|structure|class)\s+[^\s(:]+.*?(?=\s*:=)', re.S)


def sha(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()


def strip_noncode(text: str) -> str:
    out=list(text); i=0; depth=0; string=False; esc=False
    while i < len(out):
        if depth:
            if text.startswith('/-',i): out[i]=out[i+1]=' '; depth+=1; i+=2; continue
            if text.startswith('-/',i): out[i]=out[i+1]=' '; depth-=1; i+=2; continue
            if out[i] != '\n': out[i]=' '
            i+=1; continue
        if string:
            ch=out[i]
            if ch!='\n': out[i]=' '
            if esc: esc=False
            elif ch=='\\': esc=True
            elif ch=='"': string=False
            i+=1; continue
        if text.startswith('/-',i): out[i]=out[i+1]=' '; depth=1; i+=2; continue
        if text.startswith('--',i):
            while i < len(out) and out[i] != '\n': out[i]=' '; i+=1
            continue
        if out[i]=='"': out[i]=' '; string=True
        i+=1
    return ''.join(out)


def trust_counts(text: str) -> dict[str,int]:
    code=strip_noncode(text)
    return {t: len(re.findall(r'(?<![A-Za-z0-9_])'+re.escape(t)+r'(?![A-Za-z0-9_])', code)) for t in TRUST}


def decl_ranges(text: str):
    ms=list(DECL_RE.finditer(text))
    return {m.group(1):(m.start(), ms[i+1].start() if i+1<len(ms) else len(text)) for i,m in enumerate(ms)}


def decl_headers(text: str):
    return [(m.group(1), text[m.start():text.find("\n", m.start()) if text.find("\n", m.start()) >= 0 else len(text)]) for m in DECL_RE.finditer(text)]

def changed_decl_header(text: str, name: str) -> str:
    a,b=decl_ranges(text)[name]
    block=text[a:b]
    pos=block.find(":=")
    if pos < 0: raise RuntimeError(f"no := in changed declaration {name}")
    return block[:pos].rstrip()


def replace_in_decl(text: str, name: str, old: str, new: str, label: str):
    ranges=decl_ranges(text)
    if name not in ranges: raise RuntimeError(f'{label}: missing decl {name}')
    a,b=ranges[name]; block=text[a:b]
    n=block.count(old)
    if n != 1: raise RuntimeError(f'{label}: expected 1 occurrence in {name}, got {n}')
    block2=block.replace(old,new,1)
    return text[:a]+block2+text[b:], {'label':label,'declaration':name,'old_count':n}

ASSOC_OLD='''      rw [Fin.prod_univ_two]\n      simp\n'''
ASSOC_NEW='''      rw [Fin.prod_univ_two]\n      simp <;> ring_nf\n'''

ONE_TAIL_OLD='''      ((literalStageFourierScale Y)⁻¹ : ℂ) using 1 <;>\n    try simp only [one_div, Complex.one_re, Complex.one_im,\n      Complex.add_re, Complex.add_im, Complex.real_smul, smul_eq_mul,\n      mul_one, add_zero, zero_mul, Complex.ofReal_inv, Complex.ofReal_mul] <;>\n    field_simp [literalStageFourierScale_ne_zero Y] <;> ring\n'''
I_TAIL_OLD='''      ((literalStageFourierScale Y)⁻¹ : ℂ) using 1 <;>\n    try simp only [one_div, Complex.I_re, Complex.I_im, Complex.add_re,\n      Complex.add_im, Complex.real_smul, smul_eq_mul, mul_one, add_zero,\n      zero_mul, Complex.ofReal_inv, Complex.ofReal_mul] <;>\n    field_simp [literalStageFourierScale_ne_zero Y] <;> ring\n'''

TAILS={
'unfoldall': (
'''      ((literalStageFourierScale Y)⁻¹ : ℂ) using 1 <;>\n    try with_unfolding_all rfl <;>\n    simp [id, one_div, Complex.one_re, Complex.one_im,\n      Complex.add_re, Complex.add_im, Complex.real_smul, smul_eq_mul,\n      mul_comm, mul_left_comm, mul_assoc,\n      Complex.ofReal_inv, Complex.ofReal_mul] <;>\n    field_simp [literalStageFourierScale_ne_zero Y] <;> ring_nf\n''',
'''      ((literalStageFourierScale Y)⁻¹ : ℂ) using 1 <;>\n    try with_unfolding_all rfl <;>\n    simp [id, one_div, Complex.I_re, Complex.I_im, Complex.add_re,\n      Complex.add_im, Complex.real_smul, smul_eq_mul,\n      mul_comm, mul_left_comm, mul_assoc,\n      Complex.ofReal_inv, Complex.ofReal_mul] <;>\n    field_simp [literalStageFourierScale_ne_zero Y] <;> ring_nf\n'''),
'ext': (
'''      ((literalStageFourierScale Y)⁻¹ : ℂ) using 1 <;>\n    ext <;>\n    simp [id, one_div, Complex.one_re, Complex.one_im,\n      Complex.add_re, Complex.add_im, Complex.real_smul, smul_eq_mul,\n      mul_comm, mul_left_comm, mul_assoc,\n      Complex.ofReal_inv, Complex.ofReal_mul] <;>\n    field_simp [literalStageFourierScale_ne_zero Y] <;> ring_nf\n''',
'''      ((literalStageFourierScale Y)⁻¹ : ℂ) using 1 <;>\n    ext <;>\n    simp [id, one_div, Complex.I_re, Complex.I_im, Complex.add_re,\n      Complex.add_im, Complex.real_smul, smul_eq_mul,\n      mul_comm, mul_left_comm, mul_assoc,\n      Complex.ofReal_inv, Complex.ofReal_mul] <;>\n    field_simp [literalStageFourierScale_ne_zero Y] <;> ring_nf\n'''),
'allgoals': (
'''      ((literalStageFourierScale Y)⁻¹ : ℂ) using 1\n  all_goals\n    first\n    | with_unfolding_all rfl\n    | (funext t; simp [id, one_div, Complex.one_re, Complex.one_im,\n        Complex.add_re, Complex.add_im, Complex.real_smul, smul_eq_mul,\n        mul_comm, mul_left_comm, mul_assoc,\n        Complex.ofReal_inv, Complex.ofReal_mul] <;> ring_nf)\n    | (simp [id, one_div, Complex.one_re, Complex.one_im,\n        Complex.add_re, Complex.add_im, Complex.real_smul, smul_eq_mul,\n        mul_comm, mul_left_comm, mul_assoc,\n        Complex.ofReal_inv, Complex.ofReal_mul] <;>\n       field_simp [literalStageFourierScale_ne_zero Y] <;> ring_nf)\n''',
'''      ((literalStageFourierScale Y)⁻¹ : ℂ) using 1\n  all_goals\n    first\n    | with_unfolding_all rfl\n    | (funext t; simp [id, one_div, Complex.I_re, Complex.I_im,\n        Complex.add_re, Complex.add_im, Complex.real_smul, smul_eq_mul,\n        mul_comm, mul_left_comm, mul_assoc,\n        Complex.ofReal_inv, Complex.ofReal_mul] <;> ring_nf)\n    | (simp [id, one_div, Complex.I_re, Complex.I_im, Complex.add_re,\n        Complex.add_im, Complex.real_smul, smul_eq_mul,\n        mul_comm, mul_left_comm, mul_assoc,\n        Complex.ofReal_inv, Complex.ofReal_mul] <;>\n       field_simp [literalStageFourierScale_ne_zero Y] <;> ring_nf)\n'''),
'subsingleton': (
'''      ((literalStageFourierScale Y)⁻¹ : ℂ) using 1\n  all_goals\n    first\n    | exact Subsingleton.elim _ _\n    | (funext t; simp [id, one_div, Complex.one_re, Complex.one_im,\n        Complex.add_re, Complex.add_im, Complex.real_smul, smul_eq_mul,\n        mul_comm, mul_left_comm, mul_assoc,\n        Complex.ofReal_inv, Complex.ofReal_mul] <;> ring_nf)\n    | (simp [id, one_div, Complex.one_re, Complex.one_im,\n        Complex.add_re, Complex.add_im, Complex.real_smul, smul_eq_mul,\n        mul_comm, mul_left_comm, mul_assoc,\n        Complex.ofReal_inv, Complex.ofReal_mul] <;>\n       field_simp [literalStageFourierScale_ne_zero Y] <;> ring_nf)\n''',
'''      ((literalStageFourierScale Y)⁻¹ : ℂ) using 1\n  all_goals\n    first\n    | exact Subsingleton.elim _ _\n    | (funext t; simp [id, one_div, Complex.I_re, Complex.I_im,\n        Complex.add_re, Complex.add_im, Complex.real_smul, smul_eq_mul,\n        mul_comm, mul_left_comm, mul_assoc,\n        Complex.ofReal_inv, Complex.ofReal_mul] <;> ring_nf)\n    | (simp [id, one_div, Complex.I_re, Complex.I_im, Complex.add_re,\n        Complex.add_im, Complex.real_smul, smul_eq_mul,\n        mul_comm, mul_left_comm, mul_assoc,\n        Complex.ofReal_inv, Complex.ofReal_mul] <;>\n       field_simp [literalStageFourierScale_ne_zero Y] <;> ring_nf)\n'''),
'caseblocks': (
'''      ((literalStageFourierScale Y)⁻¹ : ℂ) using 1\n  case e'_4 => with_unfolding_all rfl\n  case e'_8 =>\n    funext t\n    simp [id, one_div, Complex.one_re, Complex.one_im,\n      Complex.add_re, Complex.add_im, Complex.real_smul, smul_eq_mul,\n      mul_comm, mul_left_comm, mul_assoc,\n      Complex.ofReal_inv, Complex.ofReal_mul]\n    ring_nf\n  case e'_9 =>\n    simp [id, one_div, Complex.one_re, Complex.one_im,\n      Complex.add_re, Complex.add_im, Complex.real_smul, smul_eq_mul,\n      mul_comm, mul_left_comm, mul_assoc,\n      Complex.ofReal_inv, Complex.ofReal_mul]\n    field_simp [literalStageFourierScale_ne_zero Y]\n    ring_nf\n''',
'''      ((literalStageFourierScale Y)⁻¹ : ℂ) using 1\n  case e'_4 => with_unfolding_all rfl\n  case e'_8 =>\n    funext t\n    simp [id, one_div, Complex.I_re, Complex.I_im, Complex.add_re,\n      Complex.add_im, Complex.real_smul, smul_eq_mul,\n      mul_comm, mul_left_comm, mul_assoc,\n      Complex.ofReal_inv, Complex.ofReal_mul]\n    ring_nf\n  case e'_9 =>\n    simp [id, one_div, Complex.I_re, Complex.I_im, Complex.add_re,\n      Complex.add_im, Complex.real_smul, smul_eq_mul,\n      mul_comm, mul_left_comm, mul_assoc,\n      Complex.ofReal_inv, Complex.ofReal_mul]\n    field_simp [literalStageFourierScale_ne_zero Y]\n    ring_nf\n'''),
}

VARIANTS=['assoc_only','assoc_unfoldall','assoc_ext','assoc_allgoals','assoc_subsingleton','assoc_caseblocks']


def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--base',type=Path,required=True); ap.add_argument('--variant',choices=VARIANTS,required=True); ap.add_argument('--out',type=Path,required=True); ap.add_argument('--audit',type=Path,required=True); a=ap.parse_args()
    raw=a.base.read_bytes(); text=raw.decode()
    if sha(raw)!=BASE_SHA or len(raw)!=BASE_BYTES or len(text.splitlines())!=BASE_LINES or len(DECL_RE.findall(text))!=BASE_DECLS:
        raise SystemExit('base identity mismatch')
    before_headers=decl_headers(text); before_trust=trust_counts(text); changes=[]; changed_names=['literalStageNegativePlaneWave_eq_conj_planeWaveRepresentative'] + ([] if a.variant=='assoc_only' else ['fderiv_literalStageNegativePlaneWave_one','fderiv_literalStageNegativePlaneWave_I']); before_changed_headers={n:changed_decl_header(text,n) for n in changed_names}
    text,rec=replace_in_decl(text,'literalStageNegativePlaneWave_eq_conj_planeWaveRepresentative',ASSOC_OLD,ASSOC_NEW,'assoc_ring_nf'); changes.append(rec)
    if a.variant!='assoc_only':
        mode=a.variant.removeprefix('assoc_'); one_new,i_new=TAILS[mode]
        text,rec=replace_in_decl(text,'fderiv_literalStageNegativePlaneWave_one',ONE_TAIL_OLD,one_new,f'deriv_one_{mode}'); changes.append(rec)
        text,rec=replace_in_decl(text,'fderiv_literalStageNegativePlaneWave_I',I_TAIL_OLD,i_new,f'deriv_I_{mode}'); changes.append(rec)
    after_headers=decl_headers(text); after_trust=trust_counts(text); after_changed_headers={n:changed_decl_header(text,n) for n in changed_names}
    if after_headers!=before_headers or after_changed_headers!=before_changed_headers: raise SystemExit('declaration headers/order changed')
    if any(after_trust.values()) or after_trust!=before_trust: raise SystemExit(f'trust mismatch {before_trust} {after_trust}')
    outb=text.encode(); a.out.parent.mkdir(parents=True,exist_ok=True); a.out.write_bytes(outb)
    audit={'schema':'fa-v49-assoc-deriv-matrix-v1','variant':a.variant,'base_sha256':BASE_SHA,'source_sha256':sha(outb),'source_bytes':len(outb),'source_lines':len(text.splitlines()),'declaration_count':len(DECL_RE.findall(text)),'declaration_headers_identical':True,'trust_before':before_trust,'trust_after':after_trust,'changes':changes}
    a.audit.parent.mkdir(parents=True,exist_ok=True); a.audit.write_text(json.dumps(audit,indent=2,sort_keys=True)+'\n')
    print(json.dumps(audit,indent=2,sort_keys=True))
if __name__=='__main__': main()

# round-trigger: 1
