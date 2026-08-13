#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,re,sys

if len(sys.argv)!=3:
    raise SystemExit('usage: fa_v35_evalmap_structural.py <source> <outdir>')
source=Path(sys.argv[1]); out=Path(sys.argv[2]); out.mkdir(parents=True,exist_ok=True)
before=source.read_bytes(); bt=before.decode('utf-8')
BASE='931c8656a880307acc6f871f63a4c7751fdf6ccf4c57e02f5363ab7943a61fa4'
CAND='31b9a085ddc116364065467164a9a42628fe8a2759c17ccd479a7bbd90886123'
base=hashlib.sha256(before).hexdigest(); assert base==BASE,(base,BASE)

principal_start=bt.index('theorem strongPrincipalCore_apply_pointwise')
principal_end=bt.index('/-- The literal strong Schrodinger expression', principal_start)
principal=bt[principal_start:principal_end]
oldp='''    rw [strongPrincipalCore_apply]\n    rfl\n'''
newp='''    change\n      Mock2FA.PaperCorrections.AutomorphicSobolev.FixedPhaseDensity.fixedPhaseCoreEvaluation n z\n          (strongPrincipalCore n u) =\n        Mock2FA.PaperCorrections.AutomorphicSobolev.FixedPhaseDensity.fixedPhaseCoreEvaluation n z u -\n          Mock2FA.PaperCorrections.AutomorphicSobolev.FixedPhaseDensity.fixedPhaseCoreEvaluation n z\n            (Mock2FA.PaperCorrections.AutomorphicSobolev.HalfWeightDifferentialOperators.InverseEtaFixedPhaseCore.lowerFromSucc n\n              (Mock2FA.PaperCorrections.AutomorphicSobolev.HalfWeightDifferentialOperators.InverseEtaFixedPhaseCore.raise n u)) -\n          Mock2FA.PaperCorrections.AutomorphicSobolev.FixedPhaseDensity.fixedPhaseCoreEvaluation n z\n            (Mock2FA.PaperCorrections.AutomorphicSobolev.HalfWeightDifferentialOperators.InverseEtaFixedPhaseCore.raiseFromPred n\n              (Mock2FA.PaperCorrections.AutomorphicSobolev.HalfWeightDifferentialOperators.InverseEtaFixedPhaseCore.lower n u))\n    rw [strongPrincipalCore_apply, map_sub, map_sub]\n'''
assert principal.count(oldp)==1, principal.count(oldp)
principal2=principal.replace(oldp,newp,1)
text=bt[:principal_start]+principal2+bt[principal_end:]

sch_start=text.index('theorem strongSchrodingerCore_apply_pointwise')
sch_end=text.index('/-! #### Moving both graph derivatives', sch_start)
sch=text[sch_start:sch_end]
olds='''    rw [strongSchrodingerCore_apply]\n    rfl\n'''
news='''    change\n      Mock2FA.PaperCorrections.AutomorphicSobolev.FixedPhaseDensity.fixedPhaseCoreEvaluation n z\n          (strongSchrodingerCore n t u) =\n        Mock2FA.PaperCorrections.AutomorphicSobolev.FixedPhaseDensity.fixedPhaseCoreEvaluation n z\n            (strongPrincipalCore n u) -\n          (t : ℂ) *\n            Mock2FA.PaperCorrections.AutomorphicSobolev.FixedPhaseDensity.fixedPhaseCoreEvaluation n z\n              (potentialMultiplicationCore n u)\n    rw [strongSchrodingerCore_apply, map_sub, map_smul]\n    rfl\n'''
assert sch.count(olds)==1, sch.count(olds)
sch2=sch.replace(olds,news,1)
text=text[:sch_start]+sch2+text[sch_end:]
source.write_text(text,encoding='utf-8')
after=source.read_bytes(); at=after.decode('utf-8'); cand=hashlib.sha256(after).hexdigest(); assert cand==CAND,(cand,CAND); assert len(at.splitlines())==61467

decl=re.compile(r'(?m)^(?:protected\s+|private\s+|noncomputable\s+|local\s+)*(?:theorem|lemma|def|abbrev|instance|structure|class)\s+([^\s(:]+)')
assert decl.findall(bt)==decl.findall(at),'declaration sequence changed'
th=re.compile(r'(?m)^(?:protected\s+|private\s+|noncomputable\s+|local\s+)*(theorem|lemma)\s+([^\s(:]+)')
def headers(s):
    starts=[m.start() for m in decl.finditer(s)]; r=[]
    for m in th.finditer(s):
        nxt=next((x for x in starts if x>m.start()),len(s)); block=s[m.start():nxt]; cut=block.find(':= by')
        if cut<0: cut=block.find(':=')
        r.append((m.group(2),re.sub(r'\s+',' ',block if cut<0 else block[:cut]).strip()))
    return r
assert headers(bt)==headers(at),'theorem/lemma header changed'
forbidden=['sorry','admit','axiom','unsafe','native_decide','Lean.ofReduceBool','set_option']; counts={}
for w in forbidden:
    pat=r'(?<![A-Za-z0-9_])'+re.escape(w)+r'(?![A-Za-z0-9_])'; counts[w]=[len(re.findall(pat,bt)),len(re.findall(pat,at))]
assert all(a==b for a,b in counts.values()),counts
audit={'schema':'fa-v35-evalmap-structural-strict','base_source_sha256':BASE,'candidate_sha256':CAND,'candidate_bytes':len(after),'candidate_lines':len(at.splitlines()),'repairs':['3646_fixedPhaseCoreEvaluation_map_sub','3650_fixedPhaseCoreEvaluation_map_sub_map_smul'],'semantic_public_proposition_change':False,'theorem_lemma_headers_identical':True,'declaration_sequence_identical':True,'existing_declaration_relative_order_preserved':True,'forbidden_lexical_counts_preserved':True,'forbidden_lexical_counts_before_after':counts}
(out/'PATCH_AUDIT.json').write_text(json.dumps(audit,indent=2,sort_keys=True)+'\n'); (out/'candidate.sha256').write_text(CAND+'\n'); print(json.dumps(audit,indent=2,sort_keys=True))
