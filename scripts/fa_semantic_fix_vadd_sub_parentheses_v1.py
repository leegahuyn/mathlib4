#!/usr/bin/env python3
from __future__ import annotations
import argparse, hashlib, json, re
from pathlib import Path

DECL_RE = re.compile(r'(?m)^(?:protected\s+|private\s+|noncomputable\s+)?(?:theorem|lemma|def|abbrev|instance|structure|class)\s+(?P<name>[^\s(:]+)')

ALLOWED = {
    3226: ('ambientPlaneL2_norm_translation_sub_tendsto_zero', 'DomAddAct.mk t +ᵥ f - f', '(DomAddAct.mk t +ᵥ f) - f', 3),
    3236: ('integral_kernel_vadd_eq_integral_kernel_vadd_sub_of_mean_zero', 'DomAddAct.mk (-t) +ᵥ f - f', '(DomAddAct.mk (-t) +ᵥ f) - f', 3),
    3237: ('integral_shrinkingKernel_smul_translation_sub_tendsto_zero', 'DomAddAct.mk (-t) +ᵥ f - f', '(DomAddAct.mk (-t) +ᵥ f) - f', 7),
    3292: ('integrable_kernel_smul_translation_sub', 'DomAddAct.mk (-t) +ᵥ f - f', '(DomAddAct.mk (-t) +ᵥ f) - f', 1),
    3293: ('integral_kernel_smul_translation_eq_base_add_error', 'DomAddAct.mk (-t) +ᵥ f - f', '(DomAddAct.mk (-t) +ᵥ f) - f', 2),
    3296: ('friedrichsMollifierAction_eq_base_add_error', 'DomAddAct.mk (-t) +ᵥ f - f', '(DomAddAct.mk (-t) +ᵥ f) - f', 1),
    3297: ('friedrichsMollifierError_tendsto_zero', 'DomAddAct.mk (-t) +ᵥ f - f', '(DomAddAct.mk (-t) +ᵥ f) - f', 1),
    3299: ('friedrichsAffineCommutatorAction_eq_error', 'DomAddAct.mk (-t) +ᵥ f - f', '(DomAddAct.mk (-t) +ᵥ f) - f', 1),
    3300: ('friedrichsAffineCommutatorError_tendsto_zero', 'DomAddAct.mk (-t) +ᵥ f - f', '(DomAddAct.mk (-t) +ᵥ f) - f', 1),
}

PROOF_FIXES_3237 = [
    (
        '  have hηC : η * C < ε := by\n    rw [η, div_mul_eq_mul_div, div_lt_iff₀ hC1]\n    nlinarith',
        '  have hηC : η * C < ε := by\n    dsimp only [η]\n    rw [div_mul_eq_mul_div, div_lt_iff₀ hC1]\n    nlinarith',
        'unfold-eta',
    ),
    (
        '    have hNeg : Filter.Tendsto (fun t : ℂ ↦ -t) (nhds 0) (nhds 0) := by\n      fun_prop',
        '    have hNeg : Filter.Tendsto (fun t : ℂ ↦ -t) (nhds 0) (nhds 0) := by\n      change ContinuousAt (fun t : ℂ ↦ -t) 0\n      exact continuousAt_id.neg',
        'pin-neg-continuity-shape',
    ),
    (
        '      rw [norm_smul]\n      exact mul_le_mul_of_nonneg_left htSmall.le (norm_nonneg _)',
        '      rw [norm_smul]\n      calc\n        ‖K n t‖ * ‖(DomAddAct.mk (-t) +ᵥ f) - f‖ ≤ ‖K n t‖ * η :=\n          mul_le_mul_of_nonneg_left htSmall.le (norm_nonneg _)\n        _ = η * ‖K n t‖ := mul_comm _ _',
        'align-norm-smul-order',
    ),
]

def sha(x: str) -> str:
    return hashlib.sha256(x.encode()).hexdigest()

def declarations(text: str):
    ms = list(DECL_RE.finditer(text))
    out = []
    for i,m in enumerate(ms):
        out.append((m.group('name'), m.start(), ms[i+1].start() if i+1 < len(ms) else len(text)))
    return out

def header(block: str) -> str:
    p = block.find(':=')
    if p < 0:
        return block
    return block[:p].rstrip()

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--base-source', required=True)
    ap.add_argument('--target', required=True)
    ap.add_argument('--audit-out', required=True)
    a=ap.parse_args()
    before=Path(a.base_source).read_text()
    ds=declarations(before)
    if len(ds) <= max(ALLOWED):
        raise SystemExit('declaration inventory too short')
    pieces=[]; cursor=0; records=[]
    for idx,(name,start,end) in enumerate(ds):
        block=before[start:end]
        pieces.append(before[cursor:start])
        new=block
        if idx in ALLOWED:
            exp_name, old, rep, count = ALLOWED[idx]
            if name != exp_name:
                raise SystemExit(f'declaration identity drift idx={idx} got={name} expected={exp_name}')
            got=new.count(old)
            if got != count:
                raise SystemExit(f'parenthesis count drift idx={idx} got={got} expected={count}')
            new=new.replace(old,rep)
            records.append({'idx':idx,'name':name,'kind':'semantic_parenthesis','count':count,'old':old,'new':rep})
        if idx == 3237:
            for old,rep,rid in PROOF_FIXES_3237:
                if new.count(old) != 1:
                    raise SystemExit(f'proof fragment drift idx=3237 id={rid} count={new.count(old)}')
                new=new.replace(old,rep)
                records.append({'idx':idx,'name':name,'kind':'proof_body','id':rid})
        pieces.append(new); cursor=end
    pieces.append(before[cursor:])
    after=''.join(pieces)
    ds2=declarations(after)
    names1=[x[0] for x in ds]; names2=[x[0] for x in ds2]
    if names1 != names2:
        raise SystemExit('declaration sequence changed')
    changed_headers=[]
    for idx,((n,s1,e1),(n2,s2,e2)) in enumerate(zip(ds,ds2)):
        h1=header(before[s1:e1]); h2=header(after[s2:e2])
        if h1 != h2:
            changed_headers.append({'idx':idx,'name':n,'before_sha256':sha(h1),'after_sha256':sha(h2)})
    expected=sorted(ALLOWED)
    got=sorted(x['idx'] for x in changed_headers)
    if got != expected:
        raise SystemExit(f'public proposition/header change set drift got={got} expected={expected}')
    # The semantic correction must remove every ambiguous translation-difference spelling.
    if 'DomAddAct.mk t +ᵥ f - f' in after or 'DomAddAct.mk (-t) +ᵥ f - f' in after:
        raise SystemExit('ambiguous vadd/sub spelling remains')
    forbidden=['sorryAx',' by\n  sorry','\nadmit','unsafe axiom','Lean.ofReduceBool','native_decide']
    introduced=[x for x in forbidden if x not in before and x in after]
    if introduced:
        raise SystemExit('forbidden trust token introduced: '+repr(introduced))
    Path(a.target).write_text(after)
    audit={
        'schema':'fa-semantic-fix-vadd-sub-parentheses-v1',
        'reason':'Lean parses `g +ᵥ f - f` as `g +ᵥ (f - f)`; restore documented/intended translation-difference `(g +ᵥ f) - f`.',
        'declaration_sequence_preserved':True,
        'allowed_public_proposition_changes':expected,
        'changed_public_headers':changed_headers,
        'records':records,
        'before_sha256':sha(before),
        'after_sha256':sha(after),
        'forbidden_trust_tokens_introduced':introduced,
    }
    Path(a.audit_out).write_text(json.dumps(audit,ensure_ascii=False,indent=2,sort_keys=True)+'\n')

if __name__=='__main__': main()
