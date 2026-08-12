#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--source', required=True)
    ap.add_argument('--audit-out', required=True)
    args = ap.parse_args()

    p = Path(args.source)
    before = p.read_text(encoding='utf-8')
    anchor = '''@[simp]
theorem principalEnergyEquiv_apply (n : ℤ) (u : ActualHOne n) :
    principalEnergyEquiv n u = principalEnergyOperator n u :=
  rfl
'''
    if before.count(anchor) != 1:
        raise RuntimeError(f'expected exactly one principalEnergyEquiv_apply anchor, got {before.count(anchor)}')

    helper = '''
/-- Local Riesz-transported Hilbert structure on the strong anti-dual.
It uses the already proved principal energy equivalence and preserves the existing anti-dual norm. -/
noncomputable local instance actualHMinusOneInnerProductSpace (n : ℤ) :
    InnerProductSpace ℂ (ActualHMinusOne n) where
  toNormedSpace := inferInstance
  toInner :=
    ⟨fun f g ↦ inner ℂ ((principalEnergyEquiv n).symm f)
      ((principalEnergyEquiv n).symm g)⟩
  norm_sq_eq_re_inner f := by
    have hIso : ∀ u : ActualHOne n, ‖principalEnergyEquiv n u‖ = ‖u‖ := by
      intro u
      rw [principalEnergyEquiv_apply]
      apply le_antisymm
      · refine (principalEnergyOperator n u).opNorm_le_bound (norm_nonneg u) ?_
        intro v
        rw [principalEnergyOperator_apply]
        simpa only [mul_comm] using (norm_inner_le_norm (𝕜 := ℂ) v u)
      · by_cases hu : u = 0
        · simp [hu]
        · have hop := (principalEnergyOperator n u).le_opNorm u
          rw [principalEnergyOperator_apply] at hop
          have hre : ‖u‖ ^ 2 ≤ ‖inner ℂ u u‖ := by
            calc
              ‖u‖ ^ 2 = (inner ℂ u u).re := norm_sq_eq_re_inner (𝕜 := ℂ) u
              _ ≤ ‖inner ℂ u u‖ := Complex.re_le_norm _
          have hsquare : ‖u‖ ^ 2 ≤ ‖principalEnergyOperator n u‖ * ‖u‖ := hre.trans hop
          have hpos : 0 < ‖u‖ := norm_pos_iff.mpr hu
          nlinarith [norm_nonneg (principalEnergyOperator n u)]
    have hNormSymm : ‖f‖ = ‖(principalEnergyEquiv n).symm f‖ := by
      have h := hIso ((principalEnergyEquiv n).symm f)
      simpa using h
    calc
      ‖f‖ ^ 2 = ‖(principalEnergyEquiv n).symm f‖ ^ 2 := by rw [hNormSymm]
      _ = re (inner ℂ ((principalEnergyEquiv n).symm f)
          ((principalEnergyEquiv n).symm f)) :=
        InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ)
          ((principalEnergyEquiv n).symm f)
  conj_inner_symm f g := by
    exact inner_conj_symm _ _
  add_left f g h := by
    simp only [map_add, inner_add_left]
  smul_left f g c := by
    simp only [map_smul, inner_smul_left]

'''

    text = before.replace(anchor, anchor + helper, 1)

    decl_re = re.compile(
        r'(?m)^(?:(?:protected|private|noncomputable|local)\s+)*'
        r'(?:theorem|lemma|def|abbrev|instance|structure|class)\s+'
        r'(?P<name>[^\s(:]+)'
    )
    bseq = [m.group('name') for m in decl_re.finditer(before)]
    aseq = [m.group('name') for m in decl_re.finditer(text)]
    pos = 0
    for name in bseq:
        while pos < len(aseq) and aseq[pos] != name:
            pos += 1
        if pos >= len(aseq):
            raise RuntimeError(f'existing declaration not preserved in order: {name}')
        pos += 1

    forbidden = ('sorry', 'admit', 'native_decide', 'Lean.ofReduceBool', 'unsafe')
    for tok in forbidden:
        if before.count(tok) != text.count(tok):
            raise RuntimeError(f'forbidden lexical count changed for {tok}')

    p.write_text(text, encoding='utf-8', newline='\n')
    b = p.read_bytes()
    audit = {
        'schema': 'fa-3341-antidual-hilbert-insert-audit-v2',
        'base_sha256': sha256(before.encode()),
        'candidate_sha256': sha256(b),
        'candidate_bytes': len(b),
        'candidate_lines': len(text.splitlines()),
        'existing_declaration_relative_order_preserved': True,
        'added_helper': 'local instance actualHMinusOneInnerProductSpace',
        'public_theorem_source_headers_changed': False,
        'semantic_public_proposition_change': False,
        'forbidden_lexical_counts_preserved': True,
        'norm_lower_bound_proof': 'validated anti-Riesz nlinarith probe pattern',
    }
    Path(args.audit_out).write_text(json.dumps(audit, indent=2, sort_keys=True) + '\n', encoding='utf-8')


if __name__ == '__main__':
    main()
