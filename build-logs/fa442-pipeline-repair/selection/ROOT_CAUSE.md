# FA442 matrix pipeline root cause

**Classification:** INFRA_FAILURE

**Run:** https://github.com/leegahuyn/mathlib4/actions/runs/31345045760

**Workflow:** `.github/workflows/fa442-same-height-slope-cumulative.yml` at `4c8a688568b11755c489e8252b4fb075430dc679`

## Root cause

The skipped Lean setup/compile steps were not unconditional. Their actual FA442 `if:` guards were: steps.prepare.outputs.ok == 'true'. In the candidate jobs the referenced upstream value was empty/false, so GitHub Actions evaluated the guard false. Candidate generation therefore completed while no direct Lean metric was produced.

## Actual skipped steps and guards

- `candidate (slope_change_convert)` — `Install pinned Lean and Mathlib cache` — `if: <none>`
- `candidate (slope_change_convert)` — `Directly compile completed prerequisites and candidate FA` — `if: steps.prepare.outputs.ok == 'true'`
- `candidate (slope_paired_parenthesized_ring_height_upper)` — `Install pinned Lean and Mathlib cache` — `if: <none>`
- `candidate (slope_paired_parenthesized_ring_height_upper)` — `Directly compile completed prerequisites and candidate FA` — `if: steps.prepare.outputs.ok == 'true'`
- `candidate (slope_paired_parenthesized_ring_height)` — `Install pinned Lean and Mathlib cache` — `if: <none>`
- `candidate (slope_paired_parenthesized_ring_height)` — `Directly compile completed prerequisites and candidate FA` — `if: steps.prepare.outputs.ok == 'true'`
- `candidate (slope_change_convert_paired_all_known)` — `Install pinned Lean and Mathlib cache` — `if: <none>`
- `candidate (slope_change_convert_paired_all_known)` — `Directly compile completed prerequisites and candidate FA` — `if: steps.prepare.outputs.ok == 'true'`
- `candidate (slope_paired_dot)` — `Install pinned Lean and Mathlib cache` — `if: <none>`
- `candidate (slope_paired_dot)` — `Directly compile completed prerequisites and candidate FA` — `if: steps.prepare.outputs.ok == 'true'`
- `candidate (slope_paired_parenthesized_deep_simp)` — `Install pinned Lean and Mathlib cache` — `if: <none>`
- `candidate (slope_paired_parenthesized_deep_simp)` — `Directly compile completed prerequisites and candidate FA` — `if: steps.prepare.outputs.ok == 'true'`
- `candidate (slope_paired_dot_all_known)` — `Install pinned Lean and Mathlib cache` — `if: <none>`
- `candidate (slope_paired_dot_all_known)` — `Directly compile completed prerequisites and candidate FA` — `if: steps.prepare.outputs.ok == 'true'`
- `candidate (slope_only)` — `Install pinned Lean and Mathlib cache` — `if: <none>`
- `candidate (slope_only)` — `Directly compile completed prerequisites and candidate FA` — `if: steps.prepare.outputs.ok == 'true'`
- `candidate (slope_paired_parenthesized_ring_height_upper_tail_zero)` — `Install pinned Lean and Mathlib cache` — `if: <none>`
- `candidate (slope_paired_parenthesized_ring_height_upper_tail_zero)` — `Directly compile completed prerequisites and candidate FA` — `if: steps.prepare.outputs.ok == 'true'`
- `candidate (slope_paired_parenthesized_ring_height_upper_tail)` — `Install pinned Lean and Mathlib cache` — `if: <none>`
- `candidate (slope_paired_parenthesized_ring_height_upper_tail)` — `Directly compile completed prerequisites and candidate FA` — `if: steps.prepare.outputs.ok == 'true'`
- `candidate (slope_structures)` — `Install pinned Lean and Mathlib cache` — `if: <none>`
- `candidate (slope_structures)` — `Directly compile completed prerequisites and candidate FA` — `if: steps.prepare.outputs.ok == 'true'`
- `candidate (baseline)` — `Install pinned Lean and Mathlib cache` — `if: <none>`
- `candidate (baseline)` — `Directly compile completed prerequisites and candidate FA` — `if: steps.prepare.outputs.ok == 'true'`
- `candidate (slope_paired_parenthesized)` — `Install pinned Lean and Mathlib cache` — `if: <none>`
- `candidate (slope_paired_parenthesized)` — `Directly compile completed prerequisites and candidate FA` — `if: steps.prepare.outputs.ok == 'true'`
- `candidate (slope_structures_paired_all_known)` — `Install pinned Lean and Mathlib cache` — `if: <none>`
- `candidate (slope_structures_paired_all_known)` — `Directly compile completed prerequisites and candidate FA` — `if: steps.prepare.outputs.ok == 'true'`
- `candidate (slope_paired_parenthesized_ring)` — `Install pinned Lean and Mathlib cache` — `if: <none>`
- `candidate (slope_paired_parenthesized_ring)` — `Directly compile completed prerequisites and candidate FA` — `if: steps.prepare.outputs.ok == 'true'`
- `candidate (slope_paired_parenthesized_all_known)` — `Install pinned Lean and Mathlib cache` — `if: <none>`
- `candidate (slope_paired_parenthesized_all_known)` — `Directly compile completed prerequisites and candidate FA` — `if: steps.prepare.outputs.ok == 'true'`
- `select-confirm-persist` — `Install pinned Lean and Mathlib cache` — `if: <none>`
