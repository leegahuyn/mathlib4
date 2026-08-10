# FA442 SKIP ROOT CAUSE

Run: https://github.com/leegahuyn/mathlib4/actions/runs/31345045760

Workflow path: `.github/workflows/fa442-same-height-slope-cumulative.yml`

## Verified root cause

The skipped Lean setup/compile steps were not unconditional. Their actual FA442 `if:` guards were: steps.prepare.outputs.ok == 'true'. In the candidate jobs the referenced upstream value was empty/false, so GitHub Actions evaluated the guard false. Candidate generation therefore completed while no direct Lean metric was produced.

## Skipped direct-compile path

- job `candidate (slope_change_convert)` / step `Install pinned Lean and Mathlib cache`
  - conclusion: `skipped`
  - actual condition: `<none>`
- job `candidate (slope_change_convert)` / step `Directly compile completed prerequisites and candidate FA`
  - conclusion: `skipped`
  - actual condition: `steps.prepare.outputs.ok == 'true'`
  - output `steps.prepare.outputs.ok`: owner_exists=True, definition_found=True
- job `candidate (slope_paired_parenthesized_ring_height_upper)` / step `Install pinned Lean and Mathlib cache`
  - conclusion: `skipped`
  - actual condition: `<none>`
- job `candidate (slope_paired_parenthesized_ring_height_upper)` / step `Directly compile completed prerequisites and candidate FA`
  - conclusion: `skipped`
  - actual condition: `steps.prepare.outputs.ok == 'true'`
  - output `steps.prepare.outputs.ok`: owner_exists=True, definition_found=True
- job `candidate (slope_paired_parenthesized_ring_height)` / step `Install pinned Lean and Mathlib cache`
  - conclusion: `skipped`
  - actual condition: `<none>`
- job `candidate (slope_paired_parenthesized_ring_height)` / step `Directly compile completed prerequisites and candidate FA`
  - conclusion: `skipped`
  - actual condition: `steps.prepare.outputs.ok == 'true'`
  - output `steps.prepare.outputs.ok`: owner_exists=True, definition_found=True
- job `candidate (slope_change_convert_paired_all_known)` / step `Install pinned Lean and Mathlib cache`
  - conclusion: `skipped`
  - actual condition: `<none>`
- job `candidate (slope_change_convert_paired_all_known)` / step `Directly compile completed prerequisites and candidate FA`
  - conclusion: `skipped`
  - actual condition: `steps.prepare.outputs.ok == 'true'`
  - output `steps.prepare.outputs.ok`: owner_exists=True, definition_found=True
- job `candidate (slope_paired_dot)` / step `Install pinned Lean and Mathlib cache`
  - conclusion: `skipped`
  - actual condition: `<none>`
- job `candidate (slope_paired_dot)` / step `Directly compile completed prerequisites and candidate FA`
  - conclusion: `skipped`
  - actual condition: `steps.prepare.outputs.ok == 'true'`
  - output `steps.prepare.outputs.ok`: owner_exists=True, definition_found=True
- job `candidate (slope_paired_parenthesized_deep_simp)` / step `Install pinned Lean and Mathlib cache`
  - conclusion: `skipped`
  - actual condition: `<none>`
- job `candidate (slope_paired_parenthesized_deep_simp)` / step `Directly compile completed prerequisites and candidate FA`
  - conclusion: `skipped`
  - actual condition: `steps.prepare.outputs.ok == 'true'`
  - output `steps.prepare.outputs.ok`: owner_exists=True, definition_found=True
- job `candidate (slope_paired_dot_all_known)` / step `Install pinned Lean and Mathlib cache`
  - conclusion: `skipped`
  - actual condition: `<none>`
- job `candidate (slope_paired_dot_all_known)` / step `Directly compile completed prerequisites and candidate FA`
  - conclusion: `skipped`
  - actual condition: `steps.prepare.outputs.ok == 'true'`
  - output `steps.prepare.outputs.ok`: owner_exists=True, definition_found=True
- job `candidate (slope_only)` / step `Install pinned Lean and Mathlib cache`
  - conclusion: `skipped`
  - actual condition: `<none>`
- job `candidate (slope_only)` / step `Directly compile completed prerequisites and candidate FA`
  - conclusion: `skipped`
  - actual condition: `steps.prepare.outputs.ok == 'true'`
  - output `steps.prepare.outputs.ok`: owner_exists=True, definition_found=True
- job `candidate (slope_paired_parenthesized_ring_height_upper_tail_zero)` / step `Install pinned Lean and Mathlib cache`
  - conclusion: `skipped`
  - actual condition: `<none>`
- job `candidate (slope_paired_parenthesized_ring_height_upper_tail_zero)` / step `Directly compile completed prerequisites and candidate FA`
  - conclusion: `skipped`
  - actual condition: `steps.prepare.outputs.ok == 'true'`
  - output `steps.prepare.outputs.ok`: owner_exists=True, definition_found=True
- job `candidate (slope_paired_parenthesized_ring_height_upper_tail)` / step `Install pinned Lean and Mathlib cache`
  - conclusion: `skipped`
  - actual condition: `<none>`
- job `candidate (slope_paired_parenthesized_ring_height_upper_tail)` / step `Directly compile completed prerequisites and candidate FA`
  - conclusion: `skipped`
  - actual condition: `steps.prepare.outputs.ok == 'true'`
  - output `steps.prepare.outputs.ok`: owner_exists=True, definition_found=True
- job `candidate (slope_structures)` / step `Install pinned Lean and Mathlib cache`
  - conclusion: `skipped`
  - actual condition: `<none>`
- job `candidate (slope_structures)` / step `Directly compile completed prerequisites and candidate FA`
  - conclusion: `skipped`
  - actual condition: `steps.prepare.outputs.ok == 'true'`
  - output `steps.prepare.outputs.ok`: owner_exists=True, definition_found=True
- job `candidate (baseline)` / step `Install pinned Lean and Mathlib cache`
  - conclusion: `skipped`
  - actual condition: `<none>`
- job `candidate (baseline)` / step `Directly compile completed prerequisites and candidate FA`
  - conclusion: `skipped`
  - actual condition: `steps.prepare.outputs.ok == 'true'`
  - output `steps.prepare.outputs.ok`: owner_exists=True, definition_found=True
- job `candidate (slope_paired_parenthesized)` / step `Install pinned Lean and Mathlib cache`
  - conclusion: `skipped`
  - actual condition: `<none>`
- job `candidate (slope_paired_parenthesized)` / step `Directly compile completed prerequisites and candidate FA`
  - conclusion: `skipped`
  - actual condition: `steps.prepare.outputs.ok == 'true'`
  - output `steps.prepare.outputs.ok`: owner_exists=True, definition_found=True
- job `candidate (slope_structures_paired_all_known)` / step `Install pinned Lean and Mathlib cache`
  - conclusion: `skipped`
  - actual condition: `<none>`
- job `candidate (slope_structures_paired_all_known)` / step `Directly compile completed prerequisites and candidate FA`
  - conclusion: `skipped`
  - actual condition: `steps.prepare.outputs.ok == 'true'`
  - output `steps.prepare.outputs.ok`: owner_exists=True, definition_found=True
- job `candidate (slope_paired_parenthesized_ring)` / step `Install pinned Lean and Mathlib cache`
  - conclusion: `skipped`
  - actual condition: `<none>`
- job `candidate (slope_paired_parenthesized_ring)` / step `Directly compile completed prerequisites and candidate FA`
  - conclusion: `skipped`
  - actual condition: `steps.prepare.outputs.ok == 'true'`
  - output `steps.prepare.outputs.ok`: owner_exists=True, definition_found=True
- job `candidate (slope_paired_parenthesized_all_known)` / step `Install pinned Lean and Mathlib cache`
  - conclusion: `skipped`
  - actual condition: `<none>`
- job `candidate (slope_paired_parenthesized_all_known)` / step `Directly compile completed prerequisites and candidate FA`
  - conclusion: `skipped`
  - actual condition: `steps.prepare.outputs.ok == 'true'`
  - output `steps.prepare.outputs.ok`: owner_exists=True, definition_found=True
- job `select-confirm-persist` / step `Install pinned Lean and Mathlib cache`
  - conclusion: `skipped`
  - actual condition: `<none>`

## Selector failure

`RuntimeError: expected one baseline direct metric, found 0`

## Evidence commit failure

`Author identity unknown / fatal: empty ident name`

## Repair invariant

The replacement matrix and sequential fallback run Lean setup and direct compile without candidate-metadata output guards. A nonexecuted direct compile is emitted as `INFRA_FAILURE`, never as a successful candidate.
