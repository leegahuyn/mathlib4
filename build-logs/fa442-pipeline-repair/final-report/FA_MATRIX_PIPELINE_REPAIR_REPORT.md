# FA MATRIX PIPELINE REPAIR REPORT

## Baseline

source SHA256: `71dc36f16ebea92d537aa40a5d420443e4bcb93ccb76fea31efb40a6cb5c3aa0`

line count: `60453`

direct Lean exit: `1`

first error: `31726:2`

declaration: `actualEdgeAmbientParam_hasDerivAt`

## Pipeline issue found

root cause: The skipped Lean setup/compile steps were not unconditional. Their actual FA442 `if:` guards were: steps.prepare.outputs.ok == 'true'. In the candidate jobs the referenced upstream value was empty/false, so GitHub Actions evaluated the guard false. Candidate generation therefore completed while no direct Lean metric was produced.

workflow files changed:
- `.github/workflows/fa442-direct-matrix-pipeline-repair.yml`

scripts changed:
- `scripts/fa442_pipeline_common.py`
- `scripts/fa442_pipeline_prepare.py`
- `scripts/fa442_pipeline_metric.py`
- `scripts/fa442_pipeline_select.py`
- `scripts/fa442_pipeline_verify_checked_in.py`
- `scripts/fa442_pipeline_report.py`

## Candidate results

variant | SHA256 | Lean executed? | exit | first line:col | declaration | classification
--- | --- | --- | --- | --- | --- | ---
baseline-direct | `71dc36f16ebea92d537aa40a5d420443e4bcb93ccb76fea31efb40a6cb5c3aa0` | true | 1 | 31726:2 | `actualEdgeAmbientParam_hasDerivAt` | LEAN_FAILURE
git:origin/ci/fa444-complete-run-locator-20260810 | `885e585d346e81ff15df6f03391913a791d121b7933c3c99a37a557253c87489` | true | 1 | 32590:5 | `selectedHalfOpenTile_ae_eq_openTile` | LEAN_FAILURE
git:origin/ci/fa447-run-locator-20260810 | `c12778aa72fa9541b064e466d59c854283766e73c02fda1a586cf7380e7f7626` | true | 1 | 32592:5 | `selectedHalfOpenTile_ae_eq_openTile` | LEAN_FAILURE
git:origin/fix/fa424-cross-donor-controller-20260809 | `07f6efd3309c3cc23b86adf5811918b752b72c33a3f7a76213ce9beb10796da4` | true | 1 | 31725:2 | `actualEdgeAmbientParam_hasDerivAt` | LEAN_FAILURE
git:origin/fix/fa425-strict-theorem-tournament-20260810 | `df95374fdd9a3f58b42e4cc9a7a43ee6122ba1391b5d622dd6bbd08a10152b1a` | true | 1 | 32035:8 | `nativeActualEdgeFluxIntegral_paired_circular` | LEAN_FAILURE
git:origin/fix/fa425d-derivative-rebundle-20260810 | `0ab17080422c1cf0f57ebf14dd97ca349f2a997276c7dd6fd90a0a1f6e485811` | true | 1 | 31727:2 | `actualEdgeAmbientParam_hasDerivAt` | LEAN_FAILURE
git:origin/fix/fa425e-isolated-instance-section-20260810 | `39953828163b197c50d322a6ec245979ccaac56b5ef3beab1cfdc0a7d5f8cb6f` | true | 1 | 31727:117 | `actualEdgeAmbientParam_hasDerivAt` | LEAN_FAILURE
git:origin/fix/fa425i-disable-reenable-custom-20260810 | `0985fe1524fd89727abcb03290227a4e9c12cc461be3e0cdfeafaa3528af518b` | true | 1 | 31727:117 | `actualEdgeAmbientParam_hasDerivAt` | LEAN_FAILURE
git:origin/fix/fa426b-multiround-importsafe-20260810 | `7c0f8839e8d058f5cde6a76bcc125381135f6869be0ae8d4a1f12ef1ac168a7d` | true | 1 | 32079:8 | `nativeActualEdgeFluxIntegral_paired_left` | LEAN_FAILURE
git:origin/fix/fa429-continuation-after-fa426-20260810 | `49c1c0eac33f5e758d66a99955a1690592803406a21277d5b4b4d230072d1f74` | true | 1 | 32035:8 | `nativeActualEdgeFluxIntegral_paired_circular` | LEAN_FAILURE
git:origin/fix/fa444-complete-direct-matrix-20260810 | `4647a9463e4264a7f0e08405b7ccd1ce9be87e7227fa2b91dc52024e2e198152` | true | 1 | 32590:5 | `selectedHalfOpenTile_ae_eq_openTile` | LEAN_FAILURE
git:origin/fix/fa444-fa442-matrix-pipeline-repair-20260810 | `1243b2ba563d364a6977cbf9aa867e628de50a28b0f56677dc70456a210e209a` | true | 1 | 32035:79 | `nativeActualEdgeFluxIntegral_paired_circular` | LEAN_FAILURE

## Best direct-verified candidate

variant: `git:origin/ci/fa447-run-locator-20260810`

SHA256: `c12778aa72fa9541b064e466d59c854283766e73c02fda1a586cf7380e7f7626`

exit: `1`

first error: `32592:5`

declaration: `selectedHalfOpenTile_ae_eq_openTile`

strictly better than 31726?: `true`

## Checked-in identity

selected SHA: `c12778aa72fa9541b064e466d59c854283766e73c02fda1a586cf7380e7f7626`

worktree SHA: `c12778aa72fa9541b064e466d59c854283766e73c02fda1a586cf7380e7f7626`

HEAD source SHA: `c12778aa72fa9541b064e466d59c854283766e73c02fda1a586cf7380e7f7626`

identity_ok: `true`

## Trust audit

sorry: `0`

admit: `0`

global axiom: `0`

unsafe: `0`

native_decide: `0`

Lean.ofReduceBool: `0`

## FA checked-in verification

run1: exit `1`, errors `101`, olean `False`, ilean `False`

run2: exit `1`, errors `101`, olean `False`, ilean `False`

FA_TRUE_PASS: `false`

## Downstream

Integrated: `NOT_RUN_FA_NOT_TRUE_PASS`

Mock3 bridges: `NOT_RUN_FA_NOT_TRUE_PASS`

QYM: `NOT_RUN_FA_NOT_TRUE_PASS`

## Final classification

**STRICT PROMOTION**

## Branches/commits

branch: `fix/fa442-matrix-direct-compile-repair-20260810`

report commit/worktree HEAD: `fed9c870531fc81d33b0ec384886b69a33716d8b`

Workflow run URL: https://github.com/leegahuyn/mathlib4/actions/runs/31354569386

Artifact ID: `9050982724`
