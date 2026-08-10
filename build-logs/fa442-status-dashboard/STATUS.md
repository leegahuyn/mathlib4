# FA442 / FA443 STATUS DASHBOARD

Workflow conclusion and Lean/pipeline classification are deliberately shown separately.

branch | run | workflow status | workflow conclusion | Lean/pipeline classification | artifacts
--- | --- | --- | --- | --- | ---
`fix/fa442-skip-root-cause-20260810` | [31355069192](https://github.com/leegahuyn/mathlib4/actions/runs/31355069192) | queued | None | **NO_COMMITTED_REPORT** | NONE
`fix/fa442-matrix-direct-compile-repair-20260810` | [31354569386](https://github.com/leegahuyn/mathlib4/actions/runs/31354569386) | in_progress | None | **NO_COMMITTED_REPORT** | fa442-metric-git-origin-fix-fa424-cross-donor-controller-20260809-31354569386 (`9050549314`), fa442-metric-git-origin-ci-fa447-run-locator-20260810-31354569386 (`9050533561`), fa442-prep-31354569386 (`9050209026`)
`fix/fa442-sequential-direct-tournament-20260810` | [31354847621](https://github.com/leegahuyn/mathlib4/actions/runs/31354847621) | in_progress | None | **NO_COMMITTED_REPORT** | NONE
`fix/fa443-blocker-body-tournament-20260810` | [31355435033](https://github.com/leegahuyn/mathlib4/actions/runs/31355435033) | in_progress | None | **NO_COMMITTED_REPORT** | NONE

## Job steps

### `fix/fa442-skip-root-cause-20260810`

- `diagnose`: status `queued`, conclusion `None`

### `fix/fa442-matrix-direct-compile-repair-20260810`

- `Diagnose FA442 and recover baseline/candidate sources`: status `completed`, conclusion `success`
  - 1. Set up job: `completed` / `success`
  - 2. Checkout pipeline repair branch: `completed` / `success`
  - 3. Configure Git identity: `completed` / `success`
  - 4. Inspect FA442 workflow, jobs, artifacts, and build matrix: `completed` / `success`
  - 5. Upload recovered sources and root-cause evidence: `completed` / `success`
  - 10. Post Checkout pipeline repair branch: `completed` / `success`
  - 11. Complete job: `completed` / `success`
- `direct metric / git-origin-fix-fa425d-derivative-rebundle-20260810`: status `in_progress`, conclusion `None`
  - 1. Set up job: `completed` / `success`
  - 2. Checkout exact pipeline repair branch: `completed` / `success`
  - 3. Configure Git identity: `completed` / `success`
  - 4. Install pinned Lean and Mathlib cache: `completed` / `success`
  - 5. Download authoritative candidate bundle: `completed` / `success`
  - 6. Directly compile completed prerequisites and candidate FA: `in_progress` / `None`
  - 7. Upload candidate source, direct logs, and metric: `pending` / `None`
  - 8. Enforce actual Lean execution or explicit infrastructure failure: `pending` / `None`
  - 16. Post Checkout exact pipeline repair branch: `pending` / `None`
- `direct metric / git-origin-fix-fa425e-isolated-instance-section-20260810`: status `in_progress`, conclusion `None`
  - 1. Set up job: `completed` / `success`
  - 2. Checkout exact pipeline repair branch: `completed` / `success`
  - 3. Configure Git identity: `completed` / `success`
  - 4. Install pinned Lean and Mathlib cache: `completed` / `success`
  - 5. Download authoritative candidate bundle: `completed` / `success`
  - 6. Directly compile completed prerequisites and candidate FA: `in_progress` / `None`
  - 7. Upload candidate source, direct logs, and metric: `pending` / `None`
  - 8. Enforce actual Lean execution or explicit infrastructure failure: `pending` / `None`
  - 16. Post Checkout exact pipeline repair branch: `pending` / `None`
- `direct metric / git-origin-fix-fa425-strict-theorem-tournament-20260810`: status `in_progress`, conclusion `None`
  - 1. Set up job: `completed` / `success`
  - 2. Checkout exact pipeline repair branch: `completed` / `success`
  - 3. Configure Git identity: `completed` / `success`
  - 4. Install pinned Lean and Mathlib cache: `completed` / `success`
  - 5. Download authoritative candidate bundle: `completed` / `success`
  - 6. Directly compile completed prerequisites and candidate FA: `in_progress` / `None`
  - 7. Upload candidate source, direct logs, and metric: `pending` / `None`
  - 8. Enforce actual Lean execution or explicit infrastructure failure: `pending` / `None`
  - 16. Post Checkout exact pipeline repair branch: `pending` / `None`
- `direct metric / git-origin-fix-fa425i-disable-reenable-custom-20260810`: status `in_progress`, conclusion `None`
  - 1. Set up job: `completed` / `success`
  - 2. Checkout exact pipeline repair branch: `completed` / `success`
  - 3. Configure Git identity: `completed` / `success`
  - 4. Install pinned Lean and Mathlib cache: `completed` / `success`
  - 5. Download authoritative candidate bundle: `completed` / `success`
  - 6. Directly compile completed prerequisites and candidate FA: `in_progress` / `None`
  - 7. Upload candidate source, direct logs, and metric: `pending` / `None`
  - 8. Enforce actual Lean execution or explicit infrastructure failure: `pending` / `None`
  - 16. Post Checkout exact pipeline repair branch: `pending` / `None`
- `direct metric / baseline`: status `in_progress`, conclusion `None`
  - 1. Set up job: `completed` / `success`
  - 2. Checkout exact pipeline repair branch: `completed` / `success`
  - 3. Configure Git identity: `completed` / `success`
  - 4. Install pinned Lean and Mathlib cache: `completed` / `success`
  - 5. Download authoritative candidate bundle: `completed` / `success`
  - 6. Directly compile completed prerequisites and candidate FA: `in_progress` / `None`
  - 7. Upload candidate source, direct logs, and metric: `pending` / `None`
  - 8. Enforce actual Lean execution or explicit infrastructure failure: `pending` / `None`
  - 16. Post Checkout exact pipeline repair branch: `pending` / `None`
- `direct metric / git-origin-fix-fa444-fa442-matrix-pipeline-repair-20260810`: status `in_progress`, conclusion `None`
  - 1. Set up job: `completed` / `success`
  - 2. Checkout exact pipeline repair branch: `completed` / `success`
  - 3. Configure Git identity: `completed` / `success`
  - 4. Install pinned Lean and Mathlib cache: `completed` / `success`
  - 5. Download authoritative candidate bundle: `completed` / `success`
  - 6. Directly compile completed prerequisites and candidate FA: `in_progress` / `None`
  - 7. Upload candidate source, direct logs, and metric: `pending` / `None`
  - 8. Enforce actual Lean execution or explicit infrastructure failure: `pending` / `None`
  - 16. Post Checkout exact pipeline repair branch: `pending` / `None`
- `direct metric / git-origin-fix-fa444-complete-direct-matrix-20260810`: status `in_progress`, conclusion `None`
  - 1. Set up job: `completed` / `success`
  - 2. Checkout exact pipeline repair branch: `completed` / `success`
  - 3. Configure Git identity: `completed` / `success`
  - 4. Install pinned Lean and Mathlib cache: `completed` / `success`
  - 5. Download authoritative candidate bundle: `completed` / `success`
  - 6. Directly compile completed prerequisites and candidate FA: `in_progress` / `None`
  - 7. Upload candidate source, direct logs, and metric: `pending` / `None`
  - 8. Enforce actual Lean execution or explicit infrastructure failure: `pending` / `None`
  - 16. Post Checkout exact pipeline repair branch: `pending` / `None`
- `direct metric / git-origin-fix-fa426b-multiround-importsafe-20260810`: status `in_progress`, conclusion `None`
  - 1. Set up job: `completed` / `success`
  - 2. Checkout exact pipeline repair branch: `completed` / `success`
  - 3. Configure Git identity: `completed` / `success`
  - 4. Install pinned Lean and Mathlib cache: `completed` / `success`
  - 5. Download authoritative candidate bundle: `completed` / `success`
  - 6. Directly compile completed prerequisites and candidate FA: `in_progress` / `None`
  - 7. Upload candidate source, direct logs, and metric: `pending` / `None`
  - 8. Enforce actual Lean execution or explicit infrastructure failure: `pending` / `None`
  - 16. Post Checkout exact pipeline repair branch: `pending` / `None`
- `direct metric / git-origin-fix-fa424-cross-donor-controller-20260809`: status `completed`, conclusion `success`
  - 1. Set up job: `completed` / `success`
  - 2. Checkout exact pipeline repair branch: `completed` / `success`
  - 3. Configure Git identity: `completed` / `success`
  - 4. Install pinned Lean and Mathlib cache: `completed` / `success`
  - 5. Download authoritative candidate bundle: `completed` / `success`
  - 6. Directly compile completed prerequisites and candidate FA: `completed` / `success`
  - 7. Upload candidate source, direct logs, and metric: `completed` / `success`
  - 8. Enforce actual Lean execution or explicit infrastructure failure: `completed` / `success`
  - 16. Post Checkout exact pipeline repair branch: `completed` / `success`
  - 17. Complete job: `completed` / `success`
- `direct metric / git-origin-fix-fa429-continuation-after-fa426-20260810`: status `in_progress`, conclusion `None`
  - 1. Set up job: `completed` / `success`
  - 2. Checkout exact pipeline repair branch: `completed` / `success`
  - 3. Configure Git identity: `completed` / `success`
  - 4. Install pinned Lean and Mathlib cache: `completed` / `success`
  - 5. Download authoritative candidate bundle: `completed` / `success`
  - 6. Directly compile completed prerequisites and candidate FA: `in_progress` / `None`
  - 7. Upload candidate source, direct logs, and metric: `pending` / `None`
  - 8. Enforce actual Lean execution or explicit infrastructure failure: `pending` / `None`
  - 16. Post Checkout exact pipeline repair branch: `pending` / `None`
- `direct metric / git-origin-ci-fa444-complete-run-locator-20260810`: status `in_progress`, conclusion `None`
  - 1. Set up job: `completed` / `success`
  - 2. Checkout exact pipeline repair branch: `completed` / `success`
  - 3. Configure Git identity: `completed` / `success`
  - 4. Install pinned Lean and Mathlib cache: `completed` / `success`
  - 5. Download authoritative candidate bundle: `completed` / `success`
  - 6. Directly compile completed prerequisites and candidate FA: `in_progress` / `None`
  - 7. Upload candidate source, direct logs, and metric: `pending` / `None`
  - 8. Enforce actual Lean execution or explicit infrastructure failure: `pending` / `None`
  - 16. Post Checkout exact pipeline repair branch: `pending` / `None`
- `direct metric / git-origin-ci-fa447-run-locator-20260810`: status `completed`, conclusion `success`
  - 1. Set up job: `completed` / `success`
  - 2. Checkout exact pipeline repair branch: `completed` / `success`
  - 3. Configure Git identity: `completed` / `success`
  - 4. Install pinned Lean and Mathlib cache: `completed` / `success`
  - 5. Download authoritative candidate bundle: `completed` / `success`
  - 6. Directly compile completed prerequisites and candidate FA: `completed` / `success`
  - 7. Upload candidate source, direct logs, and metric: `completed` / `success`
  - 8. Enforce actual Lean execution or explicit infrastructure failure: `completed` / `success`
  - 16. Post Checkout exact pipeline repair branch: `completed` / `success`
  - 17. Complete job: `completed` / `success`

### `fix/fa442-sequential-direct-tournament-20260810`

- `direct-tournament`: status `in_progress`, conclusion `None`
  - 1. Set up job: `completed` / `success`
  - 2. Checkout sequential repair branch: `completed` / `success`
  - 3. Configure Git identity: `completed` / `success`
  - 4. Install pinned Lean and Mathlib cache: `completed` / `success`
  - 5. Diagnose FA442 and recover exact baseline/candidates: `completed` / `success`
  - 6. Directly compile every recovered baseline/candidate variant: `in_progress` / `None`
  - 7. Strict selector over current-run direct metrics: `pending` / `None`
  - 8. Persist selected source with selected/worktree/HEAD identity: `pending` / `None`
  - 9. Checked-in FA direct compile run1/run2 and trust audit: `pending` / `None`
  - 10. Ordered downstream gate only after FA TRUE PASS: `pending` / `None`
  - 11. Generate preliminary report: `pending` / `None`
  - 12. Upload full sequential evidence: `pending` / `None`
  - 13. Finalize and commit report with artifact ID: `pending` / `None`
  - 14. Enforce every variant direct-executed and no current infrastructure failure: `pending` / `None`
  - 28. Post Checkout sequential repair branch: `pending` / `None`

### `fix/fa443-blocker-body-tournament-20260810`

- `tournament`: status `in_progress`, conclusion `None`
  - 1. Set up job: `completed` / `success`
  - 2. Checkout FA443 branch: `completed` / `success`
  - 3. Configure Git identity: `completed` / `success`
  - 4. Install pinned Lean and Mathlib cache: `completed` / `success`
  - 5. Recover FA442 baseline and candidate bundle; diagnose skip root cause: `in_progress` / `None`
  - 6. Re-run baseline and every FA442 candidate by direct Lean CLI: `pending` / `None`
  - 7. Strictly select recovered current-run direct champion: `pending` / `None`
  - 8. Persist recovered direct champion before new proof search: `pending` / `None`
  - 9. Reverify materialized recovered champion directly: `pending` / `None`
  - 10. Generate FA443 blocker proof-body candidate set: `pending` / `None`
  - 11. Directly compile every FA443 round-1 proof candidate: `pending` / `None`
  - 12. Strictly select FA443 round-1 candidate: `pending` / `None`
  - 13. Persist FA443 round-1 selection and exact identity: `pending` / `None`
  - 14. Reverify FA443 round-1 checked-in frontier: `pending` / `None`
  - 15. Generate FA443 round-2 cumulative candidates after strict non-pass promotion: `pending` / `None`
  - 16. Directly compile every FA443 round-2 candidate: `pending` / `None`
  - 17. Strictly select FA443 round-2 candidate: `pending` / `None`
  - 18. Persist FA443 round-2 selection: `pending` / `None`
  - 19. Reverify FA443 round-2 checked-in frontier: `pending` / `None`
  - 20. Resolve final checked-in FA443 selection: `pending` / `None`
  - 21. Full checked-in FA compile run1/run2 and trust audit for exit-zero candidate: `pending` / `None`
  - 22. Ordered Integrated, Mock3 bridges, QYM gate after FA TRUE PASS: `pending` / `None`
  - 23. Write FA443 final status: `pending` / `None`
  - 24. Upload complete FA443 evidence: `pending` / `None`
  - 25. Commit final status and compact evidence: `pending` / `None`
  - 26. Enforce pipeline and tournament infrastructure only: `pending` / `None`
  - 52. Post Checkout FA443 branch: `pending` / `None`

