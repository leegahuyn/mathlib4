# FA → QYM → 13 Files → Clean Build → 15 Checks

## Authority applied at continuation start

The continuation starts from the latest fully evidenced FA baseline, not from a green job label.

- Repository: `leegahuyn/mathlib4`
- Branch: `codex/fa-qym-cleanbuild-final-20260811-fast`
- Authority workflow run: `31758486070`
- Authority artifact: `9204077135`
- Authority artifact name: `codex-fa-v47-safe_w06_funprop_w27-highcap2000-d699d23a23d6676d18880710e6c1fa7d443be482`
- Authority artifact digest: `sha256:dbabd49d16ddcbd8f67a7b623cd0c45785d602c03d66dfb0833016e25ddcc0fa`
- Authority source SHA256: `c255c100f33c09cafc37276f967b9cd535e0ddd76460df149d71d632d8644a63`
- Authority source bytes: `2795882`
- Authority source lines: `62555`
- Authority declarations: `4416`
- `Mock2.lean`: direct Lean exit `0`
- `Mock2_Advanced.lean`: direct Lean exit `0`
- `Mock2_FunctionalAnalysis.lean`: direct Lean exit `1`
- FA actual error headers: `35`
- FA declarations with errors: `19`
- FA normalized signatures: `11`
- FA first error: line `49130`, column `6`
- FA first error declaration: `integrable_fullPlaneTest_mul_kernel_mul_translate`
- FA first error declaration index: `3669`
- Executable-code trust audit: all six channels zero
- Synthetic `declaration uses 'sorry'` warnings: zero

The authority baseline is therefore **FA FAIL**, despite candidate jobs having executed. No later stage may relabel it PASS without a new exact direct-Lean gate.

## Installed continuation stages

1. `scripts/fa_v48_auto_repair.py`
   - Re-proves the exact v47 authority source and artifact identity.
   - Generates eight clustered candidates.
   - Preserves the declaration sequence and six-channel trust-zero invariant.

2. `.github/workflows/codex-fa-v48-auto-repair-highcap2000.yml`
   - Runs `Mock2 → Mock2_Advanced → full FA` for every candidate.
   - Uses `-DmaxErrors=2000` and captures the complete diagnostic inventory.
   - Selects only a direct-Lean PASS or a strict metric improvement.
   - Does not treat an intentionally failed “preserve actual exit” step as a skipped compile.

3. `scripts/fa_iterative_frontier_repair.py`
   - Maps actual Lean diagnostics to enclosing declarations.
   - Generates evidence-scoped frontier repairs.
   - Rejects declaration-sequence changes and all six forbidden trust channels.

4. `.github/workflows/codex-fa-v49-iterative-frontier.yml`
   - Recompiles the exact checked-in FA baseline.
   - Runs eight dynamic frontier candidates.
   - Commits only strict direct-Lean improvement.
   - Supports repeated iterations through explicit orchestration.

5. `scripts/lean_collect_exact_diagnostics.py`
   - Provides source-agnostic direct-Lean metrics for QYM and later files.
   - Records source identity, exact exit, error headers, first declaration, signature inventory, trust counts, and synthetic-sorry warnings.

6. `.github/workflows/codex-qym-v1-iterative-frontier.yml`
   - Refuses to start QYM repair unless `Mock2`, `Mock2_Advanced`, and FA are direct-clean in the same run.
   - Uses eight dynamic QYM candidates and the same strict improvement rule.
   - Never advances QYM from a blocked or skipped prerequisite chain.

7. `scripts/final13_15checklist.py`
   - Builds exact before/after source manifests.
   - Evaluates the final 15 independent gates.
   - Produces machine-readable JSON and a human-readable Markdown report.

8. `.github/workflows/codex-final-13files-15checklist.yml`
   - Executes two full direct-Lean passes.
   - Executes the strict core dependency chain.
   - Runs `lake clean`, restores the pinned cache, and runs the project build.
   - Compiles one aggregate module importing all 13 required modules.
   - Creates an immutable clean-source tag only after checks 1–14 pass.

9. `.github/workflows/codex-new-pipeline-selfcheck-and-fix.yml`
   - `py_compile`s all new Python engines.
   - Parses all new workflows as YAML.
   - Repairs the pristine-checkout evidence ordering before final use.

10. `.github/workflows/codex-fa-qym-final-orchestrator.yml`
    - Dispatches follow-up runs explicitly rather than relying on recursive `GITHUB_TOKEN` push events.
    - Reads selector and gate JSON, not superficial workflow color.
    - Stops at FA or QYM blockers without falsifying later results.

11. `.github/workflows/codex-dispatch-fresh-v48-after-pipeline-install.yml`
    - Starts a fresh v48 run after the continuation files settle on the branch.

## Exact 13 required Lean files

1. `PrimalitySheafVerification/Spt1.lean`
2. `PrimalitySheafVerification/Spt2.lean`
3. `PrimalitySheafVerification/Spt3.lean`
4. `PrimalitySheafVerification/Spt4.lean`
5. `PrimalitySheafVerification/Spt5.lean`
6. `PrimalitySheafVerification/Spt6.lean`
7. `PrimalitySheafVerification/Spt7.lean`
8. `PrimalitySheafVerification/Mock1.lean`
9. `PrimalitySheafVerification/Mock1_Advanced.lean`
10. `PrimalitySheafVerification/Mock2.lean`
11. `PrimalitySheafVerification/Mock2_Advanced.lean`
12. `PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean`
13. `PrimalitySheafVerification/QYM.lean`

## Final 15 independent gates

1. Exact branch commit and initially pristine checkout are locked.
2. The `lean-toolchain` pin is installed and exact Lean/Lake versions are recorded.
3. `lean-toolchain`, `lake-manifest.json`, and `lakefile.lean` identities are SHA256-recorded.
4. All exact 13 source files exist at canonical paths.
5. SHA256, byte count, line count, and declaration count exist for every source.
6. All source hashes and declaration sequences remain unchanged through verification.
7. Executable-code `sorry` and `admit` counts are zero in every file.
8. Executable-code `axiom` and `unsafe` counts are zero in every file.
9. Executable-code `native_decide` and `Lean.ofReduceBool` counts are zero in every file.
10. Every one of the 13 files passes a first actual direct Lean compile.
11. `Mock2 → Mock2_Advanced → Mock2_FunctionalAnalysis → QYM` passes in strict order.
12. `lake clean`, pinned cache restoration, and project build all exit zero.
13. A generated module importing all 13 required modules passes direct Lean.
14. A second complete direct Lean pass is clean, source-identical, uncapped, and free of synthetic-sorry warnings.
15. The complete evidence set is cryptographically inventoried and an immutable tag is verified against the exact clean source commit.

## Non-negotiable PASS semantics

The following are not a PASS:

- A workflow job whose compile step was skipped.
- A green selector with no exact candidate source and no metric JSON.
- A compile wrapper that swallowed the real Lean exit code.
- Error-count reduction without a strict frontier/declaration improvement.
- A source that changes the public declaration sequence.
- Any nonzero executable occurrence of `sorry`, `admit`, `axiom`, `unsafe`, `native_decide`, or `Lean.ofReduceBool`.
- Any synthetic `declaration uses 'sorry'` warning.
- QYM evidence produced while FA prerequisites were not direct-clean.
- A 13-file result that omitted even one canonical source.
- A final report with fewer than `15/15` PASS items.

The authoritative final success record is `FINAL_15_CHECKLIST.json` with `status: PASS` and `passed_count: 15`, backed by raw logs and the immutable source tag. Until that exists, the project remains in progress.
