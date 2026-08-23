# Research Paper Formalization Audit

> **AI-assisted Lean 4 / Mathlib audit of ten mathematical manuscript sketches (507 pages), developed using GPT and Codex to identify errors, isolate assumptions, construct counterexamples, and machine-check the formalizable cores.**

**Scope:** 10 manuscript sketches · 507 pages · ~352k Lean LOC  
**Proof assistant:** Lean 4 + Mathlib  
**Pinned Lean toolchain:** `leanprover/lean4:v4.33.0-rc1`  
**AI assistance:** GPT + Codex  
**Primary objective:** public, reproducible mathematical auditing — not a claim that every sentence of every manuscript has been proved.

This repository packages a large experiment in **AI-assisted mathematical auditing and formalization**. The workflow is deliberately explicit:

`AI-assisted manuscript draft → Lean formal audit → proof/counterexample/error detection → corrected or conditional statement → machine-checkable artifact`

The important artifact is not the line count by itself. The goal is to make it possible for another person to inspect the statements, assumptions, corrections, proof interfaces, and build evidence without relying on the author's description alone.

## What is being audited

The formalization sources are under [`PrimalitySheafVerification/`](./PrimalitySheafVerification/). The current aggregate target contains **thirteen primary verification modules** plus two mandatory integration bridges.

| Manuscript family | Primary Lean modules | Integration / aggregate role |
|---|---|---|
| Manuscripts 1–7 | `Spt1.lean` … `Spt7.lean` | Seven primary modules |
| Manuscript 8 / Mock 1 family | `Mock1.lean`, `Mock1_Advanced.lean` | Elementary + advanced audit |
| Manuscript 9 / Mock 2 family | `Mock2.lean`, `Mock2_Advanced.lean`, `Mock2_FunctionalAnalysis.lean` | `Mock2_FunctionalAnalysis_Integrated.lean` is the integration bridge |
| Manuscript 10 / Mock 3–QYM family | `QYM.lean` | `Mock3.lean` is the integration bridge |

The canonical aggregate importer is [`PrimalitySheafVerification/BuildAll.lean`](./PrimalitySheafVerification/BuildAll.lean). A repository-root [`BuildAll.lean`](./BuildAll.lean) is provided as the public entry point.

> The family labels above describe the present code grouping. A standalone release should replace generic manuscript labels with the final public titles and manuscript links/identifiers.

## Reproduce the aggregate check

From a clean checkout of this repository/ref:

```bash
git clone https://github.com/leegahuyn/mathlib4.git
cd mathlib4
git checkout standalone-repo-prep-2026-08-24
lake exe cache get
lake env lean BuildAll.lean
```

A release should be described as **clean-build verified only when this command exits with status 0 on a clean checkout**, together with the project's forbidden-feature / assumption audits. A README, commit, workflow name, or generated candidate is not by itself proof of a successful aggregate build.

### Reproducibility anchor

This packaging branch was created from the frozen source ref `formalization-final-authority-2026-08-21`, resolving to source commit:

`8f7e861f5f76c0aa5d347e0de865516a1ba23922`

The Lean toolchain is pinned by [`lean-toolchain`](./lean-toolchain) to:

`leanprover/lean4:v4.33.0-rc1`

Because this preparation branch is still based on a full Mathlib fork, the **exact repository commit is part of the Mathlib source snapshot**. When the project is extracted into a small standalone repository, the equivalent Mathlib dependency commit must be pinned explicitly in the Lake manifest/configuration; do not replace it with a floating `master` dependency.

## Verification status — read this before citing the project

This branch is a **standalone-repository packaging branch**, not a declaration that every aggregate authority gate is green.

Before a public release/tag is called verified, record at minimum:

- `lake env lean BuildAll.lean` → exit `0` from a clean checkout;
- the exact Git commit SHA and hashes of the principal large artifacts;
- the exact Lean/Mathlib dependency pins;
- an audit for `sorry` / `sorryAx` and any newly introduced axioms;
- an audit for prohibited proof shortcuts used by the project policy (for example, any forbidden `native_decide` usage if that is part of the release policy);
- the explicit hypothesis set for every result classified as conditional;
- two repeat clean builds if the release protocol requires reproducibility across repeated runs;
- preserved CI logs / JSON evidence sufficient to reconstruct the final authority decision.

Do **not** infer mathematical status from file size, warning count, branch names, or generated workflow activity.

## Result-status vocabulary

The following labels are intended to prevent a formal artifact from being described more strongly than it deserves.

| Label | Meaning |
|---|---|
| **PROVED** | The stated Lean theorem has a kernel-checked proof from its declared imports and assumptions; no additional project-specific conjecture is being silently treated as proved. |
| **CONDITIONAL** | Lean proves the result from hypotheses that encode assumptions not established by the project. Those hypotheses must be visible and documented. |
| **CERTIFICATE** | Lean checks a concrete witness, finite computation, identity, bound, or other certificate relevant to the manuscript claim. This is evidence for the certified statement, not automatically a proof of a broader narrative claim. |
| **INTERFACE** | A formal specification, abstraction boundary, or bridge is provided, but the full mathematical content advertised by the surrounding prose is not claimed to be proved. |
| **CORRECTED** | Formalization exposed a problem in the manuscript statement and the repository proves/checks a corrected formulation. |
| **NO-GO** | The original formulation is false, inconsistent with other stated claims, unsupported at the required level, or otherwise cannot honestly be promoted as a proved theorem in its stated form. Counterexamples or blocker evidence should be preserved where available. |

These labels are **semantic audit labels**, not decorations. They should be assigned theorem-by-theorem or manuscript-by-manuscript only after checking that the Lean statement matches the mathematical claim being classified.

## A concrete correction found by formalization

The project already contains an example of why the audit layer matters. In the primality-sheaf manuscript, the paper attached a `min(v_p M, k)` thickness formula to the localized **intersection / lcm** object. The formalization separates the two quantities:

- the `p`-adic valuation of the relevant `lcm` uses **`max`**;
- the valuation of the `gcd` / common-residue-fiber / `Tor₁` quantity uses **`min`**.

For the manuscript's own example `M = 12`, `p = 3`, `k = 2`, the intersection is generated by `lcm(12, 9) = 36`, whose 3-adic thickness is `2 = max(1,2)`, while the common residue quantity has exponent `1 = min(1,2)`.

That is the intended research story of this repository: not “AI generated a very large Lean codebase,” but **formal checking forced two mathematically different objects to be distinguished and exposed a statement that needed correction**. The detailed catalogue is preserved in [`PrimalitySheafVerification/README.md`](./PrimalitySheafVerification/README.md).

## AI-use disclosure

This project is explicitly **AI-assisted**.

GPT and Codex were used for tasks including manuscript-to-formal-statement translation, Lean code generation, proof-search assistance, refactoring, debugging, candidate generation, documentation, and the investigation of formalization failures. The use of AI is part of the experimental workflow and is not hidden.

The project therefore does **not** make the claim that one human manually typed or independently discovered every line of the Lean source. Likewise, AI output is not treated as mathematical authority merely because it is plausible or extensive.

For compiled declarations, the Lean kernel is the final checker of the formal proof term. Separate human/audit responsibility remains necessary for questions the kernel cannot answer automatically, especially:

1. whether the Lean theorem actually expresses the corresponding manuscript statement;
2. whether hypotheses have been weakened, strengthened, or silently changed;
3. whether a theorem is unconditional or only conditional;
4. whether a computational certificate supports the broader mathematical interpretation attached to it;
5. whether an apparent correction or counterexample has been interpreted correctly in the manuscript context.

## What an independent reviewer should check first

A useful review does not need to start by reading ~352k lines. Start with:

1. **Clean checkout:** does `lake env lean BuildAll.lean` actually compile?
2. **Assumption audit:** are there `sorryAx`, project-specific axioms, or forbidden proof shortcuts?
3. **Statement correspondence:** do the Lean statements match the manuscript claims they are said to audit?
4. **Conditionality:** are certificate hypotheses and unproved assumptions explicit?
5. **Corrections:** which manuscript statements changed because formalization found an error or counterexample?
6. **AI boundary:** which parts were generated/assisted by GPT or Codex, and what was independently checked afterward?

## Repository layout

```text
BuildAll.lean                         # public aggregate entry point
PrimalitySheafVerification/
  BuildAll.lean                       # canonical aggregate importer
  Verification.lean                   # focused primality-sheaf verification
  Spt1.lean … Spt7.lean               # seven primary manuscript modules
  Mock1.lean
  Mock1_Advanced.lean
  Mock2.lean
  Mock2_Advanced.lean
  Mock2_FunctionalAnalysis.lean
  Mock2_FunctionalAnalysis_Integrated.lean
  QYM.lean
  Mock3.lean
build-evidence/                        # preserved verification evidence
build-logs/                            # preserved build logs where applicable
```

The historical fork contains substantially more development, repair, and workflow evidence than a reader needs on the first screen. A final standalone repository should keep the audit trail that is necessary for reproducibility while moving exploratory repair machinery out of the primary reading path.

## Recommended standalone identity

Recommended repository name:

**`research-paper-formalization-audit`**

Suggested GitHub description:

> AI-assisted Lean 4/Mathlib audit of 10 mathematical manuscript sketches (507 pages), with machine-checkable proofs, assumptions, corrections, counterexamples, and reproducible build evidence.

Suggested topics:

`lean4` · `mathlib` · `formal-mathematics` · `theorem-proving` · `formal-verification` · `ai-assisted-mathematics`

No community announcement is required for the repository to be useful. The objective here is **passive discoverability**: if a researcher finds the artifact independently, the first page should make its purpose, limitations, verification path, and AI involvement immediately understandable.

## Release policy

Do not create a “verified” release merely because the source has been frozen. A release/tag should identify one exact authority commit for which the documented aggregate build and audits have actually passed. Preserve the evidence and make the release immutable in practice by citing the exact commit SHA and artifact hashes.

## Attribution and license note

This preparation branch still contains the full Mathlib fork and therefore must preserve Mathlib's existing license and attribution requirements. If the formalization project is extracted into a smaller standalone repository, retain all licenses/notices required by copied Mathlib-derived material and clearly distinguish project-authored files from upstream dependencies.
