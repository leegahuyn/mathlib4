# Research Paper Formalization Audit

> **AI-assisted Lean 4 / Mathlib audit of ten mathematical manuscript sketches (507 pages), developed using GPT and Codex to identify errors, isolate assumptions, construct counterexamples, and machine-check the formalizable cores.**

**Scope:** 10 manuscript sketches · 507 pages · ~352k Lean LOC  
**Proof assistant:** Lean 4 + Mathlib  
**Pinned Lean toolchain:** `leanprover/lean4:v4.33.0-rc1`  
**Artifact version:** `v1.0.0`  
**AI assistance:** GPT + Codex  
**Primary objective:** public, reproducible mathematical auditing — not a claim that every sentence of every manuscript has been proved.

**Integrated manuscript bundle (10 manuscripts / 507 pages):** [overleaf_bundle (Copy).pdf — Google Drive](https://drive.google.com/file/d/1nmbfHF5Qkw8kFMwHn9CmnjWpGZuGKi2X/view)

The Master Evidence Index records the exact audited bundle snapshot as `overleaf_bundle (Copy)(20260812-034123).pdf`, **507 physical PDF pages**, **4,304,556 bytes**, SHA-256:

`12eb737301b3312dbad255f7b6d2f74c43c9ba27a2955157c134d36c9c0e53c5`

For exact-byte reproducibility, the filename, size, and SHA-256 above are the identity anchor.

## Publication state

This repository publishes the frozen formalization artifact from:

- repository: `leegahuyn/mathlib4`;
- canonical frozen branch: `frozen-pre-release-2026-08-24`;
- artifact version: `v1.0.0`;
- publication date: **2026-08-24**.

The frozen branch is the canonical source snapshot. The repository default branch is maintained so that the project is visible from the repository landing page rather than being hidden only on a non-default development branch.

The presence of a public repository, README, release label, branch name, or large line count is not by itself a mathematical verification claim. The Lean declarations and preserved build/audit evidence remain the relevant verification authority.

## Ten manuscripts and Lean correspondence

The 507-page bundle contains the following ten manuscripts. Physical PDF page ranges include the bundle's two front-matter pages.

| # | Manuscript | Physical PDF pages | Primary Lean authority |
|---:|---|---:|---|
| 1 | **Primality Sheaf via Local Filters and Derived Equalizers** | 5–26 | `Spt1.lean`; focused audit in `Verification.lean` |
| 2 | **Master Equivalence on Arithmetic Curves** | 27–51 | `Spt2.lean` |
| 3 | **A Primality Sheaf and Global Certification** | 52–91 | `Spt3.lean` |
| 4 | **Primality Sheaves and the Étale–Motivic–Derived Package on Arithmetic Curves** | 92–145 | `Spt4.lean` |
| 5 | **Principal-Open Methods on Arithmetic Curves: From Equalizer–Tor to Supersingular Dichotomy** | 146–183 | `Spt5.lean` |
| 6 | **Equalizer–Tor, Gate Synchronization, and Étale–Motivic Detectors on Arithmetic Curves** | 184–226 | `Spt6.lean` |
| 7 | **Geometric Reformulation of the Riemann Hypothesis via a Four-Layer Sheaf Framework** | 227–297 | `Spt7.lean` |
| 8 | **Entropy–Growth and Sheaf Stability for Mock/Partial Theta and Jacobi Objects** | 298–397 | `Mock1.lean`, `Mock1_Advanced.lean` |
| 9 | **Global Poincaré Matching and Kloosterman-Compatible Test Kernels for Half-Integral Weight Mock–Theta Gauge Objects** | 398–458 | `Mock2.lean`, `Mock2_Advanced.lean`, `Mock2_FunctionalAnalysis.lean` |
| 10 | **Modular q–Yang–Mills on Γ(2)\H: Admissible Gauge Slices, Modular Flow, and a Spectral Mass–Gap Mechanism** | 459–507 | `QYM.lean` |

The aggregate target contains **thirteen primary verification modules**: `Spt1`–`Spt7` (7), the two Mock 1 modules (2), the three Mock 2 modules (3), and `QYM` (1). Two mandatory integration bridges, `Mock2_FunctionalAnalysis_Integrated.lean` and `Mock3.lean`, connect those primary modules into the aggregate build. `Verification.lean` is a focused Paper 1 audit and is not counted among the thirteen primary modules.

The canonical aggregate importer is [`PrimalitySheafVerification/BuildAll.lean`](./PrimalitySheafVerification/BuildAll.lean). A repository-root [`BuildAll.lean`](./BuildAll.lean) is provided as the public entry point.

## Reproduce the aggregate check

From the frozen artifact:

```bash
git clone https://github.com/leegahuyn/mathlib4.git
cd mathlib4
git checkout frozen-pre-release-2026-08-24
lake exe cache get
lake env lean BuildAll.lean
```

A successful clean run checks the formal artifact under the pinned repository state. It does not, by itself, establish that every Lean statement exactly captures every manuscript sentence; statement correspondence and interpretation remain separate review tasks.

## Reproducibility anchor

The publication lineage is anchored to the frozen source history and the repository commit reached by `frozen-pre-release-2026-08-24`.

The Lean toolchain is pinned by [`lean-toolchain`](./lean-toolchain) to:

`leanprover/lean4:v4.33.0-rc1`

Because this repository is based on a full Mathlib fork, the exact repository commit is part of the dependency snapshot. Independent reviewers should therefore cite the exact frozen branch or release commit rather than a moving upstream Mathlib branch.

## Verification status — read this before citing the project

The formalization is intended to be inspected through the actual Lean sources and evidence. At minimum, a reviewer should check:

- `lake env lean BuildAll.lean` from a clean checkout;
- the exact Git commit SHA and hashes of the principal artifacts;
- the exact Lean/Mathlib dependency pins;
- the `sorry` / `sorryAx` and project-specific axiom audit;
- any project policy concerning prohibited proof shortcuts;
- the explicit hypothesis set for results classified as conditional;
- preserved build logs / JSON evidence where supplied.

Do **not** infer mathematical status from file size, warning count, branch names, or generated workflow activity. The manuscript-to-module table is a correspondence map, **not** a manuscript-wide claim that every statement in a row is proved.

## Result-status vocabulary

| Label | Meaning |
|---|---|
| **PROVED** | The stated Lean theorem has a kernel-checked proof from its declared imports and assumptions; no additional project-specific conjecture is silently treated as proved. |
| **CONDITIONAL** | Lean proves the result from hypotheses that encode assumptions not established by the project. Those hypotheses must remain visible and documented. |
| **CERTIFICATE** | Lean checks a concrete witness, finite computation, identity, bound, or other certificate relevant to a manuscript claim. |
| **INTERFACE** | A formal specification, abstraction boundary, or bridge is provided without claiming that the full surrounding narrative has been proved. |
| **CORRECTED** | Formalization exposed a problem in a manuscript statement and the repository proves or checks a corrected formulation. |
| **NO-GO** | The original formulation is false, inconsistent, unsupported at the required level, or otherwise cannot honestly be promoted as proved in its stated form. |

These are semantic audit labels, not decorations. They should be assigned only after checking that the Lean statement matches the mathematical claim being classified.

## A concrete correction found by formalization

The primality-sheaf audit exposed a useful distinction. A manuscript formula attached `min(v_p M, k)` thickness to the localized **intersection / lcm** object, while the formalization separates two different quantities:

- the `p`-adic valuation of the relevant `lcm` uses **`max`**;
- the valuation of the `gcd` / common-residue-fiber / `Tor₁` quantity uses **`min`**.

For `M = 12`, `p = 3`, `k = 2`, the intersection is generated by `lcm(12, 9) = 36`, whose 3-adic thickness is `2 = max(1,2)`, while the common-residue quantity has exponent `1 = min(1,2)`.

This is the intended research role of the repository: formal checking can force mathematically different objects to be distinguished and can expose statements that require correction. The detailed catalogue is preserved in [`PrimalitySheafVerification/README.md`](./PrimalitySheafVerification/README.md).

## AI-use disclosure

This project is explicitly **AI-assisted**.

GPT and Codex were used for manuscript-to-formal-statement translation, Lean code generation, proof-search assistance, refactoring, debugging, candidate generation, documentation, and investigation of formalization failures. The use of AI is part of the experimental workflow and is not hidden.

The project therefore does **not** claim that one human manually typed or independently discovered every line of Lean source. Likewise, AI output is not treated as mathematical authority merely because it is plausible or extensive.

For compiled declarations, the Lean kernel checks the proof term. Separate human/audit responsibility remains necessary for questions the kernel cannot answer automatically, especially:

1. whether a Lean theorem actually expresses the corresponding manuscript statement;
2. whether hypotheses have been weakened, strengthened, or silently changed;
3. whether a theorem is unconditional or conditional;
4. whether a computational certificate supports the broader interpretation attached to it;
5. whether a correction or counterexample has been interpreted correctly in manuscript context.

## What an independent reviewer should check first

1. **Manuscript identity:** compare the integrated 507-page bundle with the recorded SHA-256 when exact identity matters.
2. **Clean checkout:** run `lake env lean BuildAll.lean` on `frozen-pre-release-2026-08-24`.
3. **Assumption audit:** inspect `sorryAx`, project-specific axioms, and any prohibited proof shortcuts.
4. **Statement correspondence:** compare Lean declarations with the manuscript claims they audit.
5. **Conditionality:** identify explicit hypotheses and unproved assumptions.
6. **Corrections:** review manuscript statements changed because formalization found an error or counterexample.
7. **AI boundary:** distinguish AI-assisted construction from Lean kernel checking and human mathematical interpretation.

## Repository layout

```text
BuildAll.lean                         # public aggregate entry point
PrimalitySheafVerification/
  BuildAll.lean                       # canonical aggregate importer
  Verification.lean                   # focused Paper 1 audit
  Spt1.lean … Spt7.lean               # Papers 1–7
  Mock1.lean
  Mock1_Advanced.lean                 # Paper 8 family
  Mock2.lean
  Mock2_Advanced.lean
  Mock2_FunctionalAnalysis.lean
  Mock2_FunctionalAnalysis_Integrated.lean  # Paper 9 family + integration
  QYM.lean
  Mock3.lean                          # Paper 10 family + integration
build-evidence/                       # preserved verification evidence
build-logs/                           # preserved build logs where applicable
CITATION.md                           # human-readable citation guidance
CITATION.cff                          # GitHub-readable citation metadata
```

## Citation

Machine-readable citation metadata is provided in [`CITATION.cff`](./CITATION.cff). The artifact version is `1.0.0`, and the canonical code URL is this repository with the frozen branch `frozen-pre-release-2026-08-24`. Cite the formalization artifact separately from the underlying manuscript bundle and from Mathlib itself.

## Discovery topics

Recommended GitHub topics for this repository are:

`lean4` · `mathlib` · `formal-mathematics` · `theorem-proving` · `formal-verification` · `ai-assisted-mathematics`

No Zulip or community announcement is required for the repository to remain public and independently inspectable.

## Release policy

A GitHub release should point to one exact artifact commit and should not be described more strongly than the corresponding Lean/build evidence supports. The intended public release identifier for this frozen artifact is **`v1.0.0`**.

## Attribution and license note

This repository contains a full Mathlib fork and therefore preserves Mathlib's existing license and attribution requirements. Project-authored formalization material should be distinguished from upstream Mathlib material when reused or cited.
