# Citation

This repository contains two things that should be cited separately when relevant:

1. the **Research Paper Formalization Audit** project authored by Lee Ga Hyun; and
2. **Mathlib**, the upstream mathematical library and infrastructure on which this fork-based preparation branch depends.

The underlying 10-manuscript source corpus is a third artifact and should be identified separately from the Lean formalization when it is directly discussed.

## Research Paper Formalization Audit

Until a standalone repository and verified release/tag are frozen, use a repository-style citation rather than describing this artifact as a peer-reviewed publication:

> Lee, Ga Hyun. *Research Paper Formalization Audit: AI-Assisted Lean 4/Mathlib Audit of Ten Mathematical Manuscript Sketches.* GitHub repository, 2026. Pre-release packaging branch `standalone-repo-prep-2026-08-24`.

Current code location:

<https://github.com/leegahuyn/mathlib4/tree/standalone-repo-prep-2026-08-24>

Machine-readable citation metadata is also provided in [`CITATION.cff`](./CITATION.cff).

### BibTeX

```bibtex
@software{lee2026research_paper_formalization_audit,
  author  = {Lee, Ga Hyun},
  title   = {Research Paper Formalization Audit: AI-Assisted Lean 4/Mathlib Audit of Ten Mathematical Manuscript Sketches},
  year    = {2026},
  url     = {https://github.com/leegahuyn/mathlib4/tree/standalone-repo-prep-2026-08-24},
  note    = {Pre-release packaging branch; cite an exact release/tag and commit SHA once a verified standalone release is frozen}
}
```

## Integrated 10-manuscript source bundle

The manuscript corpus audited by the project is available as a single **507-page** PDF bundle:

> Lee, Ga Hyun. *Integrated manuscript bundle: ten mathematical research manuscripts.* 2025–2026, 507 pages.

Google Drive access link:

<https://drive.google.com/file/d/1nmbfHF5Qkw8kFMwHn9CmnjWpGZuGKi2X/view>

The Master Evidence Index records the exact audited snapshot as:

- filename: `overleaf_bundle (Copy)(20260812-034123).pdf`
- physical pages: `507`
- size: `4,304,556 bytes`
- SHA-256: `12eb737301b3312dbad255f7b6d2f74c43c9ba27a2955157c134d36c9c0e53c5`

When exact reproducibility matters, identify the manuscript bundle by this SHA-256 rather than by a mutable cloud filename alone.

## Mathlib

This preparation branch remains a Mathlib fork. If you use or discuss Mathlib itself, please also cite the Mathlib project:

> The mathlib Community. *The Lean Mathematical Library.* CPP 2020.
> https://doi.org/10.1145/3372885.3373824

### Mathlib BibTeX

```bibtex
@inproceedings{mathlib2020,
  author    = {{The mathlib Community}},
  title     = {The {L}ean {M}athematical {L}ibrary},
  booktitle = {Proceedings of the 9th {ACM} {SIGPLAN} International Conference
               on Certified Programs and Proofs},
  series    = {CPP 2020},
  publisher = {ACM},
  address   = {New Orleans, LA, USA},
  year      = {2020},
  month     = jan,
  doi       = {10.1145/3372885.3373824},
  url       = {https://doi.org/10.1145/3372885.3373824}
}
```

## Citation boundary

A citation to this repository does **not** by itself assert that every manuscript claim has been proved. The project's `PROVED / CONDITIONAL / CERTIFICATE / INTERFACE / CORRECTED / NO-GO` labels and the exact Lean statements/build evidence determine the status of individual audited claims.
