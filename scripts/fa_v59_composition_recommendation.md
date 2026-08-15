# v59 fail-closed cross-manifest composition recommendation

## Outcome

The finalized Fourier, weighted, weighted-idx4018, and reduced-chart packages normalize to seven independently selectable owner-local groups:

`F3930, F3933, F3939, W4017, W4018P1, W4019, R4198`.

Static composition passes for the bounded six-variant matrix below. Every candidate has exactly 4,416 declarations in the authority declaration order; all raw declaration headers, comments, and attributes are identical; all six executable trust-token counts remain zero; and both the raw `maxHeartbeats` token count and the `set_option maxHeartbeats` count remain eight. No heartbeat option, source move, declaration, header, comment, attribute, import, or trust escape was added.

This is not a Lean result. `W4018P1`, `W4017`, and `R4198` remain staged, every candidate is direct-Lean-unverified, and no clean-build or promotion claim is made.

## Canonical authority lock

The canonical equality object is run `31803223990`, head `14e3e3f5e85f3c3ca7a1381eb88522552ffe29dc`, branch `codex/fa-exclusive-focus-20260814`, artifact `9220688452` named `codex-fa-v58-core_base-highcap2000-14e3e3f5e85f3c3ca7a1381eb88522552ffe29dc`, artifact digest `sha256:269100960a5e7ecd8b35e39cdde2c774f244b49c269e992aec00203bd2288ab4`, and source SHA `013f64cf5eaaab544629ad02fc2e33e63f90916e9b1e1581d73f2af2e7ba34ba`.

The artifact's embedded `authority.json` and `METRIC.json.authority` describe older artifacts. They are historical payload metadata, not the v59 authority projection. Consumers must require exact equality with the current canonical object in the JSON outputs and must not accept those embedded historical objects as substitutes.

## Bounded direct-replay matrix

| Order | Variant | Exact group selection | Candidate SHA256 | Bytes | Lines | Risk isolated |
|---:|---|---|---|---:|---:|---|
| 1 | `M_promoted_without_idx3933` | `F3930,F3939,W4019` | `c3311de418db700651ca9fd9b0e34f069c11e47e4eaa8171768fa722d8bc0c2a` | 2,807,131 | 62,813 | Promoted-static minimum without idx3933; intentionally weighted-causal-incomplete |
| 2 | `F_fourier_full` | `F3930,F3933,F3939` | `25f1b28103e99dc3b7c70457d9ade2f137063c100878e73fd9bb3c50e8ff9b44` | 2,807,136 | 62,814 | Full Fourier cluster only |
| 3 | `W_weighted_structural` | `W4017,W4018P1,W4019` | `aae300cb43942895c02be3ca4da3a85276ef70c8af7fd8eec543be35a120810c` | 2,807,262 | 62,818 | Weighted producer chain in source order |
| 4 | `R_reduced_inline_isolated` | `R4198` | `5a231db840bc576a365fa3f9cd9aeaccab5ec98683834edb20d41e4ec5eaf5eb` | 2,812,354 | 62,931 | Reduced-chart inline body only |
| 5 | `A_all` | `F3930,F3933,F3939,W4017,W4018P1,W4019,R4198` | `dedbf67b514b3838c743c3eabe2bdf6b5482cdfd232556fc9acc4ab0138b68f8` | 2,812,426 | 62,933 | Complete minimal-P01 root set |
| 6 | `A_no_idx3933` | `F3930,F3939,W4017,W4018P1,W4019,R4198` | `84e0a7843de9bcf99a25e51db95d48e9d5feceffe4e1b94f315b11d166792e5a` | 2,812,433 | 62,933 | Exact A/B control differing from `A_all` only at idx3933 |

The full repair-ID lists and declaration-index order are machine-locked in `variant-matrix.json`. Each variant must be rematerialized from the authority source, not layered on another candidate.

## Weighted causal boundary

Collector ownership is not causal ownership at the two command boundaries:

- Ordinal 4 is raw-assigned to idx4016 at `55483:0`, but that line opens idx4017's command comment. Its normalized repair owner is idx4017 (`W4017`).
- Ordinal 5 is raw-assigned to idx4017 at `55545:0`, but that line opens idx4018's command comment, and the log reaches idx4018 body location `55554:13`. Its normalized producer owner is idx4018 (`W4018P1`).
- Ordinal 6 is the separate idx4019 owner-local `norm_neg _` repair (`W4019`). Ordinal 7 is the missing-idx4018 cascade, and ordinals 8-9 are downstream idx4020 cascades. Neither idx4020 nor any declaration order is changed.

The final idx4018 locks are P01 manifest SHA `5674c746d28595cfaa492f7b116e4ee685f0b225bd2e50faf09c8f461970f5c9` and result-index SHA `5c80df46f3f4dee2a17298a9e3d4fabc4cda12585ea01b04e181ea8b5c369b3a`. P01 is the preferred first staged probe. P02 and P03 are serial cumulative fallbacks only and are excluded from this first six-way matrix.

## Promotion boundary

Use `A_all` as the preferred full candidate and `A_no_idx3933` as its exact idx3933 negative control. Promotion requires a direct Lean replay at the default heartbeat budget with the expected candidate SHA, real kernel declarations for idx4017 through idx4019, no replacement owner diagnostic, no synthetic declaration-uses-sorry warning, and a newly audited diagnostic inventory. If P01 fails, capture its first exact local diagnostic before considering P02; do not add a heartbeat option.

The prior `P`, `PW`, `PR`, `PWR`, `PWI`, and `PWRI` hashes remain preserved as non-matrix compatibility locks in `variant-matrix.json`; they do not expand the recommended six-run matrix.

## Machine-readable locks

- `normalized-repair-groups.json`: canonical seven-group normalization and fragment-source locks.
- `variant-matrix.json`: exact six selections, repair IDs, source order, candidate SHA/bytes/lines, and compatibility locks.
- `cross-manifest-static-audit.json`: artifact and package identity, 10-error conservation, owner/fragment overlap, causal boundary, header/comment/attribute/trust, heartbeat, and final materialization audits.
- `HASHES.sha256`: output integrity inventory; it intentionally does not self-hash.
