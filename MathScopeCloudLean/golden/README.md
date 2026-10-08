# Restricted Golden algebra verifier

The complete Lean source proves only exact polynomial identities under stated
algebraic assumptions. See the source docstring and `golden-manifest.json` for
the explicit scope. A torus Laplacian, function space, analytic derivative,
existence, uniqueness, spectrum, topology and index are not formalized here.
C-014 is independent and its existing endpoint is unchanged.

`GET /v1/golden/meta` returns the bundled source, exact SHA-256, pinned Lean
toolchain and actual runtime/environment fingerprint. The manifest byte hash
is the dependency lock fingerprint; this source needs Lean core only.

`POST /v1/verify/golden` accepts exactly `claimId`, `sourceHash`, and the boolean
`semanticReviewed`. It starts a new Lean process for every accepted request,
inside the fixed `golden` directory, on `GoldenAlgebra.lean`. It does not accept
user-supplied code, paths, executables, environment settings or proof receipts.
Requests share the existing serial verifier queue. Execution has a90-second
timeout and bounded output. Each of the three theorem axiom lists must contain
exactly `propext`, `Classical.choice` and `Quot.sound`; no `sorryAx` is allowed.

The response is formal only after successful fresh compilation and axiom audit.
Semantic review permits `PROVED` for this exact scoped claim; it does not extend
the theorem to a PDE claim. `proofHash` is SHA-256 of compact UTF-8 JSON in this
key order: `{sourceHash,environmentHash,axiomAuditOutput}`. IDs and timestamps
change across replay; the hash stays stable in the same source/environment.
Clients must trust a configured HTTPS verifier and pin source, environment,
dependency lock, toolchain, scope and deployment; an imported JSON response is
not proof of a fresh verifier call.

Run `npm run test:golden` with Lean4.34.0-rc2 installed. Tests include fresh real
compilations and the HTTP wire boundary, in addition to failed/admitted proof
and malformed-input rejection. The CI workflow uses the same pinned Lean core.
