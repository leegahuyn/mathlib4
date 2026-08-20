from __future__ import annotations

import fa420_select_verified_champion as base

for ref in (
    "origin/fix/fa420-evidence-controller-20260809",
    "origin/fix/fa421-name-body-controller-20260809",
    "origin/fix/fa422-canonical-decl-controller-20260809",
    "origin/fix/fa423-proof-hunk-controller-20260809",
):
    if ref not in base.CANDIDATE_REFS:
        base.CANDIDATE_REFS.insert(1, ref)
for path in (
    "build-logs/fa423-proof-hunk/CURRENT.json",
    "build-logs/fa422-canonical-decl/CURRENT.json",
    "build-logs/fa421-name-body/CURRENT.json",
    "build-logs/fa420-evidence-controller/CURRENT.json",
):
    if path not in base.KNOWN_EVIDENCE_PATHS:
        base.KNOWN_EVIDENCE_PATHS.insert(0, path)

if __name__ == "__main__":
    raise SystemExit(base.main())
