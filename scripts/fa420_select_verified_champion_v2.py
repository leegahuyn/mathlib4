from __future__ import annotations

import fa420_select_verified_champion as base

controller_ref = "origin/fix/fa420-evidence-controller-20260809"
controller_evidence = "build-logs/fa420-evidence-controller/CURRENT.json"
if controller_ref not in base.CANDIDATE_REFS:
    base.CANDIDATE_REFS.insert(1, controller_ref)
if controller_evidence not in base.KNOWN_EVIDENCE_PATHS:
    base.KNOWN_EVIDENCE_PATHS.insert(0, controller_evidence)

if __name__ == "__main__":
    raise SystemExit(base.main())
