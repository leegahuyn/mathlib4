from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parent))
import pass327_lean_repair_agent_v2 as patched

agent = patched.base
ROOT = Path(__file__).resolve().parents[1]
PRIORITY_MARKER = ROOT / "build-logs" / "pass327-targets-pass.json"
STATE = ROOT / "build-logs" / "post-priority-agent-state.json"
MOCK1_MARKER = ROOT / "build-logs" / "mock1-family-pass.json"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--targets", nargs="*", default=[])
    parser.add_argument("--minutes", type=int, default=315)
    parser.add_argument("--rounds", type=int, default=24)
    args = parser.parse_args()
    if not PRIORITY_MARKER.exists():
        raise RuntimeError("PASS 327 priority marker is required before Mock1 repair")
    prior = json.loads(PRIORITY_MARKER.read_text(encoding="utf-8"))
    if prior.get("status") != "PASS":
        raise RuntimeError(f"priority marker is not PASS: {prior}")

    agent.STATE_PATH = STATE
    agent.SUCCESS_PATH = MOCK1_MARKER
    state = agent.load_state()
    state["baseline"] = "post PASS-327 priority gate"
    deadline = time.time() + args.minutes * 60
    targets = (
        [ROOT / item for item in args.targets]
        if args.targets
        else [
            ROOT / "PrimalitySheafVerification" / "Mock1.lean",
            ROOT / "PrimalitySheafVerification" / "Mock1_Advanced.lean",
        ]
    )
    targets = [path for path in targets if path.exists()]
    if not targets:
        raise RuntimeError("no Mock1-family targets were found")

    for path in targets:
        if not agent.repair_target(path, state, args.rounds, deadline):
            agent.save_state(state)
            print(json.dumps({"status": "CHECKPOINT", "state": state}, ensure_ascii=False))
            return 20

    results = []
    for path in targets:
        agent.audit_source(path)
        ok, result = agent.verify_twice(path, f"post-priority-final-{path.stem}")
        results.append(result)
        if not ok:
            raise RuntimeError(f"two-pass verification failed for {path}: {result}")
    marker = {
        "status": "PASS",
        "priority_baseline": prior.get("verified_utc"),
        "targets": [str(path.relative_to(ROOT)) for path in targets],
        "results": results,
        "verified_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
    }
    MOCK1_MARKER.parent.mkdir(parents=True, exist_ok=True)
    MOCK1_MARKER.write_text(json.dumps(marker, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    state["phase"] = "MOCK1_FAMILY_COMPLETE"
    state["completed_utc"] = marker["verified_utc"]
    agent.save_state(state)
    agent.local_commit(
        "fix: verify Mock1 family after PASS 327 priority gate",
        targets + [MOCK1_MARKER, STATE],
    )
    print(json.dumps({"status": "PASS", "marker": marker}, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
