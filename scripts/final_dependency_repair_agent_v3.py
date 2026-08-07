from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parent))
import pass327_lean_repair_agent_v3 as patched

agent = patched.base
ROOT = Path(__file__).resolve().parents[1]
PRIORITY = ROOT / "build-logs" / "pass327-targets-pass.json"
MOCK1 = ROOT / "build-logs" / "mock1-family-pass.json"
STATE = ROOT / "build-logs" / "final-dependency-agent-state.json"
MARKER = ROOT / "build-logs" / "final-dependency-repair-pass.json"


def require_pass(path: Path) -> None:
    if not path.exists():
        raise RuntimeError(f"required marker missing: {path}")
    data = json.loads(path.read_text(encoding="utf-8"))
    if data.get("status") != "PASS":
        raise RuntimeError(f"required marker is not PASS: {path}: {data}")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("targets", nargs="+")
    parser.add_argument("--minutes", type=int, default=315)
    parser.add_argument("--rounds", type=int, default=24)
    args = parser.parse_args()
    require_pass(PRIORITY)
    require_pass(MOCK1)
    paths = [ROOT / item for item in args.targets]
    for path in paths:
        if not path.exists() or path.suffix != ".lean" or ROOT not in path.resolve().parents:
            raise RuntimeError(f"invalid final dependency target: {path}")
    agent.STATE_PATH = STATE
    agent.SUCCESS_PATH = MARKER
    state = agent.load_state()
    state["baseline"] = "post priority and Mock1 PASS gates"
    deadline = time.time() + args.minutes * 60
    for path in paths:
        if not agent.repair_target(path, state, args.rounds, deadline):
            agent.save_state(state)
            return 20
    results = []
    for path in paths:
        agent.audit_source(path)
        ok, result = agent.verify_twice(path, f"final-dependency-{path.stem}")
        results.append(result)
        if not ok:
            raise RuntimeError(f"final dependency verification failed: {path}: {result}")
    marker = {
        "status": "PASS",
        "targets": [str(path.relative_to(ROOT)) for path in paths],
        "results": results,
        "verified_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
    }
    MARKER.parent.mkdir(parents=True, exist_ok=True)
    MARKER.write_text(json.dumps(marker, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    state["phase"] = "FINAL_DEPENDENCY_REPAIR_COMPLETE"
    agent.save_state(state)
    agent.local_commit("fix: repair final clean-build dependency frontier", paths + [MARKER, STATE])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
