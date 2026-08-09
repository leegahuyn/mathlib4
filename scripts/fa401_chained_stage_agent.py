#!/usr/bin/env python3
from __future__ import annotations

import importlib.util
import json
import os
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / "scripts" / "fa400_resilient_harvest_agent.py"
CHAIN = ROOT / "build-logs" / "fa401-chain"
MARKER = ROOT / "build-logs" / "fa391-targeted" / "ALL_REQUIRED_TARGETS_2X_PASS"
STATUS = ROOT / "build-logs" / "fa391-targeted" / "AUTHORITATIVE_STATUS.json"

spec = importlib.util.spec_from_file_location("fa400", BASE)
if spec is None or spec.loader is None:
    raise RuntimeError("cannot load PASS 400 resilient agent")
fa400 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(fa400)
fa399 = fa400.fa399
fa391 = fa400.fa391

stage = int(os.environ.get("FA401_STAGE", "1"))


def completed_status_is_valid() -> bool:
    if not MARKER.exists() or not STATUS.exists():
        return False
    try:
        data = json.loads(STATUS.read_text(encoding="utf-8"))
    except Exception:
        return False
    if data.get("complete") is not True or data.get("stage") != "complete":
        return False
    modules = data.get("modules", [])
    audits = data.get("forbidden_token_audit", {})
    return bool(modules) and all(m.get("status") == "PASS_2X" for m in modules) and bool(audits) and all(
        not any(v.values()) for v in audits.values()
    )


def main() -> int:
    CHAIN.mkdir(parents=True, exist_ok=True)
    if completed_status_is_valid():
        (CHAIN / f"stage-{stage:02d}.json").write_text(
            json.dumps({"stage": stage, "complete_at_start": True}, indent=2) + "\n",
            encoding="utf-8",
        )
        print(f"PASS 401 stage {stage}: prior complete marker valid; final independent verifier will recheck")
        return 0

    harvest = fa400.harvest_all()
    current_sha = fa391.sha(fa399.TARGET)
    last_sha_file = CHAIN / "LAST_COMBINATOR_SOURCE_SHA256"
    last_sha = last_sha_file.read_text(encoding="utf-8").strip() if last_sha_file.exists() else ""
    selected_metric = harvest.get("selected_metric", {})
    first_line = int(selected_metric.get("first_line", 0) or 0)
    should_combine = current_sha != last_sha and (stage == 1 or 0 < first_line <= 22000)
    if should_combine:
        combinator = fa399.deterministic_instance_search()
        last_sha_file.write_text(current_sha + "\n", encoding="utf-8")
    else:
        combinator = {
            "skipped": True,
            "reason": "same source already tested or frontier beyond instance cluster",
            "source_sha256": current_sha,
            "first_line": first_line,
        }
    stage_status = {
        "stage": stage,
        "harvest": harvest,
        "combinator": combinator,
        "source_sha256_before_model": fa391.sha(fa399.TARGET),
    }
    (CHAIN / f"stage-{stage:02d}.json").write_text(
        json.dumps(stage_status, indent=2) + "\n", encoding="utf-8"
    )
    (CHAIN / "CURRENT.json").write_text(json.dumps(stage_status, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(stage_status, indent=2))
    return fa391.main()


if __name__ == "__main__":
    raise SystemExit(main())
