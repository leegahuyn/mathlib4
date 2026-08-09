from __future__ import annotations

import importlib.util
import json
from pathlib import Path

BASE = Path(__file__).with_name("pass389_beam_repair_agent.py")
spec = importlib.util.spec_from_file_location("pass389_beam_base_v2", BASE)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load {BASE}")
beam = importlib.util.module_from_spec(spec)
spec.loader.exec_module(beam)

original_download = beam.agent.download_pass389_candidate


def resume_or_download(target: Path) -> dict:
    state_path = beam.agent.STATE
    if state_path.exists() and target.exists() and target.stat().st_size > 100000:
        try:
            state = json.loads(state_path.read_text(encoding="utf-8"))
        except Exception:
            state = {}
        if state.get("baseline") == "PASS 389":
            return {
                "mode": "checked-in-beam-source",
                "candidate_sha256": beam.agent.sha256_file(target),
                "prior_status": state.get("status"),
            }
    return original_download(target)


beam.agent.download_pass389_candidate = resume_or_download
raise SystemExit(beam.main())
