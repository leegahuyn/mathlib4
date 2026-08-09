#!/usr/bin/env python3
from __future__ import annotations

import importlib.util
import os
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / "scripts" / "fa397_canonical_dependency_agent.py"

spec = importlib.util.spec_from_file_location("fa397", BASE)
if spec is None or spec.loader is None:
    raise RuntimeError("cannot load PASS 397 dependency-aware agent")
fa397 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(fa397)
fa391 = fa397.fa391

cycle = int(os.environ.get("FA398_CYCLE", "1"))
base_prompt = fa391.prompt_for


def cycle_prompt(path, metric, log, text):
    prompt = base_prompt(path, metric, log, text)
    previous = ROOT / "build-logs" / "fa391-targeted" / "AUTHORITATIVE_STATUS.txt"
    previous_text = previous.read_text(encoding="utf-8", errors="replace") if previous.exists() else "(none)"
    return (
        prompt
        + f"\n\nThis is autonomous repair cycle {cycle}. Previous compact status:\n"
        + "```text\n"
        + previous_text[-5000:]
        + "\n```\n"
        + "Do not repeat a previously ineffective edit. Prefer a different proof route, "
          "explicit local instance binding, or a directly verified current-Mathlib API."
    )


fa391.prompt_for = cycle_prompt

if __name__ == "__main__":
    raise SystemExit(fa391.main())
