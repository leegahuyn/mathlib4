#!/usr/bin/env python3
"""Compatibility proof-body stage for the PASS 403 hybrid solver.

This module intentionally keeps the checked-in Lean source unchanged unless a later
solver accepts a kernel-checked improvement.  It supplies the interface expected by
``fa403_hybrid_continue.py`` and returns the current robust compiler metric so the
extended-frontier stage can continue from the real first error.
"""
from __future__ import annotations

import importlib.util
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
HELPER = ROOT / "scripts" / "fa394_tournament_solver.py"
spec = importlib.util.spec_from_file_location("fa394_helper_for_fa396_compat", HELPER)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot import {HELPER}")
M = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = M
spec.loader.exec_module(M)

PREFERRED_MODELS = [
    "openai/gpt-5",
    "openai/gpt-5-mini",
    "openai/o3",
    "openai/o4-mini",
    "openai/gpt-4.1",
    "xai/grok-3-mini",
    "deepseek/DeepSeek-V3-0324",
    "mistral-ai/Mistral-Large-2411",
    "qwen/Qwen3-235B-A22B",
]


def catalog_models(token: str) -> list[str]:
    fn = getattr(M, "catalog_models", None)
    if callable(fn):
        try:
            models = list(fn(token))
            if models:
                return models
        except Exception:
            pass
    return list(PREFERRED_MODELS)


def choose_models(models: list[str], cycle: int) -> list[str]:
    if not models:
        return list(PREFERRED_MODELS[:4])
    start = (max(0, cycle) * 4) % len(models)
    rotated = models[start:] + models[:start]
    return rotated[: min(4, len(rotated))]


def repair_body(
    path: Path,
    evidence: Path,
    token: str,
    models: list[str],
    *,
    rounds: int,
    max_candidates: int,
    max_errors: int,
):
    del token, models, rounds, max_candidates
    evidence.mkdir(parents=True, exist_ok=True)
    source = path.read_text(encoding="utf-8")
    lean_metric = M.H.compile_file(
        path,
        evidence / "compat-baseline.log",
        max_errors=max_errors,
        timeout=1800,
    )
    metric = M.robust_metric(source, lean_metric)
    (evidence / "compat-status.json").write_text(
        json.dumps(metric.to_json(), indent=2), encoding="utf-8"
    )
    return metric
