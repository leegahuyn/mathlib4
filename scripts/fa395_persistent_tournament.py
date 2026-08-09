#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import sys
import urllib.request

ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "fa394_tournament_solver.py"
spec = importlib.util.spec_from_file_location("fa394_persistent_helper", SCRIPT)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot import {SCRIPT}")
M = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = M
spec.loader.exec_module(M)

PVS = ROOT / "PrimalitySheafVerification"
EVIDENCE = ROOT / "build-logs" / "fa395-persistent"
STATE = EVIDENCE / "STATE.json"
NEXT = EVIDENCE / "NEXT_ACTION.json"
FINAL = EVIDENCE / "FINAL_STATUS.json"
MARKER = EVIDENCE / "ALL_REQUIRED_TARGETS_2X_PASS"

PREFERRED_MODELS = [
    "openai/gpt-5",
    "openai/gpt-5-mini",
    "openai/o3",
    "openai/o4-mini",
    "openai/gpt-4.1",
    "openai/gpt-4.1-mini",
    "xai/grok-3-mini",
    "deepseek/DeepSeek-V3-0324",
    "mistral-ai/Mistral-Large-2411",
    "qwen/Qwen3-235B-A22B",
]


def load_json(path: Path, default: dict) -> dict:
    if not path.exists():
        return dict(default)
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
        return value if isinstance(value, dict) else dict(default)
    except Exception:
        return dict(default)


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def target_paths() -> list[Path]:
    return [
        PVS / "Mock2_FunctionalAnalysis.lean",
        PVS / "Mock2_FunctionalAnalysis_Integrated.lean",
        *sorted(PVS.glob("Mock3*.lean")),
        PVS / "QYM.lean",
    ]


def source_hashes() -> dict[str, str]:
    return {
        str(path.relative_to(ROOT)): sha(path)
        for path in target_paths()
        if path.exists()
    }


def catalog_models(token: str) -> tuple[list[str], dict]:
    request = urllib.request.Request(
        "https://models.github.ai/catalog/models",
        headers={
            "Authorization": f"Bearer {token}",
            "Accept": "application/vnd.github+json",
            "X-GitHub-Api-Version": "2022-11-28",
        },
    )
    record: dict = {"source": "fallback", "ids": []}
    available: list[str] = []
    try:
        with urllib.request.urlopen(request, timeout=90) as response:
            payload = json.loads(response.read().decode())
        entries = payload if isinstance(payload, list) else payload.get("models", [])
        for entry in entries:
            if not isinstance(entry, dict):
                continue
            model_id = entry.get("id") or entry.get("name")
            task = str(entry.get("task", "")).lower()
            if model_id and (not task or "chat" in task or "completion" in task):
                available.append(str(model_id))
        record = {"source": "catalog", "ids": available}
    except Exception as exc:
        record = {"source": "fallback", "error": repr(exc), "ids": []}

    ordered = [model for model in PREFERRED_MODELS if model in available]
    for model in available:
        if model not in ordered:
            ordered.append(model)
    if not ordered:
        ordered = list(PREFERRED_MODELS)
    return ordered, record


def choose_models(all_models: list[str], cycle: int, strategy: int) -> list[str]:
    if len(all_models) <= 4:
        return all_models
    start = (cycle * 3 + strategy) % len(all_models)
    rotated = all_models[start:] + all_models[:start]
    chosen: list[str] = []
    publishers: set[str] = set()
    for model in rotated:
        publisher = model.split("/", 1)[0]
        if publisher not in publishers or len(chosen) >= 2:
            chosen.append(model)
            publishers.add(publisher)
        if len(chosen) == 4:
            break
    return chosen


def fetch_tournament_candidates(cycle: int) -> dict[str, str]:
    candidates: dict[str, str] = {}
    if cycle not in {0, 1} and cycle % 4 != 0:
        return candidates
    branches = {
        "pass391": "fix/fa391-final-gate-20260809",
        "pass392": "fix/fa392-iterative-solver-20260809",
        "pass393v2": "fix/fa393-v2-declaration-replacement-20260809",
        "pass394": "fix/fa394-tournament-20260809",
        "pr9": "ci/fa319-isolated-20260807",
    }
    for label, branch in branches.items():
        source = M.fetch_branch_source(branch, f"fa395-{cycle}-{label}")
        if source is not None:
            candidates[label] = source
    return candidates


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-cycles", type=int, default=16)
    parser.add_argument("--max-errors", type=int, default=220)
    args = parser.parse_args()

    token = os.environ.get("GITHUB_TOKEN", "")
    if not token:
        raise SystemExit("GITHUB_TOKEN is required")
    EVIDENCE.mkdir(parents=True, exist_ok=True)
    state = load_json(
        STATE,
        {
            "cycle": 0,
            "strategy": 0,
            "no_source_progress": 0,
            "history": [],
        },
    )
    cycle = int(state.get("cycle", 0))
    strategy = int(state.get("strategy", 0))
    if cycle >= args.max_cycles:
        NEXT.write_text(json.dumps({"dispatch": False, "reason": "max_cycles"}, indent=2))
        return 2

    before = source_hashes()
    all_models, catalog = catalog_models(token)
    models = choose_models(all_models, cycle, strategy)
    (EVIDENCE / f"cycle-{cycle:03d}-model-catalog.json").write_text(
        json.dumps({"catalog": catalog, "selected": models}, indent=2),
        encoding="utf-8",
    )

    fa = PVS / "Mock2_FunctionalAnalysis.lean"
    M.EVIDENCE = EVIDENCE / f"cycle-{cycle:03d}"
    tournament_sources = fetch_tournament_candidates(cycle)
    _, selected_metric, selected_label = M.select_best_baseline(
        fa,
        M.EVIDENCE / "tournament",
        tournament_sources,
        max_errors=args.max_errors,
    )

    fa_round_schedule = [2, 3, 4, 3, 5, 4]
    downstream_round_schedule = [4, 5, 6, 7, 6, 8]
    candidate_schedule = [3, 4, 4, 5, 5, 6]
    slot = strategy % len(fa_round_schedule)
    summary = M.verify_ordered(
        token,
        models,
        fa_rounds=fa_round_schedule[slot],
        downstream_rounds=downstream_round_schedule[slot],
        max_candidates=candidate_schedule[slot],
        max_errors=args.max_errors,
    )
    summary["cycle"] = cycle
    summary["strategy"] = strategy
    summary["models"] = models
    summary["tournament_selected"] = selected_label
    summary["tournament_selected_metric"] = selected_metric.to_json()

    after = source_hashes()
    source_changed = before != after
    complete = bool(summary.get("complete"))
    if complete:
        summary["status"] = "SUCCESS_ALL_REQUIRED_TARGETS_2X_PASS"
        MARKER.write_text("SUCCESS_ALL_REQUIRED_TARGETS_2X_PASS\n", encoding="utf-8")

    no_progress = int(state.get("no_source_progress", 0))
    if source_changed:
        no_progress = 0
    else:
        no_progress += 1
    history = list(state.get("history", []))
    history.append(
        {
            "cycle": cycle,
            "strategy": strategy,
            "selected": selected_label,
            "selected_metric": selected_metric.to_json(),
            "source_changed": source_changed,
            "complete": complete,
            "stage": summary.get("stage"),
            "reason": summary.get("reason"),
            "models": models,
            "before": before,
            "after": after,
        }
    )
    history = history[-40:]
    next_state = {
        "cycle": cycle + 1,
        "strategy": strategy + 1,
        "no_source_progress": no_progress,
        "history": history,
    }
    STATE.write_text(json.dumps(next_state, indent=2), encoding="utf-8")
    FINAL.write_text(json.dumps(summary, indent=2), encoding="utf-8")

    dispatch = not complete and cycle + 1 < args.max_cycles
    NEXT.write_text(
        json.dumps(
            {
                "dispatch": dispatch,
                "complete": complete,
                "next_cycle": cycle + 1,
                "source_changed": source_changed,
                "no_source_progress": no_progress,
                "stage": summary.get("stage"),
                "reason": summary.get("reason"),
            },
            indent=2,
        ),
        encoding="utf-8",
    )
    print(json.dumps(summary, indent=2))
    return 0 if complete else 2


if __name__ == "__main__":
    raise SystemExit(main())
