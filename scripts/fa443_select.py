from __future__ import annotations

import json
import os
import shutil
import sys
from pathlib import Path
from typing import Any

from fa442_pipeline_common import FA_PATH, REPO, audit_clean, read_json, sha256_file, write_json

METRICS_ROOT = Path(os.environ.get(
    "FA443_METRICS_ROOT",
    REPO / "build-logs/fa443-blocker-tournament/direct-metrics",
))
OUT = REPO / "build-logs/fa443-blocker-tournament/selection"
CURRENT_BASELINE_SHA = os.environ["CURRENT_BASELINE_SHA"]


def first(metric: dict[str, Any]) -> dict[str, Any]:
    return metric.get("fa", {}).get("first_error", {})


def integrity(metric: dict[str, Any]) -> bool:
    source = metric.get("source", {})
    return bool(
        source.get("sha_identity_ok") and source.get("same_height") and
        source.get("header_unchanged") and source.get("declaration_sequence_unchanged") and
        source.get("trust_audit_clean") and audit_clean(source.get("trust_audit", {}))
    )


def prerequisites(metric: dict[str, Any]) -> bool:
    rows = metric.get("prerequisites", {})
    for key in ("Mock2", "Mock2_Advanced"):
        row = rows.get(key, {})
        if not (row.get("exit_code") == 0 and row.get("olean_exists") and row.get("ilean_exists")):
            return False
    return True


def valid(metric: dict[str, Any]) -> bool:
    if metric.get("classification") == "INFRA_FAILURE":
        return False
    if not metric.get("direct_lean_executed") or not integrity(metric) or not prerequisites(metric):
        return False
    fa = metric.get("fa", {})
    if not isinstance(fa.get("exit_code"), int):
        return False
    if fa["exit_code"] != 0 and first(metric).get("line", 0) <= 0:
        return False
    return True


def score(metric: dict[str, Any]) -> tuple[int, int, int, int]:
    fa = metric["fa"]
    if fa["exit_code"] == 0:
        return (1, 10**9, 10**9, 10**9)
    e = first(metric)
    return (0, int(e.get("declaration_index", -1)), int(e.get("line", 0)), int(e.get("column", 0)))


def strictly_better(candidate: dict[str, Any], baseline: dict[str, Any]) -> bool:
    cfa, bfa = candidate["fa"], baseline["fa"]
    if cfa["exit_code"] == 0:
        return bfa["exit_code"] != 0 or candidate["source"]["sha256"] != baseline["source"]["sha256"]
    if bfa["exit_code"] == 0:
        return False
    ce, be = first(candidate), first(baseline)
    if ce.get("declaration_index", -1) != be.get("declaration_index", -1):
        return ce.get("declaration_index", -1) > be.get("declaration_index", -1)
    if ce.get("declaration") != be.get("declaration"):
        return False
    if ce.get("line", 0) != be.get("line", 0):
        return ce.get("line", 0) > be.get("line", 0)
    return ce.get("column", 0) > be.get("column", 0)


def row(metric: dict[str, Any]) -> dict[str, Any]:
    e = first(metric)
    return {
        "variant": metric.get("variant"),
        "sha256": metric.get("source", {}).get("sha256", ""),
        "Lean_executed": metric.get("direct_lean_executed", False),
        "exit": metric.get("fa", {}).get("exit_code", ""),
        "first_line": e.get("line", 0),
        "first_col": e.get("column", 0),
        "declaration": e.get("declaration", ""),
        "declaration_index": e.get("declaration_index", -1),
        "classification": metric.get("classification", "INFRA_FAILURE"),
    }


def main() -> None:
    if OUT.exists():
        shutil.rmtree(OUT)
    OUT.mkdir(parents=True)
    pairs = [(p, read_json(p)) for p in sorted(METRICS_ROOT.rglob("metric.json"))]
    if not pairs:
        raise RuntimeError("INFRA_FAILURE: no FA443 direct metrics found")
    baselines = [(p, m) for p, m in pairs if m.get("is_baseline")]
    if len(baselines) != 1:
        raise RuntimeError(f"INFRA_FAILURE: expected one FA443 baseline metric, found {len(baselines)}")
    baseline_path, baseline = baselines[0]
    if baseline.get("source", {}).get("sha256") != CURRENT_BASELINE_SHA:
        raise RuntimeError("INFRA_FAILURE: FA443 baseline metric SHA mismatch")
    if not valid(baseline):
        raise RuntimeError("INFRA_FAILURE: FA443 baseline did not produce a valid direct metric")
    infra = [(p, m) for p, m in pairs if m.get("classification") == "INFRA_FAILURE"]
    if infra:
        raise RuntimeError(
            f"INFRA_FAILURE: {len(infra)} FA443 candidates did not execute valid direct Lean metrics"
        )
    valid_pairs = [(p, m) for p, m in pairs if valid(m)]
    best_path, best = max(valid_pairs, key=lambda x: score(x[1]))
    strict = strictly_better(best, baseline)
    selected_path, selected = (best_path, best) if strict else (baseline_path, baseline)
    source_path = selected_path.parent / "source.lean"
    selected_sha = selected["source"]["sha256"]
    if sha256_file(source_path) != selected_sha:
        raise RuntimeError("INFRA_FAILURE: selected FA443 source/metric SHA mismatch")
    shutil.copy2(source_path, FA_PATH)
    worktree_sha = sha256_file(FA_PATH)
    if worktree_sha != selected_sha:
        raise RuntimeError("INFRA_FAILURE: FA443 materialized worktree SHA mismatch")

    be, se = first(baseline), first(selected)
    if selected["fa"]["exit_code"] == 0:
        classification = "FA_PASS_CANDIDATE"
        advance = "FA_PASS_CANDIDATE"
    elif strict and se.get("declaration_index", -1) > be.get("declaration_index", -1):
        classification = "STRICT_PROMOTION"
        advance = "DECLARATION_BREAKTHROUGH"
    elif strict:
        classification = "STRICT_PROMOTION"
        advance = "SMALL_SAME_DECLARATION_ADVANCE"
    else:
        classification = "NO_IMPROVEMENT"
        advance = "NO_IMPROVEMENT"

    rows = [row(m) for _, m in pairs]
    report = {
        "classification": classification,
        "advance_classification": advance,
        "strict_promotion": strict,
        "current_baseline": row(baseline),
        "selected": row(selected),
        "selected_slug": selected.get("slug"),
        "selected_source_sha256": selected_sha,
        "selected_artifact_sha256": sha256_file(source_path),
        "worktree_sha256": worktree_sha,
        "identity_ok_before_commit": selected_sha == sha256_file(source_path) == worktree_sha,
        "candidate_count": len(pairs),
        "candidate_results": rows,
        "promotion_rule": [
            "exit 0",
            "later declaration index",
            "same declaration and same-height source: later line/column",
        ],
    }
    write_json(OUT / "selection.json", report)
    table = [
        "variant | SHA256 | Lean executed? | exit | first line:col | declaration | classification",
        "--- | --- | --- | --- | --- | --- | ---",
    ]
    for x in rows:
        table.append(
            f"{x['variant']} | `{x['sha256']}` | {str(x['Lean_executed']).lower()} | "
            f"{x['exit']} | {x['first_line']}:{x['first_col']} | `{x['declaration']}` | "
            f"{x['classification']}"
        )
    (OUT / "candidate-results.md").write_text("\n".join(table) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2, ensure_ascii=False))
    output = os.environ.get("GITHUB_OUTPUT")
    if output:
        with open(output, "a", encoding="utf-8") as f:
            f.write(f"classification={classification}\n")
            f.write(f"advance_classification={advance}\n")
            f.write(f"strict_promotion={str(strict).lower()}\n")
            f.write(f"selected_sha={selected_sha}\n")
            f.write(f"selected_exit={selected['fa']['exit_code']}\n")
            f.write(f"selected_first_line={se.get('line', 0)}\n")
            f.write(f"selected_first_col={se.get('column', 0)}\n")
            f.write(f"selected_declaration={se.get('declaration', '')}\n")


if __name__ == "__main__":
    try:
        main()
    except Exception as exc:
        OUT.mkdir(parents=True, exist_ok=True)
        write_json(OUT / "INFRA_FAILURE.json", {
            "classification": "INFRA_FAILURE",
            "error": repr(exc),
        })
        raise
