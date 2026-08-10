from __future__ import annotations

import json
import os
import shutil
import sys
from pathlib import Path
from typing import Any

from fa442_pipeline_common import (
    BASELINE_LINE_COUNT,
    BASELINE_SHA256,
    FA_PATH,
    REPO,
    append_github_output,
    audit_clean,
    read_json,
    sha256_file,
    write_json,
)

METRICS_ROOT = Path(os.environ.get(
    "METRICS_ROOT",
    REPO / "build-logs/fa442-pipeline-repair/selector-download",
))
PREP_ROOT = Path(os.environ.get(
    "PREP_ROOT",
    REPO / "build-logs/fa442-pipeline-repair/prep-selector-download",
))
OUT = REPO / "build-logs/fa442-pipeline-repair/selection"


def fa(metric: dict[str, Any]) -> dict[str, Any]:
    return metric.get("fa", {})


def first(metric: dict[str, Any]) -> dict[str, Any]:
    return fa(metric).get("first_error", {})


def prereq_clean(metric: dict[str, Any]) -> bool:
    prereq = metric.get("prerequisites", {})
    for name in ("Mock2", "Mock2_Advanced"):
        row = prereq.get(name, {})
        if not (
            row.get("exit_code") == 0 and row.get("olean_exists") and row.get("ilean_exists")
        ):
            return False
    return True


def integrity_clean(metric: dict[str, Any]) -> bool:
    source = metric.get("source", {})
    return bool(
        source.get("sha_identity_ok") and
        source.get("line_count") == BASELINE_LINE_COUNT and
        source.get("line_count_ok") and
        source.get("blocker_header_unchanged") and
        source.get("declaration_sequence_unchanged") and
        source.get("trust_audit_clean") and
        audit_clean(source.get("trust_audit", {}))
    )


def valid_direct_metric(metric: dict[str, Any]) -> bool:
    if metric.get("classification") == "INFRA_FAILURE":
        return False
    if not metric.get("direct_lean_executed"):
        return False
    if not prereq_clean(metric) or not integrity_clean(metric):
        return False
    row = fa(metric)
    if not isinstance(row.get("exit_code"), int):
        return False
    if row["exit_code"] != 0 and first(metric).get("line", 0) <= 0:
        return False
    return True


def better(candidate: dict[str, Any], baseline: dict[str, Any]) -> bool:
    cfa, bfa = fa(candidate), fa(baseline)
    if cfa.get("exit_code") == 0:
        return bfa.get("exit_code") != 0 or candidate["source"]["sha256"] != baseline["source"]["sha256"]
    if bfa.get("exit_code") == 0:
        return False
    cf, bf = first(candidate), first(baseline)
    c_index, b_index = cf.get("declaration_index", -1), bf.get("declaration_index", -1)
    if c_index != b_index:
        return c_index > b_index
    if cf.get("declaration") != bf.get("declaration"):
        return False
    c_line, b_line = cf.get("line", 0), bf.get("line", 0)
    if c_line != b_line:
        return c_line > b_line
    return cf.get("column", 0) > bf.get("column", 0)


def score(metric: dict[str, Any]) -> tuple[int, int, int, int]:
    row = fa(metric)
    if row.get("exit_code") == 0:
        return (1, 10**9, 10**9, 10**9)
    err = first(metric)
    return (
        0,
        int(err.get("declaration_index", -1)),
        int(err.get("line", 0)),
        int(err.get("column", 0)),
    )


def source_for_metric(path: Path) -> Path:
    source = path.parent / "source.lean"
    if not source.exists():
        raise RuntimeError(f"metric artifact has no source.lean: {path}")
    return source


def row_for_table(metric: dict[str, Any]) -> dict[str, Any]:
    err = first(metric)
    return {
        "variant": metric.get("variant"),
        "slug": metric.get("slug"),
        "sha256": metric.get("source", {}).get("sha256", ""),
        "lean_executed": metric.get("direct_lean_executed", False),
        "exit": fa(metric).get("exit_code", ""),
        "first_line": err.get("line", 0),
        "first_col": err.get("column", 0),
        "declaration": err.get("declaration", ""),
        "classification": metric.get("classification", "INFRA_FAILURE"),
        "Mock2_exit": metric.get("prerequisites", {}).get("Mock2", {}).get("exit_code", ""),
        "Mock2_Advanced_exit": metric.get("prerequisites", {}).get("Mock2_Advanced", {}).get("exit_code", ""),
        "maxErrors": fa(metric).get("max_errors", ""),
    }


def render_table(rows: list[dict[str, Any]]) -> str:
    header = (
        "variant | SHA256 | Lean executed? | exit | first line:col | declaration | classification\n"
        "--- | --- | --- | --- | --- | --- | ---\n"
    )
    body = []
    for row in rows:
        body.append(
            f"{row['variant']} | `{row['sha256']}` | {str(row['lean_executed']).lower()} | "
            f"{row['exit']} | {row['first_line']}:{row['first_col']} | "
            f"`{row['declaration']}` | {row['classification']}"
        )
    return header + "\n".join(body) + "\n"


def main() -> None:
    if OUT.exists():
        shutil.rmtree(OUT)
    OUT.mkdir(parents=True)

    metric_paths = sorted(METRICS_ROOT.rglob("metric.json"))
    metrics: list[tuple[Path, dict[str, Any]]] = [
        (path, read_json(path)) for path in metric_paths
    ]
    if not metrics:
        raise RuntimeError("INFRA_FAILURE: selector received zero direct-metric artifacts")

    baseline_rows = [
        (path, metric) for path, metric in metrics
        if metric.get("is_baseline") and metric.get("direct_lean_executed")
    ]
    if len(baseline_rows) != 1:
        raise RuntimeError(
            f"INFRA_FAILURE: expected one baseline direct metric, found {len(baseline_rows)}"
        )
    baseline_path, baseline = baseline_rows[0]
    if baseline.get("source", {}).get("sha256") != BASELINE_SHA256:
        raise RuntimeError("INFRA_FAILURE: baseline direct metric SHA mismatch")
    if not valid_direct_metric(baseline):
        raise RuntimeError("INFRA_FAILURE: current-run baseline direct metric is incomplete/invalid")

    valid = [(path, metric) for path, metric in metrics if valid_direct_metric(metric)]
    best_path, best = max(valid, key=lambda item: score(item[1]))
    strict = better(best, baseline)
    selected_path, selected = (best_path, best) if strict else (baseline_path, baseline)
    selected_source = source_for_metric(selected_path)

    selected_sha = selected.get("source", {}).get("sha256", "")
    if sha256_file(selected_source) != selected_sha:
        raise RuntimeError("INFRA_FAILURE: selected metric/source artifact SHA mismatch")
    shutil.copy2(selected_source, FA_PATH)
    worktree_sha = sha256_file(FA_PATH)
    if worktree_sha != selected_sha:
        raise RuntimeError("INFRA_FAILURE: selected source did not materialize byte-for-byte")

    selected_fa = fa(selected)
    selected_err = first(selected)
    baseline_err = first(baseline)
    if selected_fa.get("exit_code") == 0:
        classification = "FA_PASS_CANDIDATE"
    elif strict:
        classification = "STRICT_PROMOTION"
    else:
        classification = "NO_IMPROVEMENT"

    if strict and selected_err.get("declaration_index", -1) > baseline_err.get("declaration_index", -1):
        advance = "DECLARATION_BREAKTHROUGH"
    elif strict and selected_err.get("declaration") == baseline_err.get("declaration"):
        advance = "SMALL_SAME_DECLARATION_ADVANCE"
    elif strict:
        advance = "STRICT_PROMOTION"
    else:
        advance = "NO_IMPROVEMENT"

    rows = [row_for_table(metric) for _, metric in metrics]
    table = render_table(rows)
    (OUT / "candidate-results.md").write_text(table, encoding="utf-8")
    if (PREP_ROOT / "ROOT_CAUSE.json").exists():
        shutil.copy2(PREP_ROOT / "ROOT_CAUSE.json", OUT / "ROOT_CAUSE.json")
    if (PREP_ROOT / "ROOT_CAUSE.md").exists():
        shutil.copy2(PREP_ROOT / "ROOT_CAUSE.md", OUT / "ROOT_CAUSE.md")

    report = {
        "classification": classification,
        "advance_classification": advance,
        "baseline": {
            "variant": baseline.get("variant"),
            "source_sha256": baseline["source"]["sha256"],
            "line_count": baseline["source"]["line_count"],
            "direct_lean_exit": fa(baseline)["exit_code"],
            "first_error": baseline_err,
        },
        "candidate_metric_count": len(metrics),
        "valid_direct_metric_count": len(valid),
        "infra_failure_count": sum(
            1 for _, metric in metrics if metric.get("classification") == "INFRA_FAILURE"
        ),
        "strictly_better": strict,
        "selected": {
            "variant": selected.get("variant"),
            "slug": selected.get("slug"),
            "source_sha256": selected_sha,
            "line_count": selected["source"]["line_count"],
            "exit": selected_fa.get("exit_code"),
            "first_error": selected_err,
            "trust_audit": selected["source"]["trust_audit"],
            "worktree_sha256": worktree_sha,
            "selected_artifact_sha256": sha256_file(selected_source),
            "identity_ok_before_commit": selected_sha == worktree_sha == sha256_file(selected_source),
        },
        "promotion_rule": [
            "exit_code = 0",
            "later first-error declaration index",
            "same declaration: later line/column",
        ],
        "same_height_enforced": True,
        "theorem_header_unchanged_enforced": True,
        "declaration_sequence_unchanged_enforced": True,
        "candidate_results": rows,
    }
    write_json(OUT / "selection.json", report)
    (OUT / "SELECTION_SUMMARY.md").write_text(
        "# FA442 repaired matrix selection\n\n"
        f"**Classification:** {classification}\n\n"
        f"**Advance:** {advance}\n\n"
        f"**Baseline:** `{baseline['source']['sha256']}` — "
        f"{fa(baseline)['exit_code']} — {baseline_err.get('line', 0)}:{baseline_err.get('column', 0)} — "
        f"`{baseline_err.get('declaration', '')}`\n\n"
        f"**Selected:** `{selected_sha}` — {selected_fa.get('exit_code')} — "
        f"{selected_err.get('line', 0)}:{selected_err.get('column', 0)} — "
        f"`{selected_err.get('declaration', '')}`\n\n"
        "## Candidate results\n\n" + table,
        encoding="utf-8",
    )
    append_github_output(
        classification=classification,
        advance_classification=advance,
        selected_sha=selected_sha,
        selected_slug=selected.get("slug", ""),
        selected_variant=selected.get("variant", ""),
        selected_fa_exit=selected_fa.get("exit_code", 999),
        selected_first_line=selected_err.get("line", 0),
        selected_first_col=selected_err.get("column", 0),
        selected_declaration=selected_err.get("declaration", ""),
        strict_promotion=strict,
        materialized=True,
    )
    print(json.dumps(report, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    try:
        main()
    except Exception as exc:
        OUT.mkdir(parents=True, exist_ok=True)
        failure = {
            "classification": "INFRA_FAILURE",
            "stage": "selector",
            "error": repr(exc),
        }
        write_json(OUT / "SELECTOR_INFRA_FAILURE.json", failure)
        append_github_output(classification="INFRA_FAILURE", materialized=False)
        print(json.dumps(failure, indent=2), file=sys.stderr)
        raise
