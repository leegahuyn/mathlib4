#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import json
import os
import subprocess
import zipfile
from pathlib import Path
from typing import Any

ROOT = Path.cwd()
REPOSITORY = os.environ.get("GITHUB_REPOSITORY", "leegahuyn/mathlib4")
RUN_ID = int(os.environ["GITHUB_RUN_ID"])
BASE = ROOT / "build-logs/fa442-pipeline-repair"
COLLECTED = BASE / "collected"
SELECTED = BASE / "selected"
INDEPENDENT_BASELINE_DIR = BASE / "selector-baseline"
EXPECTED_BASELINE_SHA = (
    "71dc36f16ebea92d537aa40a5d420443e4bcb93ccb76fea31efb40a6cb5c3aa0"
)
EXPECTED_LINES = 60453
EXPECTED_FIRST_LINE = 31726
EXPECTED_FIRST_COL = 2
EXPECTED_FIRST_DECLARATION = "actualEdgeAmbientParam_hasDerivAt"
ARTIFACT_PREFIX = "fa442-repair-candidate-"
EXPECTED_VARIANTS = {
    "baseline",
    "slope_only",
    "slope_structures",
    "slope_change_convert",
    "slope_paired_parenthesized",
    "slope_paired_dot",
    "slope_paired_parenthesized_ring",
    "slope_paired_parenthesized_ring_height",
    "slope_paired_parenthesized_ring_height_upper",
    "slope_paired_parenthesized_ring_height_upper_tail",
    "slope_paired_parenthesized_ring_height_upper_tail_zero",
    "slope_paired_parenthesized_all_known",
    "slope_paired_dot_all_known",
    "slope_structures_paired_all_known",
    "slope_change_convert_paired_all_known",
    "slope_paired_parenthesized_deep_simp",
}


def run(
    args: list[str],
    *,
    text: bool = True,
    stdout: Any = subprocess.PIPE,
    stderr: Any = subprocess.PIPE,
) -> subprocess.CompletedProcess[Any]:
    return subprocess.run(
        args,
        cwd=ROOT,
        text=text,
        stdout=stdout,
        stderr=stderr,
        check=False,
    )


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def append_outputs(values: dict[str, object]) -> None:
    output = os.environ.get("GITHUB_OUTPUT")
    if not output:
        return
    with open(output, "a", encoding="utf-8") as handle:
        for key, value in values.items():
            rendered = str(value).lower() if isinstance(value, bool) else str(value)
            handle.write(f"{key}={rendered}\n")


def decode_pages(raw: str) -> list[object]:
    if not raw.strip():
        return []
    try:
        return [json.loads(raw)]
    except json.JSONDecodeError:
        decoder = json.JSONDecoder()
        pages: list[object] = []
        index = 0
        while index < len(raw):
            while index < len(raw) and raw[index].isspace():
                index += 1
            if index >= len(raw):
                break
            value, index = decoder.raw_decode(raw, index)
            pages.append(value)
        return pages


def action_artifacts() -> list[dict[str, Any]]:
    proc = run(
        [
            "gh",
            "api",
            "--paginate",
            f"/repos/{REPOSITORY}/actions/runs/{RUN_ID}/artifacts?per_page=100",
        ]
    )
    if proc.returncode != 0:
        raise RuntimeError(f"cannot list run artifacts: {proc.stderr}")
    result: list[dict[str, Any]] = []
    for page in decode_pages(proc.stdout):
        if isinstance(page, dict):
            result.extend(
                item for item in page.get("artifacts", []) if isinstance(item, dict)
            )
        elif isinstance(page, list):
            result.extend(item for item in page if isinstance(item, dict))
    return result


def collect_artifacts() -> list[dict[str, Any]]:
    COLLECTED.mkdir(parents=True, exist_ok=True)
    rows: list[dict[str, Any]] = []
    for artifact in action_artifacts():
        name = str(artifact.get("name", ""))
        if not name.startswith(ARTIFACT_PREFIX) or artifact.get("expired"):
            continue
        variant = name.removeprefix(ARTIFACT_PREFIX)
        artifact_id = int(artifact["id"])
        zip_path = Path("/tmp") / f"fa442-repair-{artifact_id}.zip"
        unpack = COLLECTED / variant
        unpack.mkdir(parents=True, exist_ok=True)
        with zip_path.open("wb") as handle:
            proc = run(
                [
                    "gh",
                    "api",
                    f"/repos/{REPOSITORY}/actions/artifacts/{artifact_id}/zip",
                ],
                text=False,
                stdout=handle,
            )
        row: dict[str, Any] = {
            "artifact_id": artifact_id,
            "name": name,
            "variant": variant,
            "download_exit": proc.returncode,
        }
        if proc.returncode == 0:
            try:
                with zipfile.ZipFile(zip_path) as archive:
                    archive.extractall(unpack)
                row["unpacked"] = True
            except zipfile.BadZipFile as exc:
                row["bad_zip"] = str(exc)
                row["unpacked"] = False
        else:
            row["download_error"] = (
                proc.stderr.decode("utf-8", errors="replace")
                if isinstance(proc.stderr, bytes)
                else str(proc.stderr)
            )
            row["unpacked"] = False
        rows.append(row)
    (COLLECTED / "ARTIFACTS.json").write_text(
        json.dumps(rows, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )
    return rows


def find_metric_and_source(root: Path) -> tuple[Path | None, Path | None]:
    metrics = list(root.rglob("METRIC.json"))
    if len(metrics) != 1:
        return (metrics[0] if metrics else None), None
    metric_path = metrics[0]
    candidates = list(metric_path.parent.glob("Mock2_FunctionalAnalysis-candidate.lean"))
    if len(candidates) != 1:
        return metric_path, None
    return metric_path, candidates[0]


def load_candidate_metrics(
    artifact_rows: list[dict[str, Any]],
) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    metrics: list[dict[str, Any]] = []
    infrastructure: list[dict[str, Any]] = []
    seen: set[str] = set()
    for row in artifact_rows:
        variant = str(row["variant"])
        seen.add(variant)
        root = COLLECTED / variant
        metric_path, source_path = find_metric_and_source(root)
        if not row.get("unpacked") or metric_path is None or source_path is None:
            infrastructure.append(
                {
                    "variant": variant,
                    "classification": "INFRA_FAILURE",
                    "reason": "artifact missing unique METRIC.json or candidate source",
                    "artifact": row,
                }
            )
            continue
        try:
            metric = json.loads(metric_path.read_text(encoding="utf-8"))
        except Exception as exc:
            infrastructure.append(
                {
                    "variant": variant,
                    "classification": "INFRA_FAILURE",
                    "reason": f"invalid metric JSON: {type(exc).__name__}: {exc}",
                    "artifact": row,
                }
            )
            continue
        data = source_path.read_bytes()
        metric["_metric_path"] = str(metric_path)
        metric["_source_path"] = str(source_path)
        metric["_actual_sha256"] = sha256(data)
        metric["_artifact_id"] = row["artifact_id"]
        metric["_artifact_name"] = row["name"]
        metrics.append(metric)

    for variant in sorted(EXPECTED_VARIANTS - seen):
        infrastructure.append(
            {
                "variant": variant,
                "classification": "INFRA_FAILURE",
                "reason": "candidate artifact missing from current workflow run",
            }
        )
    for variant in sorted(seen - EXPECTED_VARIANTS):
        infrastructure.append(
            {
                "variant": variant,
                "classification": "INFRA_FAILURE",
                "reason": "unexpected candidate artifact in current workflow run",
            }
        )
    return metrics, infrastructure


def load_independent_baseline() -> dict[str, Any]:
    metric_path = INDEPENDENT_BASELINE_DIR / "METRIC.json"
    source_path = INDEPENDENT_BASELINE_DIR / "Mock2_FunctionalAnalysis-candidate.lean"
    if not metric_path.exists() or not source_path.exists():
        raise RuntimeError("selector's independent baseline metric/source is missing")
    metric = json.loads(metric_path.read_text(encoding="utf-8"))
    data = source_path.read_bytes()
    metric["_metric_path"] = str(metric_path)
    metric["_source_path"] = str(source_path)
    metric["_actual_sha256"] = sha256(data)
    metric["_independent_selector_baseline"] = True
    return metric


def common_valid(
    metric: dict[str, Any], header_sha: str, declaration_sequence_sha: str
) -> bool:
    return (
        metric.get("classification") != "INFRA_FAILURE"
        and metric.get("authority") == "direct Lean CLI on repository source path"
        and metric.get("lean_executed") is True
        and metric.get("all_required_lean_executed") is True
        and metric.get("source_metadata_identity") is True
        and metric.get("source_sha256") == metric.get("_actual_sha256")
        and int(metric.get("line_count", 0)) == EXPECTED_LINES
        and metric.get("target_header_sha256") == header_sha
        and metric.get("declaration_sequence_sha256") == declaration_sequence_sha
        and metric.get("Mock2_executed") is True
        and int(metric.get("Mock2_exit", 125)) == 0
        and int(metric.get("Mock2_errors_under_cap", 1)) == 0
        and metric.get("Mock2_Advanced_executed") is True
        and int(metric.get("Mock2_Advanced_exit", 125)) == 0
        and int(metric.get("Mock2_Advanced_errors_under_cap", 1)) == 0
        and metric.get("FA_executed") is True
        and metric.get("forbidden_not_increased") is True
        and metric.get("forbidden_clean") is True
    )


def exact_baseline(metric: dict[str, Any]) -> bool:
    header = str(metric.get("target_header_sha256", ""))
    sequence = str(metric.get("declaration_sequence_sha256", ""))
    return (
        common_valid(metric, header, sequence)
        and metric.get("variant") == "baseline"
        and metric.get("source_sha256") == EXPECTED_BASELINE_SHA
        and int(metric.get("FA_exit", 125)) == 1
        and int(metric.get("FA_first_actual_error_line", 0)) == EXPECTED_FIRST_LINE
        and int(metric.get("FA_first_actual_error_col", 0)) == EXPECTED_FIRST_COL
        and metric.get("FA_first_error_declaration") == EXPECTED_FIRST_DECLARATION
    )


def classify_progress(
    metric: dict[str, Any], baseline: dict[str, Any], *, valid: bool
) -> str:
    if not valid:
        return "INFRA_FAILURE"
    if metric.get("source_sha256") == EXPECTED_BASELINE_SHA:
        return "BASELINE"
    if int(metric.get("FA_exit", 125)) == 0:
        return "FA_PASS_CANDIDATE"

    baseline_index = int(baseline.get("FA_error_declaration_index", -1))
    candidate_index = int(metric.get("FA_error_declaration_index", -1))
    baseline_line = int(baseline.get("FA_first_actual_error_line", 0))
    baseline_col = int(baseline.get("FA_first_actual_error_col", 0))
    candidate_line = int(metric.get("FA_first_actual_error_line", 0))
    candidate_col = int(metric.get("FA_first_actual_error_col", 0))

    if candidate_index > baseline_index:
        return "DECLARATION_BREAKTHROUGH"
    if candidate_index == baseline_index:
        if candidate_line > baseline_line or (
            candidate_line == baseline_line and candidate_col > baseline_col
        ):
            return "SMALL_SAME_DECLARATION_ADVANCE"
        if candidate_line == baseline_line and candidate_col == baseline_col:
            return "NO_IMPROVEMENT"
    return "REGRESSION_OR_INVALID_PROGRESS"


def strict_key(metric: dict[str, Any]) -> tuple[int, int, int, int]:
    return (
        1 if int(metric.get("FA_exit", 125)) == 0 else 0,
        int(metric.get("FA_error_declaration_index", -1)),
        int(metric.get("FA_first_actual_error_line", 0)),
        int(metric.get("FA_first_actual_error_col", 0)),
    )


def fail_selector(reason: str, details: dict[str, Any] | None = None) -> None:
    SELECTED.mkdir(parents=True, exist_ok=True)
    result = {
        "classification": "SELECTOR_FAILURE",
        "reason": reason,
        "details": details or {},
    }
    (SELECTED / "SELECTOR_FAILURE.json").write_text(
        json.dumps(result, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )
    append_outputs({"selector_ok": False, "selection_mode": "infra_failure"})
    raise RuntimeError(reason)


def main() -> None:
    SELECTED.mkdir(parents=True, exist_ok=True)
    artifact_rows = collect_artifacts()
    metrics, infrastructure = load_candidate_metrics(artifact_rows)

    if infrastructure:
        fail_selector(
            "one or more matrix candidates lack complete current-run direct evidence",
            {"candidate_infrastructure_failures": infrastructure},
        )

    variants = [str(metric.get("variant", "")) for metric in metrics]
    if set(variants) != EXPECTED_VARIANTS or len(variants) != len(EXPECTED_VARIANTS):
        fail_selector(
            "matrix metric variants are incomplete or duplicated",
            {"variants": variants, "expected": sorted(EXPECTED_VARIANTS)},
        )

    baseline_metrics = [metric for metric in metrics if metric.get("variant") == "baseline"]
    if len(baseline_metrics) != 1:
        fail_selector(
            f"expected exactly one matrix baseline direct metric, found {len(baseline_metrics)}"
        )
    matrix_baseline = baseline_metrics[0]
    independent_baseline = load_independent_baseline()

    if not exact_baseline(matrix_baseline):
        fail_selector(
            "matrix baseline did not reproduce authoritative 31726:2 direct Lean result",
            {"matrix_baseline": matrix_baseline},
        )
    if not exact_baseline(independent_baseline):
        fail_selector(
            "selector independent baseline did not reproduce authoritative 31726:2 result",
            {"independent_baseline": independent_baseline},
        )

    identity_fields = (
        "source_sha256",
        "line_count",
        "target_header_sha256",
        "declaration_sequence_sha256",
        "FA_exit",
        "FA_first_actual_error_line",
        "FA_first_actual_error_col",
        "FA_first_error_declaration",
        "FA_error_declaration_index",
    )
    mismatches = {
        field: {
            "matrix": matrix_baseline.get(field),
            "selector": independent_baseline.get(field),
        }
        for field in identity_fields
        if matrix_baseline.get(field) != independent_baseline.get(field)
    }
    if mismatches:
        fail_selector(
            "matrix baseline and independently recompiled selector baseline disagree",
            {"mismatches": mismatches},
        )

    header_sha = str(independent_baseline["target_header_sha256"])
    declaration_sequence_sha = str(independent_baseline["declaration_sequence_sha256"])
    candidate_results: list[dict[str, Any]] = []
    eligible: list[dict[str, Any]] = []
    for metric in sorted(metrics, key=lambda row: str(row.get("variant", ""))):
        valid = common_valid(metric, header_sha, declaration_sequence_sha)
        progress = classify_progress(metric, independent_baseline, valid=valid)
        row = {
            "variant": metric.get("variant"),
            "source_sha256": metric.get("source_sha256"),
            "Lean_executed": metric.get("lean_executed"),
            "Mock2_exit": metric.get("Mock2_exit"),
            "Mock2_Advanced_exit": metric.get("Mock2_Advanced_exit"),
            "FA_exit": metric.get("FA_exit"),
            "first_line": metric.get("FA_first_actual_error_line"),
            "first_col": metric.get("FA_first_actual_error_col"),
            "first_message": metric.get("FA_first_error_message"),
            "declaration": metric.get("FA_first_error_declaration"),
            "declaration_index": metric.get("FA_error_declaration_index"),
            "classification": progress,
            "metric_classification": metric.get("classification"),
            "artifact_id": metric.get("_artifact_id"),
            "valid_direct_metric": valid,
            "infra_reasons": metric.get("infra_reasons", []),
        }
        candidate_results.append(row)
        if progress in {
            "FA_PASS_CANDIDATE",
            "DECLARATION_BREAKTHROUGH",
            "SMALL_SAME_DECLARATION_ADVANCE",
        }:
            eligible.append(metric)

    if eligible:
        eligible.sort(key=strict_key, reverse=True)
        chosen = eligible[0]
        selection_mode = "strict_promotion"
        chosen_progress = classify_progress(chosen, independent_baseline, valid=True)
    else:
        chosen = independent_baseline
        selection_mode = "no_improvement"
        chosen_progress = "NO_IMPROVEMENT"

    source_path = Path(str(chosen["_source_path"]))
    selected_source = SELECTED / "Mock2_FunctionalAnalysis-selected.lean"
    selected_source.write_bytes(source_path.read_bytes())
    selected_sha = sha256(selected_source.read_bytes())
    selected_metadata = {
        "variant": chosen.get("variant", "baseline"),
        "baseline_sha256": EXPECTED_BASELINE_SHA,
        "candidate_sha256": selected_sha,
        "line_count": int(chosen.get("line_count", EXPECTED_LINES)),
        "target_declaration": EXPECTED_FIRST_DECLARATION,
        "target_header_sha256": chosen.get("target_header_sha256", ""),
        "repairs": chosen.get("repairs", []),
        "baseline_forbidden_counts": independent_baseline.get(
            "candidate_forbidden_counts", {}
        ),
        "candidate_forbidden_counts": chosen.get("candidate_forbidden_counts", {}),
        "declaration_sequence_sha256": chosen.get("declaration_sequence_sha256", ""),
    }
    (SELECTED / "SELECTED_METADATA.json").write_text(
        json.dumps(selected_metadata, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    if selected_sha != chosen.get("source_sha256"):
        fail_selector(
            "selected source bytes disagree with selected direct metric",
            {"selected_sha": selected_sha, "metric_sha": chosen.get("source_sha256")},
        )

    result = {
        "classification": (
            "STRICT_PROMOTION" if selection_mode == "strict_promotion" else "NO_IMPROVEMENT"
        ),
        "authority": "current-run matrix and independent selector direct Lean CLI",
        "selection_mode": selection_mode,
        "baseline": independent_baseline,
        "matrix_baseline": matrix_baseline,
        "chosen": chosen,
        "chosen_progress_classification": chosen_progress,
        "eligible_strict_candidates": len(eligible),
        "candidate_results": candidate_results,
        "promotion_order": [
            "FA exit code 0",
            "later first-error declaration index",
            "same declaration: later line",
            "same line: later column",
        ],
        "same_height_required": True,
        "declaration_sequence_identity_required": True,
        "target_header_identity_required": True,
    }
    (SELECTED / "CANDIDATE_RESULTS.json").write_text(
        json.dumps(candidate_results, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    headers = (
        "variant",
        "source_sha256",
        "Lean_executed",
        "FA_exit",
        "first_line",
        "first_col",
        "declaration",
        "classification",
        "artifact_id",
    )
    tsv_lines = ["\t".join(headers)]
    for row in candidate_results:
        tsv_lines.append("\t".join(str(row.get(header, "")) for header in headers))
    (SELECTED / "CANDIDATE_RESULTS.tsv").write_text(
        "\n".join(tsv_lines) + "\n", encoding="utf-8"
    )
    (SELECTED / "SELECTION.json").write_text(
        json.dumps(result, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )
    print(json.dumps(result, indent=2, ensure_ascii=False))
    append_outputs(
        {
            "selector_ok": True,
            "selection_mode": selection_mode,
            "selected_sha": selected_sha,
            "variant": chosen.get("variant", "baseline"),
            "progress_classification": chosen_progress,
            "matrix_fa_exit": chosen.get("FA_exit", 125),
            "matrix_first_line": chosen.get("FA_first_actual_error_line", 0),
            "matrix_first_col": chosen.get("FA_first_actual_error_col", 0),
            "matrix_declaration": chosen.get("FA_first_error_declaration", ""),
            "matrix_declaration_index": chosen.get("FA_error_declaration_index", -1),
            "baseline_sha": independent_baseline.get("source_sha256", ""),
            "baseline_first_line": independent_baseline.get(
                "FA_first_actual_error_line", 0
            ),
            "baseline_first_col": independent_baseline.get("FA_first_actual_error_col", 0),
        }
    )


if __name__ == "__main__":
    main()
