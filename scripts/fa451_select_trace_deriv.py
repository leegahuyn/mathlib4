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
BASE = ROOT / "build-logs/fa451-trace-deriv"
ROOT_BASELINE_DIR = BASE / "root-baseline"
COLLECTED = BASE / "collected"
SELECTED = BASE / "selected"
REPOSITORY = os.environ["GITHUB_REPOSITORY"]
RUN_ID = int(os.environ["GITHUB_RUN_ID"])
PREFIX = "fa451-candidate-"
BASE_SOURCE_SHA = "1243b2ba563d364a6977cbf9aa867e628de50a28b0f56677dc70456a210e209a"
ROOT_FIRST_LINE = 33624
ROOT_FIRST_COL = 57
ROOT_FIRST_DECLARATION = "selectedCuspRestrictionRepresentative_add"
MATRIX_BASELINE_VARIANT = "known_before_trace"
EXPECTED_VARIANTS = {
    "known_before_trace",
    "trace_lpz",
    "trace_lpz_rw",
    "trace_deriv_change",
    "trace_deriv_simpa",
    "trace_deriv_change_norm",
    "trace_deriv_simpa_norm",
}
SYNTAX_MARKERS = (
    "unexpected token",
    "unexpected end of input",
    "invalid syntax",
    "parser error",
    "expected ':='",
    'expected ":="',
)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def run(args: list[str], *, binary: bool = False) -> subprocess.CompletedProcess[Any]:
    return subprocess.run(
        args,
        cwd=ROOT,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=not binary,
    )


def append_output(values: dict[str, object]) -> None:
    path = os.environ.get("GITHUB_OUTPUT")
    if not path:
        return
    with open(path, "a", encoding="utf-8") as handle:
        for key, value in values.items():
            if isinstance(value, bool):
                value = str(value).lower()
            handle.write(f"{key}={value}\n")


def list_artifacts() -> list[dict[str, Any]]:
    proc = run([
        "gh",
        "api",
        "--paginate",
        f"/repos/{REPOSITORY}/actions/runs/{RUN_ID}/artifacts?per_page=100",
    ])
    if proc.returncode != 0:
        raise RuntimeError(f"cannot list current-run artifacts: {proc.stderr}")
    decoder = json.JSONDecoder()
    raw = proc.stdout
    pos = 0
    pages: list[Any] = []
    while pos < len(raw):
        while pos < len(raw) and raw[pos].isspace():
            pos += 1
        if pos >= len(raw):
            break
        page, pos = decoder.raw_decode(raw, pos)
        pages.append(page)
    result: list[dict[str, Any]] = []
    for page in pages:
        if isinstance(page, dict):
            result.extend(
                item for item in page.get("artifacts", []) if isinstance(item, dict)
            )
    return result


def collect() -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    COLLECTED.mkdir(parents=True, exist_ok=True)
    metrics: list[dict[str, Any]] = []
    infra: list[dict[str, Any]] = []
    seen: set[str] = set()
    for artifact in list_artifacts():
        name = str(artifact.get("name", ""))
        if not name.startswith(PREFIX) or artifact.get("expired"):
            continue
        variant = name.removeprefix(PREFIX)
        seen.add(variant)
        artifact_id = int(artifact["id"])
        zip_path = Path("/tmp") / f"fa451-{artifact_id}.zip"
        unpack = COLLECTED / variant
        unpack.mkdir(parents=True, exist_ok=True)
        with zip_path.open("wb") as handle:
            proc = subprocess.run(
                [
                    "gh",
                    "api",
                    f"/repos/{REPOSITORY}/actions/artifacts/{artifact_id}/zip",
                ],
                cwd=ROOT,
                check=False,
                stdout=handle,
                stderr=subprocess.PIPE,
            )
        if proc.returncode != 0:
            infra.append(
                {
                    "variant": variant,
                    "classification": "INFRA_FAILURE",
                    "reason": "artifact download failed",
                    "artifact_id": artifact_id,
                }
            )
            continue
        try:
            with zipfile.ZipFile(zip_path) as archive:
                archive.extractall(unpack)
        except zipfile.BadZipFile as exc:
            infra.append(
                {
                    "variant": variant,
                    "classification": "INFRA_FAILURE",
                    "reason": f"bad artifact zip: {exc}",
                    "artifact_id": artifact_id,
                }
            )
            continue
        metric_paths = list(unpack.rglob("METRIC.json"))
        source_paths = list(unpack.rglob("Mock2_FunctionalAnalysis-candidate.lean"))
        metadata_paths = list(unpack.rglob("CANDIDATE.json"))
        if (
            len(metric_paths) != 1
            or len(source_paths) != 1
            or len(metadata_paths) != 1
        ):
            infra.append(
                {
                    "variant": variant,
                    "classification": "INFRA_FAILURE",
                    "reason": "artifact lacks unique METRIC.json, CANDIDATE.json, or source",
                    "artifact_id": artifact_id,
                }
            )
            continue
        try:
            metric = json.loads(metric_paths[0].read_text(encoding="utf-8"))
            metadata = json.loads(metadata_paths[0].read_text(encoding="utf-8"))
        except Exception as exc:
            infra.append(
                {
                    "variant": variant,
                    "classification": "INFRA_FAILURE",
                    "reason": f"invalid metric/metadata JSON: {type(exc).__name__}: {exc}",
                    "artifact_id": artifact_id,
                }
            )
            continue
        source_data = source_paths[0].read_bytes()
        metric["_source_path"] = str(source_paths[0])
        metric["_metadata_path"] = str(metadata_paths[0])
        metric["_artifact_id"] = artifact_id
        metric["_artifact_name"] = name
        metric["_actual_sha256"] = sha256(source_data)
        metric["_metadata"] = metadata
        metrics.append(metric)
    for variant in sorted(EXPECTED_VARIANTS - seen):
        infra.append(
            {
                "variant": variant,
                "classification": "INFRA_FAILURE",
                "reason": "current-run candidate artifact missing",
            }
        )
    for variant in sorted(seen - EXPECTED_VARIANTS):
        infra.append(
            {
                "variant": variant,
                "classification": "INFRA_FAILURE",
                "reason": "unexpected current-run candidate artifact",
            }
        )
    return metrics, infra


def load_root_baseline() -> dict[str, Any]:
    metric_path = ROOT_BASELINE_DIR / "METRIC.json"
    source_path = ROOT_BASELINE_DIR / "Mock2_FunctionalAnalysis-root-baseline.lean"
    metadata_path = ROOT_BASELINE_DIR / "CANDIDATE.json"
    if not metric_path.exists() or not source_path.exists() or not metadata_path.exists():
        raise RuntimeError("independent checked-in root baseline metric/source is missing")
    metric = json.loads(metric_path.read_text(encoding="utf-8"))
    metadata = json.loads(metadata_path.read_text(encoding="utf-8"))
    source_data = source_path.read_bytes()
    metric["_source_path"] = str(source_path)
    metric["_metadata_path"] = str(metadata_path)
    metric["_actual_sha256"] = sha256(source_data)
    metric["_metadata"] = metadata
    metric["_independent_root_baseline"] = True
    return metric


def valid(metric: dict[str, Any], baseline: dict[str, Any]) -> tuple[bool, list[str]]:
    reasons: list[str] = []
    metadata = metric.get("_metadata", {})
    checks = {
        "direct Lean CLI did not execute for every required module":
            metric.get("all_required_lean_executed") is True,
        "candidate source SHA differs from artifact bytes":
            metric.get("source_sha256") == metric.get("_actual_sha256"),
        "candidate source/metadata SHA mismatch":
            metric.get("source_metadata_identity") is True,
        "candidate was not generated from the authoritative checked-in source":
            metadata.get("baseline_sha256") == BASE_SOURCE_SHA,
        "Mock2 prerequisite failed":
            int(metric.get("Mock2_exit", 125)) == 0,
        "Mock2 prerequisite emitted Lean errors":
            int(metric.get("Mock2_errors_under_cap", 1)) == 0,
        "Mock2_Advanced prerequisite failed":
            int(metric.get("Mock2_Advanced_exit", 125)) == 0,
        "Mock2_Advanced prerequisite emitted Lean errors":
            int(metric.get("Mock2_Advanced_errors_under_cap", 1)) == 0,
        "forbidden-token audit failed":
            metric.get("forbidden_clean") is True,
        "actualEdgeAmbientParam theorem header changed":
            metric.get("target_header_sha256")
            == baseline.get("target_header_sha256"),
        "declaration sequence changed":
            metric.get("declaration_sequence_sha256")
            == baseline.get("declaration_sequence_sha256"),
    }
    for reason, ok in checks.items():
        if not ok:
            reasons.append(reason)
    if metric.get("classification") == "INFRA_FAILURE":
        reasons.extend(str(item) for item in metric.get("infra_reasons", []))
    return not reasons, reasons


def validate_root_baseline(root: dict[str, Any]) -> tuple[bool, list[str]]:
    reasons: list[str] = []
    checks = {
        "root direct Lean CLI did not execute":
            root.get("all_required_lean_executed") is True,
        "root source bytes do not equal authoritative SHA":
            root.get("source_sha256") == BASE_SOURCE_SHA
            and root.get("_actual_sha256") == BASE_SOURCE_SHA,
        "root source/metadata identity failed":
            root.get("source_metadata_identity") is True,
        "root Mock2 failed": int(root.get("Mock2_exit", 125)) == 0,
        "root Mock2 emitted errors":
            int(root.get("Mock2_errors_under_cap", 1)) == 0,
        "root Mock2_Advanced failed":
            int(root.get("Mock2_Advanced_exit", 125)) == 0,
        "root Mock2_Advanced emitted errors":
            int(root.get("Mock2_Advanced_errors_under_cap", 1)) == 0,
        "root FA exit changed": int(root.get("FA_exit", 125)) == 1,
        "root first line changed":
            int(root.get("FA_first_actual_error_line", 0)) == ROOT_FIRST_LINE,
        "root first column changed":
            int(root.get("FA_first_actual_error_col", 0)) == ROOT_FIRST_COL,
        "root first declaration changed":
            root.get("FA_first_error_declaration") == ROOT_FIRST_DECLARATION,
        "root forbidden audit failed": root.get("forbidden_clean") is True,
    }
    for reason, ok in checks.items():
        if not ok:
            reasons.append(reason)
    if root.get("classification") == "INFRA_FAILURE":
        reasons.extend(str(item) for item in root.get("infra_reasons", []))
    return not reasons, reasons


def classify(metric: dict[str, Any], baseline: dict[str, Any], ok: bool) -> str:
    if not ok:
        return "INFRA_FAILURE"
    if int(metric.get("FA_exit", 125)) == 0:
        return "FA_PASS_CANDIDATE"
    message = str(metric.get("FA_first_error_message", "")).lower()
    if any(marker in message for marker in SYNTAX_MARKERS):
        return "LEAN_SYNTAX_REGRESSION"
    baseline_index = int(baseline.get("FA_error_declaration_index", -1))
    candidate_index = int(metric.get("FA_error_declaration_index", -1))
    if candidate_index > baseline_index:
        return "DECLARATION_BREAKTHROUGH"
    if candidate_index < baseline_index:
        return "REGRESSION"
    same_height = int(metric.get("line_count", 0)) == int(
        baseline.get("line_count", -1)
    )
    same_declaration_start = int(
        metric.get("FA_error_declaration_start_line", 0)
    ) == int(baseline.get("FA_error_declaration_start_line", -1))
    if same_height and same_declaration_start:
        baseline_position = (
            int(baseline.get("FA_first_actual_error_line", 0)),
            int(baseline.get("FA_first_actual_error_col", 0)),
        )
        candidate_position = (
            int(metric.get("FA_first_actual_error_line", 0)),
            int(metric.get("FA_first_actual_error_col", 0)),
        )
        if candidate_position > baseline_position:
            return "SMALL_SAME_DECLARATION_ADVANCE"
        if candidate_position == baseline_position:
            return "NO_IMPROVEMENT"
    return "NO_STRICT_PROMOTION"


def strict_key(metric: dict[str, Any]) -> tuple[int, int, int, int]:
    return (
        1 if int(metric.get("FA_exit", 125)) == 0 else 0,
        int(metric.get("FA_error_declaration_index", -1)),
        int(metric.get("FA_first_actual_error_line", 0)),
        int(metric.get("FA_first_actual_error_col", 0)),
    )


def metric_row(
    metric: dict[str, Any],
    *,
    classification: str,
    valid_metric: bool,
    reasons: list[str],
) -> dict[str, Any]:
    return {
        "variant": metric.get("variant"),
        "SHA256": metric.get("source_sha256"),
        "line_count": metric.get("line_count"),
        "Lean_executed": metric.get("lean_executed"),
        "all_required_lean_executed": metric.get("all_required_lean_executed"),
        "Mock2_exit": metric.get("Mock2_exit"),
        "Mock2_Advanced_exit": metric.get("Mock2_Advanced_exit"),
        "FA_exit": metric.get("FA_exit"),
        "first_line": metric.get("FA_first_actual_error_line"),
        "first_col": metric.get("FA_first_actual_error_col"),
        "first_message": metric.get("FA_first_error_message"),
        "declaration": metric.get("FA_first_error_declaration"),
        "declaration_index": metric.get("FA_error_declaration_index"),
        "declaration_start_line": metric.get("FA_error_declaration_start_line"),
        "classification": classification,
        "valid": valid_metric,
        "reasons": reasons,
        "artifact_id": metric.get("_artifact_id"),
        "artifact_name": metric.get("_artifact_name"),
    }


def fail(reason: str, details: dict[str, Any] | None = None) -> None:
    SELECTED.mkdir(parents=True, exist_ok=True)
    result = {
        "classification": "SELECTOR_FAILURE",
        "reason": reason,
        "details": details or {},
        "workflow_run_id": RUN_ID,
        "workflow_run_url": f"https://github.com/{REPOSITORY}/actions/runs/{RUN_ID}",
    }
    (SELECTED / "SELECTOR_FAILURE.json").write_text(
        json.dumps(result, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    append_output({"selector_ok": False, "selection_mode": "INFRA_FAILURE"})
    raise RuntimeError(reason)


def main() -> None:
    SELECTED.mkdir(parents=True, exist_ok=True)
    root_baseline = load_root_baseline()
    root_ok, root_reasons = validate_root_baseline(root_baseline)
    if not root_ok:
        fail(
            "independent checked-in root baseline did not reproduce 33624:57",
            {"root_reasons": root_reasons, "root_baseline": root_baseline},
        )

    metrics, infrastructure = collect()
    if infrastructure:
        fail(
            "one or more FA451 variants lack complete current-run direct evidence",
            {"candidate_infrastructure_failures": infrastructure},
        )
    variants = [str(metric.get("variant", "")) for metric in metrics]
    if set(variants) != EXPECTED_VARIANTS or len(variants) != len(EXPECTED_VARIANTS):
        fail(
            "FA451 metric variants are incomplete or duplicated",
            {"variants": variants, "expected": sorted(EXPECTED_VARIANTS)},
        )
    matrix_baselines = [
        metric
        for metric in metrics
        if metric.get("variant") == MATRIX_BASELINE_VARIANT
    ]
    if len(matrix_baselines) != 1:
        fail(f"expected exactly one {MATRIX_BASELINE_VARIANT} direct metric")
    matrix_baseline = matrix_baselines[0]
    matrix_baseline_ok, matrix_baseline_reasons = valid(
        matrix_baseline, root_baseline
    )
    if not matrix_baseline_ok:
        fail(
            "FA451 matrix baseline is not a valid direct Lean metric",
            {
                "matrix_baseline_reasons": matrix_baseline_reasons,
                "matrix_baseline": matrix_baseline,
            },
        )
    if int(matrix_baseline.get("FA_exit", 125)) not in (0, 1):
        fail(
            "FA451 matrix baseline returned a non-Lean infrastructure exit",
            {"matrix_baseline": matrix_baseline},
        )
    if int(matrix_baseline.get("FA_exit", 125)) != 0 and int(
        matrix_baseline.get("FA_first_actual_error_line", 0)
    ) <= 0:
        fail(
            "FA451 matrix baseline failed without a parsed first Lean error",
            {"matrix_baseline": matrix_baseline},
        )

    rows: list[dict[str, Any]] = [
        metric_row(
            root_baseline,
            classification="ROOT_BASELINE",
            valid_metric=True,
            reasons=[],
        )
    ]
    matrix_eligible: list[dict[str, Any]] = []
    for metric in sorted(metrics, key=lambda item: str(item.get("variant", ""))):
        ok, reasons = valid(metric, matrix_baseline)
        classification = (
            "MATRIX_BASELINE"
            if metric.get("variant") == MATRIX_BASELINE_VARIANT
            else classify(metric, matrix_baseline, ok)
        )
        rows.append(
            metric_row(
                metric,
                classification=classification,
                valid_metric=ok,
                reasons=reasons,
            )
        )
        if classification in {
            "FA_PASS_CANDIDATE",
            "DECLARATION_BREAKTHROUGH",
            "SMALL_SAME_DECLARATION_ADVANCE",
        }:
            matrix_eligible.append(metric)

    if matrix_eligible:
        matrix_eligible.sort(key=strict_key, reverse=True)
        matrix_chosen = matrix_eligible[0]
    else:
        matrix_chosen = matrix_baseline

    chosen_ok, chosen_reasons = valid(matrix_chosen, root_baseline)
    root_progress = classify(matrix_chosen, root_baseline, chosen_ok)
    if root_progress in {
        "FA_PASS_CANDIDATE",
        "DECLARATION_BREAKTHROUGH",
        "SMALL_SAME_DECLARATION_ADVANCE",
    }:
        chosen = matrix_chosen
        selection_mode = "STRICT_PROMOTION"
    else:
        chosen = root_baseline
        selection_mode = "NO_IMPROVEMENT"

    selected_source = Path(str(chosen["_source_path"])).read_bytes()
    selected_path = SELECTED / "Mock2_FunctionalAnalysis-selected.lean"
    selected_path.write_bytes(selected_source)
    result = {
        "classification": selection_mode,
        "authority": "independent root baseline plus complete current-run direct Lean CLI matrix",
        "workflow_run_id": RUN_ID,
        "workflow_run_url": f"https://github.com/{REPOSITORY}/actions/runs/{RUN_ID}",
        "root_baseline": root_baseline,
        "matrix_baseline": matrix_baseline,
        "matrix_chosen": matrix_chosen,
        "matrix_chosen_vs_root": {
            "classification": root_progress,
            "valid": chosen_ok,
            "reasons": chosen_reasons,
        },
        "chosen": chosen,
        "candidate_results": rows,
        "promotion_rule": [
            "FA exit 0",
            "later first-error declaration index",
            "same declaration only with equal file height and equal declaration start, then later line/column",
            "otherwise retain the independently recompiled checked-in root source",
        ],
    }
    (SELECTED / "SELECTION.json").write_text(
        json.dumps(result, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    (SELECTED / "CANDIDATE_RESULTS.json").write_text(
        json.dumps(rows, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    append_output(
        {
            "selector_ok": True,
            "selection_mode": selection_mode,
            "variant": chosen.get("variant", "checked_in_root"),
            "selected_sha": chosen.get("source_sha256", ""),
            "fa_exit": chosen.get("FA_exit", 125),
            "first_line": chosen.get("FA_first_actual_error_line", 0),
            "first_col": chosen.get("FA_first_actual_error_col", 0),
            "declaration": chosen.get("FA_first_error_declaration", ""),
            "declaration_index": chosen.get("FA_error_declaration_index", -1),
        }
    )
    print(json.dumps(result, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
