#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import json
import os
import shutil
import subprocess
import sys
import zipfile
from pathlib import Path
from typing import Any

ROOT = Path.cwd()
REPO = os.environ.get("GITHUB_REPOSITORY", "leegahuyn/mathlib4")
RUN_ID = int(os.environ["GITHUB_RUN_ID"])
BASELINE_SHA = "71dc36f16ebea92d537aa40a5d420443e4bcb93ccb76fea31efb40a6cb5c3aa0"
BASELINE_LINE = 31726
BASELINE_COL = 2
BASELINE_DECLARATION = "actualEdgeAmbientParam_hasDerivAt"
EXPECTED_LINES = 60453
PREFIX = "fa443-candidate-"
EXPECTED_VARIANTS = [
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
]
COLLECTED = ROOT / "build-logs/fa443-matrix/collected"
SELECTED = ROOT / "build-logs/fa443-matrix/selected"


def run(args: list[str], *, text: bool = True, stdout=None, stderr=None):
    return subprocess.run(
        args, cwd=ROOT, text=text, stdout=stdout, stderr=stderr, check=False
    )


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def write_output(key: str, value: object) -> None:
    output = os.environ.get("GITHUB_OUTPUT")
    if output:
        with open(output, "a", encoding="utf-8") as handle:
            handle.write(f"{key}={value}\n")


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


def list_run_artifacts() -> list[dict[str, Any]]:
    proc = run(
        [
            "gh", "api", "--paginate",
            f"/repos/{REPO}/actions/runs/{RUN_ID}/artifacts?per_page=100",
        ],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if proc.returncode != 0:
        raise RuntimeError(f"artifact listing failed: {proc.stderr}")
    artifacts: list[dict[str, Any]] = []
    for page in decode_pages(proc.stdout):
        if isinstance(page, dict):
            artifacts.extend(x for x in page.get("artifacts", []) if isinstance(x, dict))
        elif isinstance(page, list):
            artifacts.extend(x for x in page if isinstance(x, dict))
    return artifacts


def collect_artifacts() -> tuple[dict[str, Path], list[dict[str, Any]], list[str]]:
    shutil.rmtree(COLLECTED, ignore_errors=True)
    COLLECTED.mkdir(parents=True, exist_ok=True)
    artifacts = list_run_artifacts()
    by_variant: dict[str, list[dict[str, Any]]] = {v: [] for v in EXPECTED_VARIANTS}
    for artifact in artifacts:
        name = str(artifact.get("name", ""))
        if name.startswith(PREFIX) and not artifact.get("expired"):
            variant = name.removeprefix(PREFIX)
            if variant in by_variant:
                by_variant[variant].append(artifact)

    extracted: dict[str, Path] = {}
    records: list[dict[str, Any]] = []
    infra: list[str] = []
    for variant in EXPECTED_VARIANTS:
        matches = by_variant[variant]
        if len(matches) != 1:
            infra.append(f"{variant}: expected exactly one artifact, found {len(matches)}")
            continue
        artifact = matches[0]
        artifact_id = int(artifact["id"])
        zip_path = Path("/tmp") / f"fa443-{artifact_id}.zip"
        unpack = COLLECTED / variant
        unpack.mkdir(parents=True, exist_ok=True)
        with zip_path.open("wb") as handle:
            proc = run(
                ["gh", "api", f"/repos/{REPO}/actions/artifacts/{artifact_id}/zip"],
                text=False, stdout=handle, stderr=subprocess.PIPE,
            )
        record = {
            "variant": variant,
            "artifact_id": artifact_id,
            "artifact_name": artifact.get("name"),
            "download_exit": proc.returncode,
        }
        records.append(record)
        if proc.returncode != 0:
            infra.append(f"{variant}: artifact download failed")
            continue
        try:
            with zipfile.ZipFile(zip_path) as archive:
                archive.extractall(unpack)
        except zipfile.BadZipFile:
            infra.append(f"{variant}: artifact is not a valid ZIP")
            continue
        extracted[variant] = unpack
    (COLLECTED / "ARTIFACTS.json").write_text(
        json.dumps(records, indent=2) + "\n", encoding="utf-8"
    )
    return extracted, records, infra


def load_metric_for_variant(variant: str, root: Path) -> tuple[dict[str, Any] | None, Path | None, list[str]]:
    infra: list[str] = []
    metric_paths = list(root.rglob("METRIC.json"))
    source_paths = list(root.rglob("Mock2_FunctionalAnalysis-candidate.lean"))
    if len(metric_paths) != 1:
        infra.append(f"{variant}: expected one METRIC.json, found {len(metric_paths)}")
    if len(source_paths) != 1:
        infra.append(f"{variant}: expected one candidate source, found {len(source_paths)}")
    if infra:
        return None, None, infra
    try:
        metric = json.loads(metric_paths[0].read_text(encoding="utf-8"))
    except Exception as exc:
        return None, None, [f"{variant}: invalid METRIC.json: {exc}"]
    if not isinstance(metric, dict):
        return None, None, [f"{variant}: METRIC.json is not an object"]
    source = source_paths[0]
    metric["_actual_source_sha256"] = sha256_bytes(source.read_bytes())
    metric["_source_path"] = str(source)
    metric["_metric_path"] = str(metric_paths[0])
    return metric, source, []


def common_valid(metric: dict[str, Any], baseline_header_sha: str) -> bool:
    executed = metric.get("lean_executed", {})
    return (
        metric.get("classification") == "VERIFIED"
        and metric.get("authority") == "actual direct Lean CLI on generated repository source path"
        and metric.get("all_required_lean_commands_executed") is True
        and isinstance(executed, dict)
        and all(executed.get(stem) is True for stem in ["Mock2", "Mock2_Advanced", "Mock2_FunctionalAnalysis"])
        and metric.get("source_metadata_identity") is True
        and metric.get("source_sha256") == metric.get("_actual_source_sha256")
        and metric.get("line_count") == EXPECTED_LINES
        and metric.get("same_height") is True
        and metric.get("theorem_header_unchanged") is True
        and metric.get("target_header_sha256") == baseline_header_sha
        and metric.get("Mock2_exit") == 0
        and metric.get("Mock2_errors_under_cap") == 0
        and metric.get("Mock2_Advanced_exit") == 0
        and metric.get("Mock2_Advanced_errors_under_cap") == 0
        and metric.get("forbidden_clean") is True
    )


def strictly_better(candidate: dict[str, Any], baseline: dict[str, Any]) -> bool:
    if candidate.get("FA_exit") == 0:
        return True
    if candidate.get("FA_exit") != 1:
        return False
    c_decl = int(candidate.get("FA_error_declaration_index", -1))
    b_decl = int(baseline.get("FA_error_declaration_index", -1))
    if c_decl > b_decl:
        return True
    if c_decl < b_decl:
        return False
    c_pos = (
        int(candidate.get("FA_first_actual_error_line", 0)),
        int(candidate.get("FA_first_actual_error_col", 0)),
    )
    b_pos = (
        int(baseline.get("FA_first_actual_error_line", 0)),
        int(baseline.get("FA_first_actual_error_col", 0)),
    )
    return c_pos > b_pos


def candidate_classification(metric: dict[str, Any], baseline: dict[str, Any]) -> str:
    if metric.get("classification") == "INFRA_FAILURE":
        return "INFRA_FAILURE"
    if metric.get("Mock2_exit") != 0 or metric.get("Mock2_Advanced_exit") != 0:
        return "LEAN_FAILURE_PREREQUISITE"
    if metric.get("FA_exit") == 0:
        return "FA_PASS_CANDIDATE"
    if not strictly_better(metric, baseline):
        return "NO_IMPROVEMENT"
    if int(metric.get("FA_error_declaration_index", -1)) > int(baseline.get("FA_error_declaration_index", -1)):
        return "DECLARATION_BREAKTHROUGH"
    return "SMALL_SAME_DECLARATION_ADVANCE"


def fail(infra: list[str], partial: dict[str, Any] | None = None) -> None:
    SELECTED.mkdir(parents=True, exist_ok=True)
    result = {
        "classification": "INFRA_FAILURE",
        "authority": "selector requires one current-run direct metric for every matrix variant",
        "infra_reasons": infra,
        "partial": partial or {},
    }
    (SELECTED / "SELECTOR_INFRA_FAILURE.json").write_text(
        json.dumps(result, indent=2) + "\n", encoding="utf-8"
    )
    print(json.dumps(result, indent=2))
    write_output("selector_ok", "false")
    raise SystemExit(2)


def main() -> None:
    extracted, artifact_records, infra = collect_artifacts()
    metrics: dict[str, dict[str, Any]] = {}
    sources: dict[str, Path] = {}
    for variant in EXPECTED_VARIANTS:
        root = extracted.get(variant)
        if root is None:
            continue
        metric, source, errors = load_metric_for_variant(variant, root)
        infra.extend(errors)
        if metric is not None and source is not None:
            if metric.get("variant") != variant:
                infra.append(f"{variant}: metric variant mismatch {metric.get('variant')!r}")
            metrics[variant] = metric
            sources[variant] = source

    if set(metrics) != set(EXPECTED_VARIANTS):
        missing = sorted(set(EXPECTED_VARIANTS) - set(metrics))
        infra.append("missing parsed metrics: " + ", ".join(missing))
    for variant, metric in metrics.items():
        if metric.get("classification") == "INFRA_FAILURE":
            infra.append(f"{variant}: candidate metric is INFRA_FAILURE: {metric.get('infra_reasons')}")
        if metric.get("all_required_lean_commands_executed") is not True:
            infra.append(f"{variant}: not all required direct Lean commands executed")
    if infra:
        fail(infra, {"artifact_records": artifact_records, "metrics": metrics})

    baseline_metrics = [m for v, m in metrics.items() if v == "baseline"]
    if len(baseline_metrics) != 1:
        fail([f"expected one baseline direct metric, found {len(baseline_metrics)}"], {"metrics": metrics})
    baseline = baseline_metrics[0]
    header_sha = str(baseline.get("target_header_sha256", ""))
    baseline_valid = (
        common_valid(baseline, header_sha)
        and baseline.get("source_sha256") == BASELINE_SHA
        and baseline.get("FA_exit") == 1
        and int(baseline.get("FA_first_actual_error_line", 0)) == BASELINE_LINE
        and int(baseline.get("FA_first_actual_error_col", 0)) == BASELINE_COL
        and baseline.get("FA_first_error_declaration") == BASELINE_DECLARATION
    )
    if not baseline_valid:
        fail(["exact 71dc36 baseline did not reproduce 31726:2 under current-run direct Lean CLI"], {"baseline": baseline})

    valid_candidates = [
        metric for variant, metric in metrics.items()
        if variant != "baseline"
        and common_valid(metric, header_sha)
        and metric.get("source_sha256") != BASELINE_SHA
    ]
    eligible = [metric for metric in valid_candidates if strictly_better(metric, baseline)]
    if eligible:
        eligible.sort(
            key=lambda metric: (
                metric.get("FA_exit") == 0,
                int(metric.get("FA_error_declaration_index", -1)),
                int(metric.get("FA_first_actual_error_line", 0)),
                int(metric.get("FA_first_actual_error_col", 0)),
            ),
            reverse=True,
        )
        chosen = eligible[0]
        mode = "strict_promotion"
    else:
        chosen = baseline
        mode = "retain_verified_baseline"

    results = []
    for variant in EXPECTED_VARIANTS:
        metric = metrics[variant]
        results.append({
            "variant": variant,
            "source_sha256": metric.get("source_sha256"),
            "Lean_executed": metric.get("all_required_lean_commands_executed"),
            "Mock2_exit": metric.get("Mock2_exit"),
            "Mock2_Advanced_exit": metric.get("Mock2_Advanced_exit"),
            "FA_exit": metric.get("FA_exit"),
            "first_line": metric.get("FA_first_actual_error_line"),
            "first_col": metric.get("FA_first_actual_error_col"),
            "declaration": metric.get("FA_first_error_declaration"),
            "classification": "BASELINE" if variant == "baseline" else candidate_classification(metric, baseline),
        })

    shutil.rmtree(SELECTED, ignore_errors=True)
    SELECTED.mkdir(parents=True, exist_ok=True)
    selected_source = SELECTED / "Mock2_FunctionalAnalysis-selected.lean"
    selected_source.write_bytes(sources[str(chosen["variant"])].read_bytes())
    selection_classification = (
        "FA_PASS_CANDIDATE" if chosen.get("FA_exit") == 0
        else "STRICT_PROMOTION" if mode == "strict_promotion"
        else "NO_IMPROVEMENT"
    )
    selection = {
        "classification": selection_classification,
        "selector_status": "VERIFIED",
        "authority": "current-run actual direct Lean CLI matrix metrics",
        "selection_mode": mode,
        "baseline": baseline,
        "chosen": chosen,
        "eligible_strict_candidates": len(eligible),
        "candidate_results": results,
        "promotion_order": [
            "FA exit 0",
            "later declaration index",
            "same declaration with later line/column",
        ],
        "same_height_required": True,
        "expected_line_count": EXPECTED_LINES,
    }
    (SELECTED / "SELECTION.json").write_text(
        json.dumps(selection, indent=2) + "\n", encoding="utf-8"
    )
    (SELECTED / "CANDIDATE_RESULTS.json").write_text(
        json.dumps(results, indent=2) + "\n", encoding="utf-8"
    )
    (SELECTED / "CHOSEN_METRIC.json").write_text(
        json.dumps(chosen, indent=2) + "\n", encoding="utf-8"
    )
    print(json.dumps(selection, indent=2))
    write_output("selector_ok", "true")
    write_output("selection_mode", mode)
    write_output("selection_classification", selection_classification)
    write_output("variant", chosen["variant"])
    write_output("selected_sha", chosen["source_sha256"])
    write_output("matrix_fa_exit", chosen["FA_exit"])
    write_output("matrix_first_line", chosen["FA_first_actual_error_line"])
    write_output("matrix_first_col", chosen["FA_first_actual_error_col"])
    write_output("matrix_declaration", chosen["FA_first_error_declaration"])
    write_output("matrix_declaration_index", chosen["FA_error_declaration_index"])


if __name__ == "__main__":
    main()
