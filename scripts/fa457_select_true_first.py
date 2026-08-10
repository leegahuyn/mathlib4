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
BASE = ROOT / "build-logs/fa457-true-first"
COLLECTED = BASE / "collected"
SELECTED = BASE / "selected"
REPOSITORY = os.environ["GITHUB_REPOSITORY"]
RUN_ID = int(os.environ["GITHUB_RUN_ID"])
PREFIX = "fa457-candidate-"
EXPECTED_VARIANTS = {
    "true_baseline",
    "paired_explicit",
    "paired_selected_instance",
    "paired_both_instances",
    "paired_both_instances_union_abs",
}
EXPECTED_SHA = "1f0a7e6c95691a89b3099a829da3e11fbbc731332f87e7c63d24eadade5692eb"
EXPECTED_LINE = 32035
EXPECTED_COL = 79
EXPECTED_CODE = "lean.invalidField"
EXPECTED_DECL = "nativeActualEdgeFluxIntegral_paired_circular"
EXPECTED_DECL_INDEX = 2645
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
        raise RuntimeError(f"cannot list artifacts: {proc.stderr}")
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
            result.extend(page.get("artifacts", []))
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
        zip_path = Path("/tmp") / f"fa457-{artifact_id}.zip"
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
            infra.append({"variant": variant, "reason": "artifact download failed"})
            continue
        try:
            with zipfile.ZipFile(zip_path) as archive:
                archive.extractall(unpack)
        except zipfile.BadZipFile as exc:
            infra.append({"variant": variant, "reason": f"bad artifact zip: {exc}"})
            continue
        metric_paths = list(unpack.rglob("METRIC.json"))
        source_paths = list(unpack.rglob("Mock2_FunctionalAnalysis-candidate.lean"))
        if len(metric_paths) != 1 or len(source_paths) != 1:
            infra.append({
                "variant": variant,
                "reason": "artifact lacks unique METRIC.json or candidate source",
            })
            continue
        metric = json.loads(metric_paths[0].read_text(encoding="utf-8"))
        source = source_paths[0].read_bytes()
        metric["_source_path"] = str(source_paths[0])
        metric["_artifact_id"] = artifact_id
        metric["_actual_sha256"] = sha256(source)
        metrics.append(metric)
    for variant in sorted(EXPECTED_VARIANTS - seen):
        infra.append({"variant": variant, "reason": "artifact missing"})
    for variant in sorted(seen - EXPECTED_VARIANTS):
        infra.append({"variant": variant, "reason": "unexpected artifact"})
    return metrics, infra


def validate(metric: dict[str, Any], baseline: dict[str, Any]) -> tuple[bool, list[str]]:
    reasons: list[str] = []
    checks = {
        "metric parser did not expose coded error field": "FA_first_error_code" in metric,
        "all required direct Lean commands not executed": metric.get("all_required_lean_executed") is True,
        "source bytes disagree with metric": metric.get("source_sha256") == metric.get("_actual_sha256"),
        "source/metadata SHA mismatch": metric.get("source_metadata_identity") is True,
        "Mock2 prerequisite failed": int(metric.get("Mock2_exit", 125)) == 0,
        "Mock2 Advanced prerequisite failed": int(metric.get("Mock2_Advanced_exit", 125)) == 0,
        "trust audit failed": metric.get("forbidden_clean") is True,
        "actualEdgeAmbientParam header changed": metric.get("target_header_sha256") == baseline.get("target_header_sha256"),
        "declaration sequence changed": metric.get("declaration_sequence_sha256") == baseline.get("declaration_sequence_sha256"),
    }
    for reason, ok in checks.items():
        if not ok:
            reasons.append(reason)
    if metric.get("classification") == "INFRA_FAILURE":
        reasons.extend(str(reason) for reason in metric.get("infra_reasons", []))
    return not reasons, reasons


def classify(metric: dict[str, Any], baseline: dict[str, Any], valid: bool) -> str:
    if not valid:
        return "INFRA_FAILURE"
    if metric.get("variant") == "true_baseline":
        return "BASELINE"
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
    same_height = int(metric.get("line_count", 0)) == int(baseline.get("line_count", -1))
    same_decl_start = int(metric.get("FA_error_declaration_start_line", 0)) == int(
        baseline.get("FA_error_declaration_start_line", -1)
    )
    if same_height and same_decl_start:
        baseline_pos = (
            int(baseline.get("FA_first_actual_error_line", 0)),
            int(baseline.get("FA_first_actual_error_col", 0)),
        )
        candidate_pos = (
            int(metric.get("FA_first_actual_error_line", 0)),
            int(metric.get("FA_first_actual_error_col", 0)),
        )
        if candidate_pos > baseline_pos:
            return "SMALL_SAME_DECLARATION_ADVANCE"
        if candidate_pos == baseline_pos:
            return "NO_IMPROVEMENT"
    return "NO_STRICT_PROMOTION"


def strict_key(metric: dict[str, Any]) -> tuple[int, int, int, int]:
    return (
        1 if int(metric.get("FA_exit", 125)) == 0 else 0,
        int(metric.get("FA_error_declaration_index", -1)),
        int(metric.get("FA_first_actual_error_line", 0)),
        int(metric.get("FA_first_actual_error_col", 0)),
    )


def main() -> None:
    SELECTED.mkdir(parents=True, exist_ok=True)
    metrics, infrastructure = collect()
    if infrastructure:
        result = {"classification": "SELECTOR_FAILURE", "infra": infrastructure}
        (SELECTED / "SELECTOR_FAILURE.json").write_text(
            json.dumps(result, indent=2) + "\n", encoding="utf-8"
        )
        append_output({"selector_ok": False})
        raise RuntimeError(json.dumps(result))
    baselines = [metric for metric in metrics if metric.get("variant") == "true_baseline"]
    if len(baselines) != 1:
        raise RuntimeError(f"expected one baseline metric, found {len(baselines)}")
    baseline = baselines[0]
    if not (
        baseline.get("source_sha256") == EXPECTED_SHA
        and baseline.get("all_required_lean_executed") is True
        and int(baseline.get("Mock2_exit", 125)) == 0
        and int(baseline.get("Mock2_Advanced_exit", 125)) == 0
        and int(baseline.get("FA_exit", 125)) == 1
        and int(baseline.get("FA_first_actual_error_line", 0)) == EXPECTED_LINE
        and int(baseline.get("FA_first_actual_error_col", 0)) == EXPECTED_COL
        and baseline.get("FA_first_error_code") == EXPECTED_CODE
        and baseline.get("FA_first_error_declaration") == EXPECTED_DECL
        and int(baseline.get("FA_error_declaration_index", -1)) == EXPECTED_DECL_INDEX
    ):
        raise RuntimeError("fixed parser did not reproduce true 32035:79 baseline")

    rows: list[dict[str, Any]] = []
    eligible: list[dict[str, Any]] = []
    for metric in sorted(metrics, key=lambda item: str(item.get("variant", ""))):
        ok, reasons = validate(metric, baseline)
        classification = classify(metric, baseline, ok)
        row = {
            "variant": metric.get("variant"),
            "SHA256": metric.get("source_sha256"),
            "line_count": metric.get("line_count"),
            "Lean_executed": metric.get("lean_executed"),
            "Mock2_exit": metric.get("Mock2_exit"),
            "Mock2_Advanced_exit": metric.get("Mock2_Advanced_exit"),
            "FA_exit": metric.get("FA_exit"),
            "first_line": metric.get("FA_first_actual_error_line"),
            "first_col": metric.get("FA_first_actual_error_col"),
            "first_code": metric.get("FA_first_error_code"),
            "first_message": metric.get("FA_first_error_message"),
            "declaration": metric.get("FA_first_error_declaration"),
            "declaration_index": metric.get("FA_error_declaration_index"),
            "classification": classification,
            "valid": ok,
            "reasons": reasons,
            "artifact_id": metric.get("_artifact_id"),
        }
        rows.append(row)
        if classification in {
            "FA_PASS_CANDIDATE",
            "DECLARATION_BREAKTHROUGH",
            "SMALL_SAME_DECLARATION_ADVANCE",
        }:
            eligible.append(metric)
    if eligible:
        eligible.sort(key=strict_key, reverse=True)
        chosen = eligible[0]
        mode = "STRICT_PROMOTION"
    else:
        chosen = baseline
        mode = "NO_IMPROVEMENT"
    selected_source = Path(str(chosen["_source_path"])).read_bytes()
    selected_path = SELECTED / "Mock2_FunctionalAnalysis-selected.lean"
    selected_path.write_bytes(selected_source)
    result = {
        "classification": mode,
        "authority": "direct Lean CLI with coded and classic errors parsed",
        "baseline": baseline,
        "chosen": chosen,
        "candidate_results": rows,
    }
    (SELECTED / "SELECTION.json").write_text(
        json.dumps(result, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )
    (SELECTED / "CANDIDATE_RESULTS.json").write_text(
        json.dumps(rows, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )
    append_output({
        "selector_ok": True,
        "selection_mode": mode,
        "variant": chosen.get("variant", "true_baseline"),
        "selected_sha": chosen.get("source_sha256", ""),
        "fa_exit": chosen.get("FA_exit", 125),
        "first_line": chosen.get("FA_first_actual_error_line", 0),
        "first_col": chosen.get("FA_first_actual_error_col", 0),
        "first_code": chosen.get("FA_first_error_code", ""),
        "declaration": chosen.get("FA_first_error_declaration", ""),
        "declaration_index": chosen.get("FA_error_declaration_index", -1),
    })
    print(json.dumps(result, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
