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
BASE = ROOT / "build-logs/fa453-compact-energy"
COLLECTED = BASE / "collected"
SELECTED = BASE / "selected"
REPOSITORY = os.environ["GITHUB_REPOSITORY"]
RUN_ID = int(os.environ["GITHUB_RUN_ID"])
PREFIX = "fa459-candidate-"
EXPECTED_VARIANTS = {
    "baseline",
    "macro_pair_only",
    "macro_pair_smul",
    "macro_pair_smul_cumulative",
    "postfix_pair_smul_cumulative",
}
BASELINE_SHA = "1f0a7e6c95691a89b3099a829da3e11fbbc731332f87e7c63d24eadade5692eb"
BASELINE_LINES = 60450
BASELINE_FIRST = (32035, 79)
BASELINE_DECL = "nativeActualEdgeFluxIntegral_paired_circular"
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
        args, cwd=ROOT, check=False, stdout=subprocess.PIPE,
        stderr=subprocess.PIPE, text=not binary,
    )


def append_output(values: dict[str, object]) -> None:
    output = os.environ.get("GITHUB_OUTPUT")
    if not output:
        return
    with open(output, "a", encoding="utf-8") as handle:
        for key, value in values.items():
            if isinstance(value, bool):
                value = str(value).lower()
            handle.write(f"{key}={value}\n")


def decode_pages(raw: str) -> list[Any]:
    decoder = json.JSONDecoder()
    pages: list[Any] = []
    index = 0
    while index < len(raw):
        while index < len(raw) and raw[index].isspace():
            index += 1
        if index >= len(raw):
            break
        page, index = decoder.raw_decode(raw, index)
        pages.append(page)
    return pages


def list_artifacts() -> list[dict[str, Any]]:
    proc = run([
        "gh", "api", "--paginate",
        f"/repos/{REPOSITORY}/actions/runs/{RUN_ID}/artifacts?per_page=100",
    ])
    if proc.returncode != 0:
        raise RuntimeError(f"cannot list artifacts: {proc.stderr}")
    artifacts: list[dict[str, Any]] = []
    for page in decode_pages(proc.stdout):
        if isinstance(page, dict):
            artifacts.extend(
                item for item in page.get("artifacts", []) if isinstance(item, dict)
            )
    return artifacts


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
        archive_path = Path("/tmp") / f"fa459-{artifact_id}.zip"
        unpack = COLLECTED / variant
        unpack.mkdir(parents=True, exist_ok=True)
        with archive_path.open("wb") as handle:
            proc = subprocess.run(
                ["gh", "api", f"/repos/{REPOSITORY}/actions/artifacts/{artifact_id}/zip"],
                cwd=ROOT, check=False, stdout=handle, stderr=subprocess.PIPE,
            )
        if proc.returncode != 0:
            infra.append({"variant": variant, "classification": "INFRA_FAILURE",
                          "reason": "artifact download failed", "artifact_id": artifact_id})
            continue
        try:
            with zipfile.ZipFile(archive_path) as archive:
                archive.extractall(unpack)
        except zipfile.BadZipFile as exc:
            infra.append({"variant": variant, "classification": "INFRA_FAILURE",
                          "reason": f"bad artifact zip: {exc}", "artifact_id": artifact_id})
            continue
        metric_paths = list(unpack.rglob("METRIC.json"))
        source_paths = list(unpack.rglob("Mock2_FunctionalAnalysis-candidate.lean"))
        if len(metric_paths) != 1 or len(source_paths) != 1:
            infra.append({"variant": variant, "classification": "INFRA_FAILURE",
                          "reason": "artifact lacks unique METRIC.json/source",
                          "artifact_id": artifact_id})
            continue
        try:
            metric = json.loads(metric_paths[0].read_text(encoding="utf-8"))
        except Exception as exc:
            infra.append({"variant": variant, "classification": "INFRA_FAILURE",
                          "reason": f"metric JSON invalid: {type(exc).__name__}: {exc}",
                          "artifact_id": artifact_id})
            continue
        data = source_paths[0].read_bytes()
        metric["_source_path"] = str(source_paths[0])
        metric["_actual_sha256"] = sha256(data)
        metric["_artifact_id"] = artifact_id
        metrics.append(metric)
    for variant in sorted(EXPECTED_VARIANTS - seen):
        infra.append({"variant": variant, "classification": "INFRA_FAILURE",
                      "reason": "candidate artifact missing from current run"})
    for variant in sorted(seen - EXPECTED_VARIANTS):
        infra.append({"variant": variant, "classification": "INFRA_FAILURE",
                      "reason": "unexpected candidate artifact"})
    return metrics, infra


def validate(metric: dict[str, Any], baseline: dict[str, Any]) -> tuple[bool, list[str]]:
    reasons: list[str] = []
    checks = {
        "metric classified INFRA_FAILURE": metric.get("classification") != "INFRA_FAILURE",
        "strict categorized diagnostic parser missing":
            metric.get("diagnostic_parser") == "strict_error_and_error_category_v1",
        "all required direct Lean commands not executed":
            metric.get("all_required_lean_executed") is True,
        "candidate FA direct Lean not executed": metric.get("FA_executed") is True,
        "source/metadata SHA mismatch": metric.get("source_metadata_identity") is True,
        "artifact source SHA mismatch": metric.get("source_sha256") == metric.get("_actual_sha256"),
        "Mock2 prerequisite failed": int(metric.get("Mock2_exit", 125)) == 0,
        "Mock2 emitted errors": int(metric.get("Mock2_errors_under_cap", 1)) == 0,
        "Mock2 Advanced prerequisite failed": int(metric.get("Mock2_Advanced_exit", 125)) == 0,
        "Mock2 Advanced emitted errors": int(metric.get("Mock2_Advanced_errors_under_cap", 1)) == 0,
        "forbidden trust audit failed": metric.get("forbidden_clean") is True,
        "authoritative theorem header changed":
            metric.get("target_header_sha256") == baseline.get("target_header_sha256"),
        "existing declaration sequence changed":
            metric.get("declaration_sequence_sha256") == baseline.get("declaration_sequence_sha256"),
    }
    for reason, ok in checks.items():
        if not ok:
            reasons.append(reason)
    reasons.extend(str(x) for x in metric.get("infra_reasons", []))
    return not reasons, reasons


def classify(metric: dict[str, Any], baseline: dict[str, Any], valid: bool) -> str:
    if not valid:
        return "INFRA_FAILURE"
    if metric.get("variant") == "baseline":
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
    same_start = int(metric.get("FA_error_declaration_start_line", 0)) == int(
        baseline.get("FA_error_declaration_start_line", -1)
    )
    baseline_pos = (int(baseline.get("FA_first_actual_error_line", 0)),
                    int(baseline.get("FA_first_actual_error_col", 0)))
    candidate_pos = (int(metric.get("FA_first_actual_error_line", 0)),
                     int(metric.get("FA_first_actual_error_col", 0)))
    if same_height and same_start and candidate_pos > baseline_pos:
        return "SMALL_SAME_DECLARATION_ADVANCE"
    if candidate_pos == baseline_pos:
        return "NO_IMPROVEMENT"
    return "NO_STRICT_PROMOTION"


def ranking(metric: dict[str, Any]) -> tuple[int, int, int, int]:
    return (
        1 if int(metric.get("FA_exit", 125)) == 0 else 0,
        int(metric.get("FA_error_declaration_index", -1)),
        int(metric.get("FA_first_actual_error_line", 0)),
        int(metric.get("FA_first_actual_error_col", 0)),
    )


def fail(reason: str, details: dict[str, Any] | None = None) -> None:
    SELECTED.mkdir(parents=True, exist_ok=True)
    result = {"classification": "SELECTOR_FAILURE", "reason": reason,
              "details": details or {}}
    (SELECTED / "SELECTOR_FAILURE.json").write_text(
        json.dumps(result, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )
    append_output({"selector_ok": False, "selection_mode": "INFRA_FAILURE"})
    raise RuntimeError(reason)


def main() -> None:
    SELECTED.mkdir(parents=True, exist_ok=True)
    metrics, infra = collect()
    if infra:
        fail("candidate artifact/direct-metric infrastructure incomplete", {"infra": infra})
    variants = [str(m.get("variant", "")) for m in metrics]
    if set(variants) != EXPECTED_VARIANTS or len(variants) != len(EXPECTED_VARIANTS):
        fail("candidate metric variants incomplete or duplicated",
             {"actual": variants, "expected": sorted(EXPECTED_VARIANTS)})
    baselines = [m for m in metrics if m.get("variant") == "baseline"]
    if len(baselines) != 1:
        fail(f"expected exactly one matrix baseline metric, found {len(baselines)}")
    baseline = baselines[0]
    baseline_ok = (
        baseline.get("source_sha256") == BASELINE_SHA
        and baseline.get("_actual_sha256") == BASELINE_SHA
        and int(baseline.get("line_count", 0)) == BASELINE_LINES
        and baseline.get("diagnostic_parser") == "strict_error_and_error_category_v1"
        and baseline.get("all_required_lean_executed") is True
        and int(baseline.get("Mock2_exit", 125)) == 0
        and int(baseline.get("Mock2_Advanced_exit", 125)) == 0
        and int(baseline.get("FA_exit", 125)) == 1
        and (int(baseline.get("FA_first_actual_error_line", 0)),
             int(baseline.get("FA_first_actual_error_col", 0))) == BASELINE_FIRST
        and baseline.get("FA_first_error_declaration") == BASELINE_DECL
        and baseline.get("forbidden_clean") is True
    )
    if not baseline_ok:
        fail("matrix baseline failed to reproduce strict categorized direct first error",
             {"baseline": baseline})

    rows: list[dict[str, Any]] = []
    eligible: list[dict[str, Any]] = []
    for metric in sorted(metrics, key=lambda row: str(row.get("variant", ""))):
        valid, reasons = validate(metric, baseline)
        classification = classify(metric, baseline, valid)
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
            "first_message": metric.get("FA_first_error_message"),
            "declaration": metric.get("FA_first_error_declaration"),
            "declaration_index": metric.get("FA_error_declaration_index"),
            "classification": classification,
            "valid_direct_metric": valid,
            "reasons": reasons,
            "artifact_id": metric.get("_artifact_id"),
        }
        rows.append(row)
        if classification in {"FA_PASS_CANDIDATE", "DECLARATION_BREAKTHROUGH",
                              "SMALL_SAME_DECLARATION_ADVANCE"}:
            eligible.append(metric)

    if eligible:
        eligible.sort(key=ranking, reverse=True)
        chosen = eligible[0]
        mode = "STRICT_PROMOTION"
    else:
        chosen = baseline
        mode = "NO_IMPROVEMENT"

    source = Path(str(chosen["_source_path"])).read_bytes()
    selected_path = SELECTED / "Mock2_FunctionalAnalysis-selected.lean"
    selected_path.write_bytes(source)
    selected_sha = sha256(source)
    if selected_sha != chosen.get("source_sha256"):
        fail("selected bytes disagree with selected direct metric")
    metadata = {
        "variant": chosen.get("variant", "baseline"),
        "baseline_sha256": BASELINE_SHA,
        "candidate_sha256": selected_sha,
        "line_count": int(chosen.get("line_count", BASELINE_LINES)),
        "target_header_sha256": chosen.get("target_header_sha256", ""),
        "declaration_sequence_sha256": chosen.get("declaration_sequence_sha256", ""),
        "baseline_forbidden_counts": baseline.get("candidate_forbidden_counts", {}),
        "candidate_forbidden_counts": chosen.get("candidate_forbidden_counts", {}),
        "repairs": chosen.get("repairs", []),
    }
    (SELECTED / "SELECTED_METADATA.json").write_text(
        json.dumps(metadata, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )
    result = {
        "classification": mode,
        "authority": "current-run strict categorized direct Lean CLI",
        "baseline": baseline,
        "chosen": chosen,
        "candidate_results": rows,
        "promotion_order": [
            "FA exit 0",
            "later declaration index",
            "same declaration only at identical file height/start: later line/column",
        ],
    }
    (SELECTED / "CANDIDATE_RESULTS.json").write_text(
        json.dumps(rows, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )
    (SELECTED / "SELECTION.json").write_text(
        json.dumps(result, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )
    print(json.dumps(result, indent=2, ensure_ascii=False))
    append_output({
        "selector_ok": True,
        "selection_mode": mode,
        "selected_sha": selected_sha,
        "variant": chosen.get("variant", "baseline"),
        "fa_exit": chosen.get("FA_exit", 125),
        "first_line": chosen.get("FA_first_actual_error_line", 0),
        "first_col": chosen.get("FA_first_actual_error_col", 0),
        "declaration": chosen.get("FA_first_error_declaration", ""),
        "declaration_index": chosen.get("FA_error_declaration_index", -1),
    })


if __name__ == "__main__":
    main()
