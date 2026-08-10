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
BASE = ROOT / "build-logs/fa452-compact-energy"
COLLECTED = BASE / "collected"
SELECTED = BASE / "selected"
REPOSITORY = os.environ["GITHUB_REPOSITORY"]
RUN_ID = int(os.environ["GITHUB_RUN_ID"])
PREFIX = "fa452-candidate-"
ROOT_SHA = "1243b2ba563d364a6977cbf9aa867e628de50a28b0f56677dc70456a210e209a"
ROOT_LINE = 33624
ROOT_COL = 57
ROOT_DECL = "selectedCuspRestrictionRepresentative_add"
ROOT_DECL_INDEX = 2720
EXPECTED_VARIANTS = {
    "root_baseline",
    "simpa_norm",
    "change_norm",
    "rw_simpa_norm",
    "simpa_norm_compact_pow",
    "change_norm_compact_pow",
    "simpa_norm_compact_mulleft",
    "simpa_norm_compact_convert",
    "rw_simpa_norm_compact_pow",
    "simpa_norm_compact_mono",
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


def decode_pages(raw: str) -> list[Any]:
    decoder = json.JSONDecoder()
    pos = 0
    pages: list[Any] = []
    while pos < len(raw):
        while pos < len(raw) and raw[pos].isspace():
            pos += 1
        if pos >= len(raw):
            break
        value, pos = decoder.raw_decode(raw, pos)
        pages.append(value)
    return pages


def list_artifacts() -> list[dict[str, Any]]:
    proc = run([
        "gh",
        "api",
        "--paginate",
        f"/repos/{REPOSITORY}/actions/runs/{RUN_ID}/artifacts?per_page=100",
    ])
    if proc.returncode != 0:
        raise RuntimeError(f"cannot list artifacts: {proc.stderr}")
    result: list[dict[str, Any]] = []
    for page in decode_pages(proc.stdout):
        if isinstance(page, dict):
            result.extend(x for x in page.get("artifacts", []) if isinstance(x, dict))
    return result


def collect() -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    if COLLECTED.exists():
        import shutil
        shutil.rmtree(COLLECTED)
    COLLECTED.mkdir(parents=True, exist_ok=True)
    metrics: list[dict[str, Any]] = []
    infra: list[dict[str, Any]] = []
    seen: set[str] = set()
    artifact_rows: list[dict[str, Any]] = []

    for artifact in list_artifacts():
        name = str(artifact.get("name", ""))
        if not name.startswith(PREFIX) or artifact.get("expired"):
            continue
        variant = name.removeprefix(PREFIX)
        seen.add(variant)
        artifact_id = int(artifact["id"])
        zip_path = Path("/tmp") / f"fa452-{artifact_id}.zip"
        unpack = COLLECTED / variant
        unpack.mkdir(parents=True, exist_ok=True)
        with zip_path.open("wb") as handle:
            proc = subprocess.run(
                ["gh", "api", f"/repos/{REPOSITORY}/actions/artifacts/{artifact_id}/zip"],
                cwd=ROOT,
                check=False,
                stdout=handle,
                stderr=subprocess.PIPE,
            )
        row = {
            "variant": variant,
            "artifact_id": artifact_id,
            "artifact_name": name,
            "download_exit": proc.returncode,
        }
        artifact_rows.append(row)
        if proc.returncode != 0:
            infra.append({**row, "reason": "artifact download failed"})
            continue
        try:
            with zipfile.ZipFile(zip_path) as archive:
                archive.extractall(unpack)
        except zipfile.BadZipFile as exc:
            infra.append({**row, "reason": f"bad zip: {exc}"})
            continue
        metric_paths = list(unpack.rglob("METRIC.json"))
        source_paths = list(unpack.rglob("Mock2_FunctionalAnalysis-candidate.lean"))
        if len(metric_paths) != 1 or len(source_paths) != 1:
            infra.append({
                **row,
                "reason": "artifact lacks unique METRIC.json and candidate source",
                "metric_count": len(metric_paths),
                "source_count": len(source_paths),
            })
            continue
        try:
            metric = json.loads(metric_paths[0].read_text(encoding="utf-8"))
        except Exception as exc:
            infra.append({**row, "reason": f"invalid metric JSON: {exc}"})
            continue
        source_data = source_paths[0].read_bytes()
        metric["_source_path"] = str(source_paths[0])
        metric["_metric_path"] = str(metric_paths[0])
        metric["_artifact_id"] = artifact_id
        metric["_actual_sha256"] = sha256(source_data)
        metrics.append(metric)

    for variant in sorted(EXPECTED_VARIANTS - seen):
        infra.append({"variant": variant, "reason": "current-run artifact missing"})
    for variant in sorted(seen - EXPECTED_VARIANTS):
        infra.append({"variant": variant, "reason": "unexpected current-run artifact"})
    (COLLECTED / "ARTIFACTS.json").write_text(
        json.dumps(artifact_rows, indent=2) + "\n", encoding="utf-8"
    )
    return metrics, infra


def valid(metric: dict[str, Any], baseline: dict[str, Any]) -> tuple[bool, list[str]]:
    reasons: list[str] = []
    checks = {
        "direct Lean CLI not executed": metric.get("all_required_lean_executed") is True,
        "source SHA differs from artifact bytes": metric.get("source_sha256") == metric.get("_actual_sha256"),
        "source/metadata SHA mismatch": metric.get("source_metadata_identity") is True,
        "Mock2 direct prerequisite failed": int(metric.get("Mock2_exit", 125)) == 0,
        "Mock2 direct prerequisite reported errors": int(metric.get("Mock2_errors_under_cap", 1)) == 0,
        "Mock2 Advanced direct prerequisite failed": int(metric.get("Mock2_Advanced_exit", 125)) == 0,
        "Mock2 Advanced direct prerequisite reported errors": int(metric.get("Mock2_Advanced_errors_under_cap", 1)) == 0,
        "FA direct Lean CLI missing": metric.get("FA_executed") is True,
        "forbidden audit failed": metric.get("forbidden_clean") is True,
        "blocker theorem header changed": metric.get("target_header_sha256") == baseline.get("target_header_sha256"),
        "declaration sequence changed": metric.get("declaration_sequence_sha256") == baseline.get("declaration_sequence_sha256"),
    }
    for reason, ok in checks.items():
        if not ok:
            reasons.append(reason)
    if metric.get("classification") == "INFRA_FAILURE":
        reasons.extend(str(x) for x in metric.get("infra_reasons", []))
    return not reasons, reasons


def classify(metric: dict[str, Any], baseline: dict[str, Any], ok: bool) -> str:
    if not ok:
        return "INFRA_FAILURE"
    if metric.get("variant") == "root_baseline":
        return "BASELINE"
    if int(metric.get("FA_exit", 125)) == 0:
        return "FA_PASS_CANDIDATE"
    message = str(metric.get("FA_first_error_message", "")).lower()
    if any(marker in message for marker in SYNTAX_MARKERS):
        return "LEAN_SYNTAX_REGRESSION"
    bidx = int(baseline.get("FA_error_declaration_index", -1))
    cidx = int(metric.get("FA_error_declaration_index", -1))
    if cidx > bidx:
        return "DECLARATION_BREAKTHROUGH"
    if cidx < bidx:
        return "REGRESSION"
    same_height = int(metric.get("line_count", 0)) == int(baseline.get("line_count", -1))
    same_decl_start = int(metric.get("FA_error_declaration_start_line", 0)) == int(
        baseline.get("FA_error_declaration_start_line", -1)
    )
    bpos = (
        int(baseline.get("FA_first_actual_error_line", 0)),
        int(baseline.get("FA_first_actual_error_col", 0)),
    )
    cpos = (
        int(metric.get("FA_first_actual_error_line", 0)),
        int(metric.get("FA_first_actual_error_col", 0)),
    )
    if same_height and same_decl_start and cpos > bpos:
        return "SMALL_SAME_DECLARATION_ADVANCE"
    if same_height and same_decl_start and cpos == bpos:
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
        result = {
            "classification": "SELECTOR_FAILURE",
            "reason": "incomplete current-run direct matrix",
            "infrastructure": infrastructure,
        }
        (SELECTED / "SELECTOR_FAILURE.json").write_text(
            json.dumps(result, indent=2) + "\n", encoding="utf-8"
        )
        append_output({"selector_ok": False, "selection_mode": "INFRA_FAILURE"})
        raise RuntimeError(json.dumps(result))

    variants = [str(m.get("variant", "")) for m in metrics]
    if set(variants) != EXPECTED_VARIANTS or len(variants) != len(EXPECTED_VARIANTS):
        raise RuntimeError(f"metric variants incomplete or duplicated: {variants}")
    baselines = [m for m in metrics if m.get("variant") == "root_baseline"]
    if len(baselines) != 1:
        raise RuntimeError(f"expected exactly one root baseline metric, found {len(baselines)}")
    baseline = baselines[0]
    baseline_ok = (
        baseline.get("all_required_lean_executed") is True
        and baseline.get("source_sha256") == ROOT_SHA
        and int(baseline.get("Mock2_exit", 125)) == 0
        and int(baseline.get("Mock2_Advanced_exit", 125)) == 0
        and int(baseline.get("FA_exit", 125)) == 1
        and int(baseline.get("FA_first_actual_error_line", 0)) == ROOT_LINE
        and int(baseline.get("FA_first_actual_error_col", 0)) == ROOT_COL
        and baseline.get("FA_first_error_declaration") == ROOT_DECL
        and int(baseline.get("FA_error_declaration_index", -1)) == ROOT_DECL_INDEX
        and baseline.get("forbidden_clean") is True
    )
    if not baseline_ok:
        raise RuntimeError("root baseline did not reproduce 33624:57 direct Lean frontier")

    rows: list[dict[str, Any]] = []
    eligible: list[dict[str, Any]] = []
    for metric in sorted(metrics, key=lambda x: str(x.get("variant", ""))):
        ok, reasons = valid(metric, baseline)
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
        "authority": "current-run direct Lean CLI metrics only",
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
        "variant": chosen.get("variant", "root_baseline"),
        "selected_sha": chosen.get("source_sha256", ""),
        "fa_exit": chosen.get("FA_exit", 125),
        "first_line": chosen.get("FA_first_actual_error_line", 0),
        "first_col": chosen.get("FA_first_actual_error_col", 0),
        "declaration": chosen.get("FA_first_error_declaration", ""),
        "declaration_index": chosen.get("FA_error_declaration_index", -1),
    })
    print(json.dumps(result, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
