#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import json
import os
import subprocess
import zipfile
from pathlib import Path

ROOT = Path.cwd()
REPO = os.environ.get("GITHUB_REPOSITORY", "leegahuyn/mathlib4")
RUN_ID = int(os.environ["GITHUB_RUN_ID"])
BASELINE_SHA = "71dc36f16ebea92d537aa40a5d420443e4bcb93ccb76fea31efb40a6cb5c3aa0"
BASELINE_LINE = 31726
EXPECTED_LINES = 60453
COLLECTED = ROOT / "build-logs/fa442-same-height/collected"
SELECTED = ROOT / "build-logs/fa442-same-height/selected"


def run(args: list[str], *, text: bool = True, stdout=None, stderr=None):
    return subprocess.run(
        args,
        cwd=ROOT,
        text=text,
        stdout=stdout,
        stderr=stderr,
        check=False,
    )


def sha_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


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


def action_artifacts() -> list[dict]:
    proc = run(
        [
            "gh",
            "api",
            "--paginate",
            f"/repos/{REPO}/actions/runs/{RUN_ID}/artifacts?per_page=100",
        ],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if proc.returncode != 0:
        raise RuntimeError(proc.stderr)
    result: list[dict] = []
    for page in decode_pages(proc.stdout):
        if isinstance(page, dict):
            result.extend(page.get("artifacts", []))
        elif isinstance(page, list):
            result.extend(item for item in page if isinstance(item, dict))
    return result


def collect() -> list[dict]:
    COLLECTED.mkdir(parents=True, exist_ok=True)
    collected: list[dict] = []
    for artifact in action_artifacts():
        name = str(artifact.get("name", ""))
        if not name.startswith("fa442-candidate-") or artifact.get("expired"):
            continue
        artifact_id = int(artifact["id"])
        variant = name.removeprefix("fa442-candidate-")
        zip_path = Path("/tmp") / f"fa442-{artifact_id}.zip"
        unpack = COLLECTED / variant
        unpack.mkdir(parents=True, exist_ok=True)
        with zip_path.open("wb") as handle:
            proc = run(
                ["gh", "api", f"/repos/{REPO}/actions/artifacts/{artifact_id}/zip"],
                text=False,
                stdout=handle,
                stderr=subprocess.PIPE,
            )
        row = {
            "artifact_id": artifact_id,
            "name": name,
            "variant": variant,
            "download_exit": proc.returncode,
        }
        collected.append(row)
        if proc.returncode != 0:
            continue
        try:
            with zipfile.ZipFile(zip_path) as archive:
                archive.extractall(unpack)
        except zipfile.BadZipFile:
            row["bad_zip"] = True
    (COLLECTED / "ARTIFACTS.json").write_text(
        json.dumps(collected, indent=2) + "\n", encoding="utf-8"
    )
    return collected


def load_metrics() -> list[dict]:
    metrics: list[dict] = []
    for metric_path in COLLECTED.rglob("METRIC.json"):
        try:
            metric = json.loads(metric_path.read_text(encoding="utf-8"))
        except Exception:
            continue
        source_candidates = list(metric_path.parent.glob("*candidate.lean"))
        if not source_candidates:
            source_candidates = list(metric_path.parent.glob("Mock2_FunctionalAnalysis-candidate.lean"))
        if not source_candidates:
            continue
        source_path = source_candidates[0]
        data = source_path.read_bytes()
        metric["_metric_path"] = str(metric_path)
        metric["_source_path"] = str(source_path)
        metric["_actual_sha256"] = sha_bytes(data)
        metrics.append(metric)
    return metrics


def common_valid(metric: dict, header_sha: str) -> bool:
    return (
        metric.get("classification") == "VERIFIED"
        and metric.get("authority") == "direct Lean CLI on repository source path"
        and metric.get("source_metadata_identity") is True
        and metric.get("source_sha256") == metric.get("_actual_sha256")
        and metric.get("line_count") == EXPECTED_LINES
        and metric.get("target_header_sha256") == header_sha
        and metric.get("Mock2_exit") == 0
        and metric.get("Mock2_errors_under_cap") == 0
        and metric.get("Mock2_Advanced_exit") == 0
        and metric.get("Mock2_Advanced_errors_under_cap") == 0
        and metric.get("forbidden_not_increased") is True
        and metric.get("forbidden_clean") is True
    )


def main() -> None:
    collect()
    metrics = load_metrics()
    baseline_metrics = [
        metric for metric in metrics if metric.get("variant") == "baseline"
    ]
    if len(baseline_metrics) != 1:
        raise RuntimeError(
            f"expected one baseline direct metric, found {len(baseline_metrics)}"
        )
    baseline = baseline_metrics[0]
    header_sha = str(baseline.get("target_header_sha256", ""))
    baseline_valid = (
        common_valid(baseline, header_sha)
        and baseline.get("source_sha256") == BASELINE_SHA
        and baseline.get("FA_exit") == 1
        and int(baseline.get("FA_first_actual_error_line", 0)) == BASELINE_LINE
    )
    if not baseline_valid:
        raise RuntimeError(
            "exact PASS423 baseline did not reproduce under direct Lean CLI"
        )

    eligible = [
        metric
        for metric in metrics
        if common_valid(metric, header_sha)
        and metric.get("source_sha256") != BASELINE_SHA
        and (
            metric.get("FA_exit") == 0
            or int(metric.get("FA_first_actual_error_line", 0)) > BASELINE_LINE
        )
    ]
    if eligible:
        eligible.sort(
            key=lambda metric: (
                metric.get("FA_exit") == 0,
                int(metric.get("FA_first_actual_error_line", 0)),
                int(metric.get("FA_error_declaration_index", -1)),
                int(metric.get("FA_first_actual_error_col", 0)),
            ),
            reverse=True,
        )
        chosen = eligible[0]
        mode = "strict_promotion"
    else:
        chosen = baseline
        mode = "retain_verified_baseline"

    SELECTED.mkdir(parents=True, exist_ok=True)
    source_path = Path(chosen["_source_path"])
    selected_source = SELECTED / "Mock2_FunctionalAnalysis-selected.lean"
    selected_source.write_bytes(source_path.read_bytes())
    result = {
        "classification": "CANDIDATE",
        "authority_required": "independent direct Lean CLI confirmation",
        "selection_mode": mode,
        "baseline": baseline,
        "chosen": chosen,
        "eligible_strict_candidates": len(eligible),
        "all_direct_metrics": metrics,
        "promotion_rule": (
            "checked source SHA identity, 60453 lines, identical theorem header, "
            "Mock2 and Mock2_Advanced clean, forbidden audit clean, then FA exit0 "
            "or first actual error line strictly greater than 31726"
        ),
    }
    (SELECTED / "SELECTION.json").write_text(
        json.dumps(result, indent=2) + "\n", encoding="utf-8"
    )
    print(json.dumps(result, indent=2))
    output = os.environ.get("GITHUB_OUTPUT")
    if output:
        with open(output, "a", encoding="utf-8") as handle:
            handle.write(f"selection_mode={mode}\n")
            handle.write(f"selected_sha={chosen['source_sha256']}\n")
            handle.write(f"variant={chosen['variant']}\n")
            handle.write(f"matrix_fa_exit={chosen['FA_exit']}\n")
            handle.write(
                f"matrix_first_line={chosen['FA_first_actual_error_line']}\n"
            )
            handle.write(
                f"matrix_first_col={chosen['FA_first_actual_error_col']}\n"
            )
            handle.write(
                f"matrix_declaration={chosen['FA_first_error_declaration']}\n"
            )


if __name__ == "__main__":
    main()
