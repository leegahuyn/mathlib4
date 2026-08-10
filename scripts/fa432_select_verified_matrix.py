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
EXPECTED_ARTIFACTS = 10
COLLECTED = ROOT / "build-logs/fa432-scoped-instance-matrix/collected"
SELECTED = ROOT / "build-logs/fa432-scoped-instance-matrix/selected"


def run(args: list[str], *, text: bool = True, stdout=None, stderr=None):
    return subprocess.run(
        args, cwd=ROOT, text=text, stdout=stdout, stderr=stderr, check=False
    )


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def pages(endpoint: str):
    proc = run(
        ["gh", "api", "--paginate", endpoint],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if proc.returncode != 0:
        raise RuntimeError(proc.stderr)
    raw = proc.stdout.strip()
    if not raw:
        return []
    try:
        return [json.loads(raw)]
    except json.JSONDecodeError:
        decoder = json.JSONDecoder()
        result = []
        i = 0
        while i < len(raw):
            while i < len(raw) and raw[i].isspace():
                i += 1
            if i >= len(raw):
                break
            obj, i = decoder.raw_decode(raw, i)
            result.append(obj)
        return result


def action_artifacts() -> list[dict]:
    result: list[dict] = []
    for page in pages(f"/repos/{REPO}/actions/runs/{RUN_ID}/artifacts?per_page=100"):
        if isinstance(page, dict):
            result.extend(page.get("artifacts", []))
        elif isinstance(page, list):
            result.extend(item for item in page if isinstance(item, dict))
    return result


def collect() -> list[dict]:
    COLLECTED.mkdir(parents=True, exist_ok=True)
    rows: list[dict] = []
    for artifact in action_artifacts():
        name = str(artifact.get("name", ""))
        if not name.startswith("fa432-candidate-") or artifact.get("expired"):
            continue
        artifact_id = int(artifact["id"])
        variant = name.removeprefix("fa432-candidate-")
        zip_path = Path("/tmp") / f"fa432-{artifact_id}.zip"
        unpack = COLLECTED / variant
        unpack.mkdir(parents=True, exist_ok=True)
        with zip_path.open("wb") as handle:
            proc = run(
                ["gh", "api", f"/repos/{REPO}/actions/artifacts/{artifact_id}/zip"],
                text=False,
                stdout=handle,
                stderr=subprocess.PIPE,
            )
        if proc.returncode != 0:
            continue
        with zipfile.ZipFile(zip_path) as archive:
            archive.extractall(unpack)
        rows.append(
            {"artifact_id": artifact_id, "name": name, "variant": variant}
        )
    (COLLECTED / "ARTIFACTS.json").write_text(
        json.dumps(rows, indent=2) + "\n", encoding="utf-8"
    )
    if len(rows) != EXPECTED_ARTIFACTS:
        raise RuntimeError(
            f"expected {EXPECTED_ARTIFACTS} candidate artifacts, collected {len(rows)}"
        )
    return rows


def load_metrics() -> list[dict]:
    result: list[dict] = []
    for metric_path in COLLECTED.glob("*/METRIC.json"):
        try:
            metric = json.loads(metric_path.read_text(encoding="utf-8"))
        except Exception:
            continue
        source_path = metric_path.parent / "Mock2_FunctionalAnalysis-candidate.lean"
        if not source_path.exists():
            continue
        metric["_metric_path"] = str(metric_path)
        metric["_source_path"] = str(source_path)
        metric["_actual_sha256"] = sha(source_path.read_bytes())
        result.append(metric)
    return result


def common_valid(metric: dict, header_sha: str) -> bool:
    return (
        metric.get("classification") == "VERIFIED"
        and metric.get("authority") == "direct Lean CLI"
        and metric.get("source_metadata_identity") is True
        and metric.get("source_sha256") == metric.get("_actual_sha256")
        and metric.get("line_count") == EXPECTED_LINES
        and metric.get("target_header_sha256") == header_sha
        and metric.get("Mock2_exit") == 0
        and metric.get("Mock2_errors") == 0
        and metric.get("Mock2_Advanced_exit") == 0
        and metric.get("Mock2_Advanced_errors") == 0
    )


def main() -> None:
    collect()
    metrics = load_metrics()
    baseline = [metric for metric in metrics if metric.get("variant") == "baseline"]
    if len(baseline) != 1:
        raise RuntimeError(f"expected one baseline metric, found {len(baseline)}")
    baseline_metric = baseline[0]
    header_sha = str(baseline_metric.get("target_header_sha256", ""))
    baseline_ok = (
        common_valid(baseline_metric, header_sha)
        and baseline_metric.get("source_sha256") == BASELINE_SHA
        and (
            baseline_metric.get("FA_exit") == 0
            or int(baseline_metric.get("FA_first_error_line", 0)) >= BASELINE_LINE
        )
    )
    if not baseline_ok:
        raise RuntimeError("exact PASS423 baseline did not reproduce")

    eligible = [
        metric
        for metric in metrics
        if common_valid(metric, header_sha)
        and metric.get("source_sha256") != BASELINE_SHA
        and (
            metric.get("FA_exit") == 0
            or int(metric.get("FA_first_error_line", 0)) > BASELINE_LINE
        )
    ]
    if eligible:
        eligible.sort(
            key=lambda metric: (
                metric.get("FA_exit") == 0,
                int(metric.get("FA_first_error_line", 0)),
                int(metric.get("FA_first_error_col", 0)),
            ),
            reverse=True,
        )
        chosen = eligible[0]
        mode = "strict_promotion"
    else:
        chosen = baseline_metric
        mode = "materialize_verified_baseline"

    SELECTED.mkdir(parents=True, exist_ok=True)
    chosen_source = Path(chosen["_source_path"])
    (SELECTED / "Mock2_FunctionalAnalysis-selected.lean").write_bytes(
        chosen_source.read_bytes()
    )
    result = {
        "classification": "CANDIDATE",
        "authority_required": "direct Lean CLI confirmation",
        "selection_mode": mode,
        "baseline": baseline_metric,
        "chosen": chosen,
        "eligible_strict_candidates": len(eligible),
        "all_metrics": metrics,
        "promotion_rule": (
            "same 60453-line file and identical target theorem header; "
            "FA exit 0 or first actual error line strictly greater than 31726"
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
            handle.write(f"matrix_fa_exit={chosen['FA_exit']}\n")
            handle.write(
                f"matrix_first_line={chosen['FA_first_error_line']}\n"
            )
            handle.write(f"matrix_first_col={chosen['FA_first_error_col']}\n")
            handle.write(f"variant={chosen['variant']}\n")


if __name__ == "__main__":
    main()
