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
COLLECTED = ROOT / "build-logs/fa428-cumulative-matrix/collected"
SELECTED = ROOT / "build-logs/fa428-cumulative-matrix/selected"


def run(args: list[str], *, text: bool = True, stdout=None, stderr=None):
    return subprocess.run(args, cwd=ROOT, text=text, stdout=stdout, stderr=stderr, check=False)


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def gh_pages(endpoint: str):
    p = run(["gh", "api", "--paginate", endpoint], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    if p.returncode != 0:
        raise RuntimeError(p.stderr)
    raw = p.stdout.strip()
    if not raw:
        return []
    try:
        return [json.loads(raw)]
    except json.JSONDecodeError:
        dec = json.JSONDecoder(); i = 0; pages = []
        while i < len(raw):
            while i < len(raw) and raw[i].isspace(): i += 1
            if i >= len(raw): break
            obj, i = dec.raw_decode(raw, i); pages.append(obj)
        return pages


def artifacts() -> list[dict]:
    result = []
    for page in gh_pages(f"/repos/{REPO}/actions/runs/{RUN_ID}/artifacts?per_page=100"):
        if isinstance(page, dict): result.extend(page.get("artifacts", []))
        elif isinstance(page, list): result.extend(x for x in page if isinstance(x, dict))
    return result


def collect() -> list[dict]:
    COLLECTED.mkdir(parents=True, exist_ok=True)
    rows = []
    for art in artifacts():
        name = str(art.get("name", ""))
        if not name.startswith("fa428-candidate-") or art.get("expired"):
            continue
        aid = int(art["id"]); variant = name.removeprefix("fa428-candidate-")
        z = Path("/tmp") / f"fa428-{aid}.zip"; d = COLLECTED / variant
        d.mkdir(parents=True, exist_ok=True)
        with z.open("wb") as h:
            p = run(["gh", "api", f"/repos/{REPO}/actions/artifacts/{aid}/zip"], text=False, stdout=h, stderr=subprocess.PIPE)
        if p.returncode != 0:
            continue
        with zipfile.ZipFile(z) as ar:
            ar.extractall(d)
        rows.append({"artifact_id": aid, "name": name, "variant": variant})
    (COLLECTED / "ARTIFACTS.json").write_text(json.dumps(rows, indent=2) + "\n")
    if len(rows) != 9:
        raise RuntimeError(f"expected 9 candidate artifacts, collected {len(rows)}")
    return rows


def load_metrics() -> list[dict]:
    rows = []
    for p in COLLECTED.glob("*/METRIC.json"):
        try:
            metric = json.loads(p.read_text())
        except Exception:
            continue
        source = p.parent / "Mock2_FunctionalAnalysis-candidate.lean"
        if not source.exists():
            continue
        data = source.read_bytes()
        metric["_metric_path"] = str(p)
        metric["_source_path"] = str(source)
        metric["_actual_sha256"] = sha(data)
        rows.append(metric)
    return rows


def valid_common(r: dict, header: str) -> bool:
    return (
        r.get("source_metadata_identity") is True
        and r.get("source_sha256") == r.get("_actual_sha256")
        and r.get("line_count") == EXPECTED_LINES
        and r.get("target_header_sha256") == header
        and r.get("Mock2_exit") == 0
        and r.get("Mock2_errors") == 0
        and r.get("Mock2_Advanced_exit") == 0
        and r.get("Mock2_Advanced_errors") == 0
    )


def main() -> None:
    collect()
    rows = load_metrics()
    baseline = [r for r in rows if r.get("variant") == "baseline"]
    if len(baseline) != 1:
        raise RuntimeError(f"expected one baseline metric, found {len(baseline)}")
    b = baseline[0]
    header = str(b.get("target_header_sha256", ""))
    baseline_ok = (
        valid_common(b, header)
        and b.get("source_sha256") == BASELINE_SHA
        and (b.get("FA_exit") == 0 or int(b.get("FA_first_error_line", 0)) >= BASELINE_LINE)
    )
    if not baseline_ok:
        raise RuntimeError("exact PASS423 baseline did not reproduce")
    eligible = [
        r for r in rows
        if valid_common(r, header)
        and r.get("source_sha256") != BASELINE_SHA
        and (r.get("FA_exit") == 0 or int(r.get("FA_first_error_line", 0)) > BASELINE_LINE)
    ]
    if eligible:
        eligible.sort(
            key=lambda r: (
                r.get("FA_exit") == 0,
                int(r.get("FA_first_error_line", 0)),
                int(r.get("FA_first_error_col", 0)),
            ),
            reverse=True,
        )
        chosen = eligible[0]
        mode = "strict_promotion"
    else:
        chosen = b
        mode = "materialize_verified_baseline"
    SELECTED.mkdir(parents=True, exist_ok=True)
    source = Path(chosen["_source_path"])
    (SELECTED / "Mock2_FunctionalAnalysis-selected.lean").write_bytes(source.read_bytes())
    result = {
        "classification": "CANDIDATE",
        "authority_required": "direct Lean CLI confirmation",
        "selection_mode": mode,
        "baseline": b,
        "chosen": chosen,
        "eligible_strict_candidates": len(eligible),
        "all_metrics": rows,
        "promotion_rule": "FA exit 0 or first actual error line > 31726; same 60453 lines and exact target header",
    }
    (SELECTED / "SELECTION.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
    output = os.environ.get("GITHUB_OUTPUT")
    if output:
        with open(output, "a", encoding="utf-8") as h:
            h.write(f"selection_mode={mode}\n")
            h.write(f"selected_sha={chosen['source_sha256']}\n")
            h.write(f"matrix_fa_exit={chosen['FA_exit']}\n")
            h.write(f"matrix_first_line={chosen['FA_first_error_line']}\n")
            h.write(f"matrix_first_col={chosen['FA_first_error_col']}\n")
            h.write(f"variant={chosen['variant']}\n")


if __name__ == "__main__":
    main()
