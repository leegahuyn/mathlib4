#!/usr/bin/env python3
from __future__ import annotations

import importlib.util
import io
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import urllib.parse
import urllib.request
import zipfile

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
OUT = ROOT / "build-logs" / "fa402-artifact-harvest"
BASE = ROOT / "scripts" / "fa400_resilient_harvest_agent.py"
TOKEN = os.environ.get("GITHUB_TOKEN", "")
REPO = os.environ.get("GITHUB_REPOSITORY", "leegahuyn/mathlib4")

spec = importlib.util.spec_from_file_location("fa400", BASE)
if spec is None or spec.loader is None:
    raise RuntimeError("cannot load PASS 400 resilient agent")
fa400 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(fa400)
fa399 = fa400.fa399
fa391 = fa400.fa391

NAME_RX = re.compile(r"(?:fa|pass)[-_ ]?(?:35[8-9]|36\d|37\d|38\d|39\d|400)", re.I)


def api(url: str) -> bytes:
    request = urllib.request.Request(
        url,
        headers={
            "Authorization": f"Bearer {TOKEN}",
            "Accept": "application/vnd.github+json",
            "X-GitHub-Api-Version": "2022-11-28",
        },
    )
    with urllib.request.urlopen(request, timeout=180) as response:
        return response.read()


def artifacts() -> list[dict[str, object]]:
    selected: list[dict[str, object]] = []
    for page in range(1, 11):
        url = f"https://api.github.com/repos/{REPO}/actions/artifacts?" + urllib.parse.urlencode(
            {"per_page": 100, "page": page}
        )
        data = json.loads(api(url))
        rows = data.get("artifacts", [])
        if not rows:
            break
        for row in rows:
            name = str(row.get("name") or "")
            if row.get("expired"):
                continue
            if NAME_RX.search(name) and any(
                key in name.lower() for key in ("functional", "frontier", "fa", "pass3")
            ):
                selected.append(row)
    selected.sort(key=lambda row: str(row.get("created_at") or ""), reverse=True)
    return selected[:35]


def compile_candidate(text: str, tag: str, headers: dict[str, str]) -> dict[str, object] | None:
    if fa391.public_headers(text) != headers:
        return None
    audit = fa391.audit_text(text)
    if any(audit.values()):
        return None
    original = TARGET.read_text(encoding="utf-8")
    TARGET.write_text(text, encoding="utf-8")
    try:
        metric = fa391.compile_file(TARGET, tag, max_errors=16)
    finally:
        TARGET.write_text(original, encoding="utf-8")
    return metric


def metric_key(metric: dict[str, object]) -> tuple[int, int, int]:
    return (
        1 if int(metric["exit_code"]) == 0 else 0,
        int(metric["first_line"]),
        -int(metric["errors"]),
    )


def main() -> int:
    if not TOKEN:
        raise RuntimeError("GITHUB_TOKEN is required")
    OUT.mkdir(parents=True, exist_ok=True)
    current_text = TARGET.read_text(encoding="utf-8")
    headers = fa391.public_headers(current_text)
    baseline = fa391.compile_file(TARGET, "fa402-baseline", max_errors=16)
    best_text = current_text
    best_metric = baseline
    manifest: dict[str, object] = {
        "baseline": baseline,
        "artifacts": [],
        "candidates": [],
    }
    scratch = Path("/tmp/fa402-artifacts")
    shutil.rmtree(scratch, ignore_errors=True)
    scratch.mkdir(parents=True, exist_ok=True)
    seen_sha: set[str] = {fa391.sha(TARGET)}
    candidate_count = 0
    for row in artifacts():
        artifact_id = int(row["id"])
        name = str(row["name"])
        entry = {"id": artifact_id, "name": name, "created_at": row.get("created_at")}
        manifest["artifacts"].append(entry)
        try:
            raw = api(f"https://api.github.com/repos/{REPO}/actions/artifacts/{artifact_id}/zip")
            with zipfile.ZipFile(io.BytesIO(raw)) as archive:
                names = archive.namelist()
                for member in names:
                    lower = member.lower()
                    if not lower.endswith(".lean") or "mock2_functionalanalysis" not in lower.replace("-", "_"):
                        continue
                    data = archive.read(member)
                    try:
                        text = data.decode("utf-8")
                    except UnicodeDecodeError:
                        continue
                    digest = __import__("hashlib").sha256(data).hexdigest()
                    if digest in seen_sha:
                        continue
                    seen_sha.add(digest)
                    candidate_count += 1
                    if candidate_count > 45:
                        break
                    metric = compile_candidate(text, f"fa402-a{artifact_id}-c{candidate_count}", headers)
                    record = {
                        "artifact_id": artifact_id,
                        "artifact_name": name,
                        "member": member,
                        "sha256": digest,
                        "metric": metric,
                    }
                    manifest["candidates"].append(record)
                    if metric is not None and metric_key(metric) > metric_key(best_metric):
                        best_metric = metric
                        best_text = text
                if candidate_count > 45:
                    break
        except Exception as exc:
            entry["error"] = f"{type(exc).__name__}: {exc}"
    TARGET.write_text(best_text, encoding="utf-8")
    manifest["selected_metric"] = best_metric
    manifest["selected_sha256"] = fa391.sha(TARGET)
    manifest["candidate_count"] = candidate_count
    (OUT / "selection.json").write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({
        "baseline": baseline,
        "selected": best_metric,
        "selected_sha256": manifest["selected_sha256"],
        "candidate_count": candidate_count,
    }, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
