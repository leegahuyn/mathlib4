from __future__ import annotations

import hashlib
import json
import os
import shutil
import subprocess
import zipfile
from pathlib import Path

from fa442_pipeline_common import (
    BASELINE_LINE_COUNT,
    BASELINE_SHA256,
    BLOCKER,
    REPO,
    source_metadata,
    write_json,
)

REPOSITORY = os.environ.get("GITHUB_REPOSITORY", "leegahuyn/mathlib4")
OUT = REPO / "build-logs/fa442-exact-baseline-recovery"
RUN_IDS = (31317392557, 31345045760)


def gh_json(endpoint: str):
    cp = subprocess.run(
        ["gh", "api", "-H", "Accept: application/vnd.github+json", endpoint],
        cwd=REPO, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        text=True, check=True,
    )
    return json.loads(cp.stdout)


def scan(root: Path, matches: list[dict]) -> None:
    for path in root.rglob("*"):
        try:
            if not path.is_file() or path.stat().st_size < 100_000:
                continue
            data = path.read_bytes()
            if f"theorem {BLOCKER}".encode() not in data:
                continue
            sha = hashlib.sha256(data).hexdigest()
            if sha == BASELINE_SHA256:
                matches.append({"path": str(path), "data": data})
        except Exception:
            continue


def main() -> None:
    if OUT.exists():
        shutil.rmtree(OUT)
    OUT.mkdir(parents=True)
    matches: list[dict] = []
    manifest: list[dict] = []
    for run_id in RUN_IDS:
        payload = gh_json(
            f"/repos/{REPOSITORY}/actions/runs/{run_id}/artifacts?per_page=100"
        )
        for artifact in payload.get("artifacts", []):
            artifact_id = int(artifact["id"])
            target = OUT / "artifacts" / f"{run_id}-{artifact_id}"
            target.mkdir(parents=True, exist_ok=True)
            zip_path = target / "artifact.zip"
            try:
                with zip_path.open("wb") as fh:
                    subprocess.run(
                        [
                            "gh", "api", "-H", "Accept: application/vnd.github+json",
                            f"/repos/{REPOSITORY}/actions/artifacts/{artifact_id}/zip",
                        ],
                        cwd=REPO, stdout=fh, stderr=subprocess.PIPE, check=True,
                    )
                with zipfile.ZipFile(zip_path) as archive:
                    archive.extractall(target / "content")
                zip_path.unlink(missing_ok=True)
                scan(target / "content", matches)
                status = "downloaded_and_scanned"
            except Exception as exc:
                status = f"failure: {exc!r}"
            manifest.append({
                "run_id": run_id,
                "artifact_id": artifact_id,
                "artifact_name": artifact.get("name"),
                "expired": artifact.get("expired"),
                "status": status,
            })

    # Fallback: targeted branch contents, never a wildcard all-ref fetch.
    if not matches:
        page = 1
        while True:
            branches = gh_json(f"/repos/{REPOSITORY}/branches?per_page=100&page={page}")
            if not branches:
                break
            for row in branches:
                name = str(row.get("name", ""))
                if not any(token in name.lower() for token in (
                    "fa423", "fa424", "fa442", "functional", "clean-build"
                )):
                    continue
                cp = subprocess.run(
                    [
                        "gh", "api", "-H", "Accept: application/vnd.github.raw+json",
                        f"/repos/{REPOSITORY}/contents/PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean?ref={name}",
                    ],
                    cwd=REPO, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
                    check=False,
                )
                if cp.returncode == 0 and hashlib.sha256(cp.stdout).hexdigest() == BASELINE_SHA256:
                    matches.append({"path": f"branch:{name}", "data": cp.stdout})
            if len(branches) < 100:
                break
            page += 1

    unique = {hashlib.sha256(x["data"]).hexdigest(): x for x in matches}
    if list(unique) != [BASELINE_SHA256]:
        raise RuntimeError(
            f"expected exact baseline content {BASELINE_SHA256}; unique matches={list(unique)}"
        )
    data = unique[BASELINE_SHA256]["data"]
    meta = source_metadata(data)
    if meta["line_count"] != BASELINE_LINE_COUNT:
        raise RuntimeError(f"baseline line count mismatch: {meta['line_count']}")
    (OUT / "source.lean").write_bytes(data)
    meta.update({
        "expected_sha256": BASELINE_SHA256,
        "expected_line_count": BASELINE_LINE_COUNT,
        "origins": [x["path"] for x in matches],
        "run_ids_scanned": list(RUN_IDS),
    })
    write_json(OUT / "metadata.json", meta)
    write_json(OUT / "artifact-manifest.json", manifest)
    print(json.dumps(meta, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
