#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
from pathlib import Path
from typing import Any

SOURCE_PATH = "PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean"
KNOWN = {
    "07f6efd3309c3cc23b86adf5811918b752b72c33a3f7a76213ce9beb10796da4": (0, 31725, 2),
    "71dc36f16ebea92d537aa40a5d420443e4bcb93ccb76fea31efb40a6cb5c3aa0": (0, 31726, 2),
}


def git_bytes(ref: str, path: str) -> bytes | None:
    p = subprocess.run(["git", "show", f"{ref}:{path}"], stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
    return p.stdout if p.returncode == 0 else None


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def source_metric(status: dict[str, Any]) -> tuple[int, int, int] | None:
    if status.get("fa_true_pass"):
        row = status.get("FA_final_run2", {})
        if row.get("exit_code") == 0:
            return (1, 0, 0)
    if status.get("strict_promotion"):
        row = status.get("promotion", {}).get("reverify_run2", {})
        if row:
            return (1 if row.get("exit_code") == 0 else 0,
                    int(row.get("first_error_line", 0)), int(row.get("first_error_col", 0)))
    row = status.get("baseline", {}).get("FA", {})
    if status.get("baseline", {}).get("verified") and row:
        return (1 if row.get("exit_code") == 0 else 0,
                int(row.get("first_error_line", 0)), int(row.get("first_error_col", 0)))
    return None


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--refs", required=True)
    ap.add_argument("--fallback", required=True)
    ap.add_argument("--output", required=True)
    ap.add_argument("--metadata", required=True)
    args = ap.parse_args()

    refs = [x.strip() for x in Path(args.refs).read_text().splitlines() if x.strip()]
    candidates: list[dict[str, Any]] = []
    for ref in refs:
        source = git_bytes(ref, SOURCE_PATH)
        if source is None:
            continue
        source_sha = sha(source)
        line_count = len(source.decode("utf-8", errors="replace").splitlines())
        if line_count != 60453:
            continue
        tree = subprocess.run(
            ["git", "ls-tree", "-r", "--name-only", ref, "verified-records"],
            stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, text=True,
        )
        evidence_paths = [p for p in tree.stdout.splitlines() if p.endswith("/CURRENT.json")]
        evidence_found = False
        for evidence_path in evidence_paths:
            raw = git_bytes(ref, evidence_path)
            if raw is None:
                continue
            try:
                status = json.loads(raw)
            except Exception:
                continue
            if status.get("classification") != "VERIFIED":
                continue
            expected = status.get("checked_in_candidate_sha256")
            if expected and expected != source_sha:
                continue
            metric = source_metric(status)
            if metric is None:
                continue
            evidence_found = True
            candidates.append({
                "ref": ref,
                "source_sha256": source_sha,
                "line_count": line_count,
                "metric": {"exit_zero": bool(metric[0]), "first_error_line": metric[1], "first_error_col": metric[2]},
                "score": list(metric),
                "evidence_path": evidence_path,
                "classification": "VERIFIED",
                "source": source,
            })
        if not evidence_found and source_sha in KNOWN:
            metric = KNOWN[source_sha]
            candidates.append({
                "ref": ref,
                "source_sha256": source_sha,
                "line_count": line_count,
                "metric": {"exit_zero": False, "first_error_line": metric[1], "first_error_col": metric[2]},
                "score": list(metric),
                "evidence_path": "known-direct-verified-source-sha",
                "classification": "HISTORICAL+DIRECT-VERIFIED",
                "source": source,
            })

    fallback = Path(args.fallback).read_bytes()
    fallback_sha = sha(fallback)
    metric = KNOWN.get(fallback_sha, (0, 0, 0))
    candidates.append({
        "ref": "resolved-fallback",
        "source_sha256": fallback_sha,
        "line_count": len(fallback.decode("utf-8", errors="replace").splitlines()),
        "metric": {"exit_zero": False, "first_error_line": metric[1], "first_error_col": metric[2]},
        "score": list(metric),
        "evidence_path": "SHA-selected fallback; must be directly reverified",
        "classification": "CANDIDATE",
        "source": fallback,
    })

    best = max(candidates, key=lambda x: tuple(x["score"]))
    Path(args.output).write_bytes(best.pop("source"))
    metadata = {
        "selection_rule": "highest source-matched direct evidence metric; final authority is fresh direct Lean CLI reverify",
        "selected": best,
        "candidate_count": len(candidates),
        "candidates": [{k: v for k, v in c.items() if k != "source"} for c in candidates],
    }
    Path(args.metadata).write_text(json.dumps(metadata, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(metadata["selected"], indent=2))


if __name__ == "__main__":
    main()
