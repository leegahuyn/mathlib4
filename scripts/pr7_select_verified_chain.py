#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
from pathlib import Path
from typing import Any

FA_PATH = "PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean"
COPY_PREFIX = "PrimalitySheafVerification/"


def git_bytes(ref: str, path: str) -> bytes | None:
    proc = subprocess.run(
        ["git", "show", f"{ref}:{path}"],
        stdout=subprocess.PIPE,
        stderr=subprocess.DEVNULL,
        check=False,
    )
    return proc.stdout if proc.returncode == 0 else None


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def commit_epoch(ref: str) -> int:
    proc = subprocess.run(
        ["git", "show", "-s", "--format=%ct", ref],
        stdout=subprocess.PIPE,
        stderr=subprocess.DEVNULL,
        text=True,
        check=False,
    )
    try:
        return int(proc.stdout.strip())
    except Exception:
        return 0


def current_source_sha(status: dict[str, Any]) -> str | None:
    for key in (
        "selected_source_sha256",
        "checked_in_candidate_sha256",
        "source_sha256",
        "candidate_source_sha256",
    ):
        value = status.get(key)
        if isinstance(value, str) and value:
            return value
    baseline = status.get("baseline")
    if isinstance(baseline, dict):
        value = baseline.get("source_sha256")
        if isinstance(value, str) and value:
            return value
    return None


def trust_clean(status: dict[str, Any]) -> bool:
    audit = status.get("trust_audit")
    if not isinstance(audit, dict):
        return False
    if audit.get("clean") is not True:
        return False
    counts = audit.get("counts")
    return isinstance(counts, dict) and all(int(v) == 0 for v in counts.values())


def chain_complete(status: dict[str, Any]) -> bool:
    if status.get("classification") != "VERIFIED":
        return False
    if status.get("fa_true_pass") is not True:
        return False
    if status.get("all_required_targets_2x_pass") is not True:
        return False
    if not trust_clean(status):
        return False
    downstream = status.get("downstream")
    if isinstance(downstream, dict) and downstream.get("complete") is not True:
        return False
    return True


def list_files(ref: str) -> list[str]:
    proc = subprocess.run(
        ["git", "ls-tree", "-r", "--name-only", ref, COPY_PREFIX],
        stdout=subprocess.PIPE,
        stderr=subprocess.DEVNULL,
        text=True,
        check=False,
    )
    return [line.strip() for line in proc.stdout.splitlines() if line.strip()]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--refs", required=True)
    parser.add_argument("--output-dir", required=True)
    parser.add_argument("--metadata", required=True)
    args = parser.parse_args()

    refs = [line.strip() for line in Path(args.refs).read_text(encoding="utf-8").splitlines() if line.strip()]
    candidates: list[dict[str, Any]] = []
    for ref in refs:
        tree = subprocess.run(
            ["git", "ls-tree", "-r", "--name-only", ref, "verified-records"],
            stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL,
            text=True,
            check=False,
        )
        evidence_paths = [p for p in tree.stdout.splitlines() if p.endswith("/CURRENT.json")]
        fa_data = git_bytes(ref, FA_PATH)
        if fa_data is None:
            continue
        fa_sha = sha(fa_data)
        fa_lines = len(fa_data.decode("utf-8", errors="replace").splitlines())
        for evidence_path in evidence_paths:
            raw = git_bytes(ref, evidence_path)
            if raw is None:
                continue
            try:
                status = json.loads(raw.decode("utf-8", errors="replace"))
            except Exception:
                continue
            if not chain_complete(status):
                continue
            expected = current_source_sha(status)
            if expected != fa_sha:
                continue
            candidates.append(
                {
                    "ref": ref,
                    "evidence_path": evidence_path,
                    "source_sha256": fa_sha,
                    "line_count": fa_lines,
                    "commit_epoch": commit_epoch(ref),
                    "status": status,
                }
            )

    candidates.sort(key=lambda row: (row["commit_epoch"], row["ref"]), reverse=True)
    metadata: dict[str, Any] = {
        "found": bool(candidates),
        "selection_rule": "latest source-matched VERIFIED all-required-targets x2 evidence with clean FA trust audit",
        "candidate_count": len(candidates),
        "candidates": candidates,
        "selected": candidates[0] if candidates else None,
    }

    output = Path(args.output_dir)
    output.mkdir(parents=True, exist_ok=True)
    if candidates:
        selected = candidates[0]
        ref = selected["ref"]
        files = list_files(ref)
        wanted = []
        for path in files:
            name = Path(path).name
            if name in {
                "Mock2_FunctionalAnalysis.lean",
                "Mock2_FunctionalAnalysis_Integrated.lean",
                "QYM.lean",
            } or name.startswith("Mock3") and name.endswith(".lean"):
                wanted.append(path)
        if FA_PATH not in wanted:
            raise SystemExit("selected branch omitted required checked-in FA source")
        for path in wanted:
            data = git_bytes(ref, path)
            if data is None:
                raise SystemExit(f"selected source disappeared: {path}")
            destination = output / path
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_bytes(data)
        metadata["selected_files"] = wanted

    Path(args.metadata).write_text(json.dumps(metadata, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"found": metadata["found"], "selected": metadata["selected"], "selected_files": metadata.get("selected_files", [])}, indent=2))


if __name__ == "__main__":
    main()
