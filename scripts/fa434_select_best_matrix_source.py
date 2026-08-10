#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import json
import subprocess
from dataclasses import dataclass, asdict
from pathlib import Path

ROOT = Path.cwd()
OUT = Path("/tmp/fa434-best-of-matrices")
OUT.mkdir(parents=True, exist_ok=True)
SOURCE_PATH = "PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean"
EXPECTED_LINES = 60453
MIN_FRONTIER = 31726

UPSTREAMS = [
    (
        "fix/fa427-actualedge-parallel-matrix-20260810",
        "build-logs/fa427-actualedge-matrix/selected/CONFIRMATION.json",
    ),
    (
        "fix/fa428-cumulative-known-hunks-20260810",
        "build-logs/fa428-cumulative-matrix/selected/CONFIRMATION.json",
    ),
    (
        "fix/fa432-scoped-complex-instance-20260810",
        "build-logs/fa432-scoped-instance-matrix/selected/CONFIRMATION.json",
    ),
]


@dataclass
class Candidate:
    branch: str
    commit: str
    source_sha256: str
    line_count: int
    fa_exit: int
    first_error_line: int
    first_error_col: int
    selection_mode: str
    confirmation_path: str
    source_file: str

    @property
    def passed(self) -> bool:
        return self.fa_exit == 0


def run(args: list[str], *, text: bool = True, stdout=None, stderr=None):
    return subprocess.run(
        args,
        cwd=ROOT,
        text=text,
        stdout=stdout,
        stderr=stderr,
        check=False,
    )


def git_show(ref: str, path: str, *, text: bool = False):
    proc = run(
        ["git", "show", f"{ref}:{path}"],
        text=text,
        stdout=subprocess.PIPE,
        stderr=subprocess.DEVNULL,
    )
    return proc.stdout if proc.returncode == 0 else None


def fetch_branch(branch: str) -> str | None:
    remote_ref = f"refs/remotes/origin/{branch}"
    proc = run(
        [
            "git",
            "fetch",
            "--force",
            "origin",
            f"refs/heads/{branch}:{remote_ref}",
            "--depth=40",
        ],
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )
    if proc.returncode != 0:
        return None
    rev = run(
        ["git", "rev-parse", remote_ref],
        stdout=subprocess.PIPE,
        stderr=subprocess.DEVNULL,
    )
    return rev.stdout.strip() if rev.returncode == 0 else None


def validate(branch: str, confirmation_path: str) -> tuple[Candidate | None, dict]:
    diagnostic: dict = {"branch": branch, "confirmation_path": confirmation_path}
    commit = fetch_branch(branch)
    diagnostic["commit"] = commit
    if not commit:
        diagnostic["status"] = "branch_fetch_failed"
        return None, diagnostic

    confirmation_raw = git_show(commit, confirmation_path, text=True)
    source_raw = git_show(commit, SOURCE_PATH, text=False)
    if confirmation_raw is None or source_raw is None:
        diagnostic["status"] = "required_file_missing"
        diagnostic["confirmation_present"] = confirmation_raw is not None
        diagnostic["source_present"] = source_raw is not None
        return None, diagnostic
    try:
        confirmation = json.loads(confirmation_raw)
    except json.JSONDecodeError as exc:
        diagnostic["status"] = "invalid_confirmation_json"
        diagnostic["error"] = str(exc)
        return None, diagnostic

    source_sha = hashlib.sha256(source_raw).hexdigest()
    line_count = source_raw.count(b"\n") + (0 if source_raw.endswith(b"\n") else 1)
    fa_exit = int(confirmation.get("FA_exit", 999))
    first_line = int(confirmation.get("FA_first_error_line", 0))
    first_col = int(confirmation.get("FA_first_error_col", 0))
    valid = (
        confirmation.get("classification") == "VERIFIED"
        and confirmation.get("authority") == "direct Lean CLI"
        and confirmation.get("verified") is True
        and confirmation.get("source_sha256") == source_sha
        and line_count == EXPECTED_LINES
        and (fa_exit == 0 or first_line >= MIN_FRONTIER)
    )
    diagnostic.update(
        {
            "status": "valid" if valid else "invalid",
            "source_sha256": source_sha,
            "line_count": line_count,
            "FA_exit": fa_exit,
            "FA_first_error_line": first_line,
            "FA_first_error_col": first_col,
            "confirmation_source_sha256": confirmation.get("source_sha256"),
            "classification": confirmation.get("classification"),
            "authority": confirmation.get("authority"),
            "verified": confirmation.get("verified"),
        }
    )
    if not valid:
        return None, diagnostic

    source_file = OUT / f"{branch.replace('/', '__')}.lean"
    source_file.write_bytes(source_raw)
    candidate = Candidate(
        branch=branch,
        commit=commit,
        source_sha256=source_sha,
        line_count=line_count,
        fa_exit=fa_exit,
        first_error_line=first_line,
        first_error_col=first_col,
        selection_mode=str(confirmation.get("selection_mode", "unknown")),
        confirmation_path=confirmation_path,
        source_file=str(source_file),
    )
    return candidate, diagnostic


def main() -> None:
    candidates: list[Candidate] = []
    diagnostics: list[dict] = []
    for branch, confirmation_path in UPSTREAMS:
        candidate, diagnostic = validate(branch, confirmation_path)
        diagnostics.append(diagnostic)
        if candidate is not None:
            candidates.append(candidate)

    candidates.sort(
        key=lambda item: (
            item.passed,
            item.first_error_line,
            item.first_error_col,
            item.commit,
        ),
        reverse=True,
    )
    result: dict = {
        "classification": "VERIFIED" if candidates else "INFRA_FAILURE",
        "authority": "direct Lean CLI upstream confirmation with checked-in source SHA identity",
        "valid_candidate_count": len(candidates),
        "candidates": [asdict(candidate) for candidate in candidates],
        "diagnostics": diagnostics,
    }
    if candidates:
        best = candidates[0]
        result["best"] = asdict(best)
        Path("/tmp/fa434-best-of-matrices/selected-source.lean").write_bytes(
            Path(best.source_file).read_bytes()
        )
    (OUT / "POLL.json").write_text(
        json.dumps(result, indent=2) + "\n", encoding="utf-8"
    )
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
