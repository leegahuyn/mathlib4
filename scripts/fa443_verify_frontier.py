from __future__ import annotations

import json
import os
import subprocess
from pathlib import Path
from typing import Any

from fa442_pipeline_common import (
    FA_PATH,
    MOCK2_ADV_PATH,
    MOCK2_PATH,
    REPO,
    audit_clean,
    exact_command,
    parse_first_error,
    sha256_bytes,
    sha256_file,
    source_metadata,
    write_json,
)

OUT = REPO / "build-logs/fa443-blocker-tournament/checked-in-frontier"
EXPECTED_SHA = os.environ["EXPECTED_SELECTED_SHA"]
EXPECTED_EXIT = int(os.environ.get("EXPECTED_SELECTED_EXIT", "1"))
EXPECTED_LINE = int(os.environ.get("EXPECTED_SELECTED_FIRST_LINE", "0"))
EXPECTED_COL = int(os.environ.get("EXPECTED_SELECTED_FIRST_COL", "0"))
MAX_ERRORS = int(os.environ.get("FA_MAX_ERRORS", "2000"))


def head_bytes() -> bytes:
    return subprocess.run(
        ["git", "show", "HEAD:PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean"],
        cwd=REPO, stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=True,
    ).stdout


def compile_one(stem: str, source: Path, max_errors: int) -> dict[str, Any]:
    output_dir = REPO / ".lake/build/lib/lean/PrimalitySheafVerification"
    output_dir.mkdir(parents=True, exist_ok=True)
    olean = output_dir / f"{stem}.olean"
    ilean = output_dir / f"{stem}.ilean"
    olean.unlink(missing_ok=True)
    ilean.unlink(missing_ok=True)
    command = [
        "lake", "env", "lean", "-DwarningAsError=false", f"-DmaxErrors={max_errors}",
        "-o", str(olean), "-i", str(ilean), str(source.relative_to(REPO)),
    ]
    log = OUT / f"{stem}.log"
    with log.open("wb") as fh:
        cp = subprocess.run(command, cwd=REPO, stdout=fh, stderr=subprocess.STDOUT, check=False)
    row = {
        "command": exact_command(command),
        "max_errors": max_errors,
        "exit_code": cp.returncode,
        "olean_exists": olean.exists() and olean.stat().st_size > 0,
        "ilean_exists": ilean.exists() and ilean.stat().st_size > 0,
        "log": str(log.relative_to(OUT)),
    }
    if stem == "Mock2_FunctionalAnalysis":
        text = log.read_text(encoding="utf-8", errors="replace")
        row["first_error"] = parse_first_error(text, source.read_text(encoding="utf-8"))
    return row


def main() -> None:
    OUT.mkdir(parents=True, exist_ok=True)
    worktree_sha = sha256_file(FA_PATH)
    head_sha = sha256_bytes(head_bytes())
    identity_ok = EXPECTED_SHA == worktree_sha == head_sha
    meta = source_metadata(FA_PATH.read_bytes())
    trust_ok = audit_clean(meta["trust_audit"])
    m2 = compile_one("Mock2", MOCK2_PATH, 400)
    m2a = compile_one("Mock2_Advanced", MOCK2_ADV_PATH, 400)
    prereq_ok = all(
        r["exit_code"] == 0 and r["olean_exists"] and r["ilean_exists"]
        for r in (m2, m2a)
    )
    fa = compile_one("Mock2_FunctionalAnalysis", FA_PATH, MAX_ERRORS) if prereq_ok else {
        "exit_code": 125,
        "first_error": {"line": 0, "column": 0, "declaration": ""},
        "error": "prerequisite regression",
    }
    actual_line = int(fa.get("first_error", {}).get("line", 0))
    actual_col = int(fa.get("first_error", {}).get("column", 0))
    metric_matches = (
        fa["exit_code"] == EXPECTED_EXIT and
        (fa["exit_code"] == 0 or (actual_line == EXPECTED_LINE and actual_col == EXPECTED_COL))
    )
    verified = identity_ok and trust_ok and prereq_ok and metric_matches
    report = {
        "classification": "VERIFIED" if verified else "INFRA_FAILURE",
        "selected_sha": EXPECTED_SHA,
        "worktree_sha": worktree_sha,
        "HEAD_source_sha": head_sha,
        "identity_ok": identity_ok,
        "trust_audit": meta["trust_audit"],
        "trust_audit_clean": trust_ok,
        "prerequisites": {"Mock2": m2, "Mock2_Advanced": m2a},
        "expected_metric": {
            "exit": EXPECTED_EXIT,
            "first_line": EXPECTED_LINE,
            "first_col": EXPECTED_COL,
        },
        "checked_in_direct_metric": fa,
        "metric_matches_selected_artifact": metric_matches,
        "verified": verified,
    }
    write_json(OUT / "verification.json", report)
    print(json.dumps(report, indent=2, ensure_ascii=False))
    if not verified:
        raise RuntimeError("checked-in FA443 frontier identity/direct metric mismatch")


if __name__ == "__main__":
    main()
