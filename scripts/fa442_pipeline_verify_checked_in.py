from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path
from typing import Any

from fa442_pipeline_common import (
    FA_PATH,
    MOCK2_ADV_PATH,
    MOCK2_PATH,
    REPO,
    append_github_output,
    audit_clean,
    exact_command,
    parse_first_error,
    sha256_bytes,
    sha256_file,
    source_metadata,
    trust_audit,
    write_json,
)

OUT = REPO / "build-logs/fa442-pipeline-repair/checked-in-verification"
EXPECTED_SELECTED_SHA = os.environ.get("EXPECTED_SELECTED_SHA", "")


def compile_one(stem: str, source: Path, label: str) -> dict[str, Any]:
    output_dir = REPO / ".lake/build/lib/lean/PrimalitySheafVerification"
    output_dir.mkdir(parents=True, exist_ok=True)
    olean = output_dir / f"{stem}.olean"
    ilean = output_dir / f"{stem}.ilean"
    olean.unlink(missing_ok=True)
    ilean.unlink(missing_ok=True)
    command = [
        "lake", "env", "lean",
        "-DwarningAsError=false",
        "-o", str(olean),
        "-i", str(ilean),
        str(source.relative_to(REPO)),
    ]
    log_path = OUT / f"{stem}-{label}.log"
    with log_path.open("wb") as log:
        cp = subprocess.run(
            command, cwd=REPO, stdout=log, stderr=subprocess.STDOUT, check=False
        )
    text = log_path.read_text(encoding="utf-8", errors="replace")
    result = {
        "label": label,
        "command": exact_command(command),
        "exit_code": cp.returncode,
        "olean_exists": olean.exists() and olean.stat().st_size > 0,
        "ilean_exists": ilean.exists() and ilean.stat().st_size > 0,
        "error_header_count": len([
            line for line in text.splitlines()
            if ".lean:" in line and ": error" in line
        ]),
        "log": str(log_path.relative_to(OUT)),
    }
    if stem == "Mock2_FunctionalAnalysis":
        result["first_error"] = parse_first_error(text, source.read_text(encoding="utf-8"))
    return result


def head_source_bytes() -> bytes:
    cp = subprocess.run(
        [
            "git", "show",
            "HEAD:PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean",
        ],
        cwd=REPO,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=True,
    )
    return cp.stdout


def main() -> None:
    OUT.mkdir(parents=True, exist_ok=True)
    worktree_sha = sha256_file(FA_PATH)
    head_bytes = head_source_bytes()
    head_sha = sha256_bytes(head_bytes)
    selected_sha = EXPECTED_SELECTED_SHA or worktree_sha
    source_text = FA_PATH.read_text(encoding="utf-8")
    audit = trust_audit(source_text)
    source_meta = source_metadata(FA_PATH.read_bytes())
    identity_ok = selected_sha == worktree_sha == head_sha

    prereq1 = compile_one("Mock2", MOCK2_PATH, "regression")
    prereq2 = compile_one("Mock2_Advanced", MOCK2_ADV_PATH, "regression")
    prereq_ok = all(
        row["exit_code"] == 0 and row["olean_exists"] and row["ilean_exists"]
        for row in (prereq1, prereq2)
    )

    fa_run1 = compile_one("Mock2_FunctionalAnalysis", FA_PATH, "run1") if prereq_ok else {
        "label": "run1", "exit_code": 125, "error": "prerequisite regression"
    }
    fa_run2 = compile_one("Mock2_FunctionalAnalysis", FA_PATH, "run2") if prereq_ok else {
        "label": "run2", "exit_code": 125, "error": "prerequisite regression"
    }

    true_pass = bool(
        identity_ok and audit_clean(audit) and prereq_ok and
        fa_run1.get("exit_code") == 0 and fa_run1.get("error_header_count") == 0 and
        fa_run1.get("olean_exists") and fa_run1.get("ilean_exists") and
        fa_run2.get("exit_code") == 0 and fa_run2.get("error_header_count") == 0 and
        fa_run2.get("olean_exists") and fa_run2.get("ilean_exists")
    )
    if true_pass:
        classification = "TRUE_PASS"
    elif not identity_ok or not audit_clean(audit) or not prereq_ok:
        classification = "INFRA_FAILURE"
    else:
        classification = "LEAN_FAILURE"

    report = {
        "classification": classification,
        "FA_TRUE_PASS": true_pass,
        "selected_sha256": selected_sha,
        "worktree_sha256": worktree_sha,
        "HEAD_source_sha256": head_sha,
        "identity_ok": identity_ok,
        "line_count": source_meta["line_count"],
        "trust_audit": audit,
        "trust_audit_clean": audit_clean(audit),
        "prerequisites": {
            "Mock2": prereq1,
            "Mock2_Advanced": prereq2,
        },
        "FA_checked_in_run1": fa_run1,
        "FA_checked_in_run2": fa_run2,
        "lean_version": Path("/tmp/fa442-verify-lean-version.txt").read_text(
            errors="replace").strip() if Path("/tmp/fa442-verify-lean-version.txt").exists() else "",
        "lake_version": Path("/tmp/fa442-verify-lake-version.txt").read_text(
            errors="replace").strip() if Path("/tmp/fa442-verify-lake-version.txt").exists() else "",
        "repository_head": subprocess.run(
            ["git", "rev-parse", "HEAD"], cwd=REPO,
            stdout=subprocess.PIPE, text=True, check=True,
        ).stdout.strip(),
        "authority": "checked-in HEAD source direct lake env lean CLI, run twice",
    }
    write_json(OUT / "verification.json", report)
    (OUT / ("FA_TRUE_PASS" if true_pass else classification)).touch()
    append_github_output(
        classification=classification,
        fa_true_pass=true_pass,
        selected_sha=selected_sha,
        head_source_sha=head_sha,
        worktree_sha=worktree_sha,
        identity_ok=identity_ok,
        run1_exit=fa_run1.get("exit_code", 999),
        run2_exit=fa_run2.get("exit_code", 999),
    )
    print(json.dumps(report, indent=2, ensure_ascii=False))
    if classification == "INFRA_FAILURE":
        raise RuntimeError("checked-in verification infrastructure/identity/trust failure")


if __name__ == "__main__":
    main()
