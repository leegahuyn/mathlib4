#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import importlib.util
import json
import os
import sys
from pathlib import Path
from typing import Any

ROOT = Path.cwd()
D = ROOT / "build-logs/fa443-matrix/final-gates"
SRC = ROOT / "PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean"


def read_text(path: Path) -> str:
    return path.read_text(encoding="utf-8", errors="replace") if path.exists() else ""


def read_int(path: Path, default: int = 999) -> int:
    try:
        return int(path.read_text(encoding="utf-8").strip())
    except Exception:
        return default


def forbidden_counts(text: str) -> dict[str, int]:
    module_path = ROOT / "scripts/fa442_prepare_same_height_candidate.py"
    spec = importlib.util.spec_from_file_location("fa443_checked_in_trust", module_path)
    if spec is None or spec.loader is None:
        raise RuntimeError("cannot load trust audit implementation")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return dict(module.forbidden_counts(text))


def write_output(key: str, value: object) -> None:
    output = os.environ.get("GITHUB_OUTPUT")
    if output:
        with open(output, "a", encoding="utf-8") as handle:
            handle.write(f"{key}={value}\n")


D.mkdir(parents=True, exist_ok=True)
text = SRC.read_text(encoding="utf-8") if SRC.exists() else ""
source_sha = hashlib.sha256(SRC.read_bytes()).hexdigest() if SRC.exists() else ""
selected_sha = os.environ.get("SELECTED_SHA", "")
identity_ok = os.environ.get("IDENTITY_OK", "false").lower() == "true"

runs: list[dict[str, Any]] = []
for run_number in (1, 2):
    prefix = D / f"FA-run{run_number}"
    run = {
        "run": run_number,
        "executed": prefix.with_suffix(".executed").exists(),
        "exit": read_int(prefix.with_suffix(".exit")),
        "command": read_text(prefix.with_suffix(".command.txt")).strip(),
        "olean_size": read_int(prefix.with_suffix(".olean.size"), 0),
        "ilean_size": read_int(prefix.with_suffix(".ilean.size"), 0),
        "log_exists": prefix.with_suffix(".log").exists(),
    }
    runs.append(run)

audit = forbidden_counts(text) if text else {}
forbidden_clean = bool(audit) and all(value == 0 for value in audit.values())
source_identity = identity_ok and source_sha == selected_sha and bool(source_sha)
runs_clean = all(
    run["executed"]
    and run["log_exists"]
    and run["exit"] == 0
    and run["olean_size"] > 0
    and run["ilean_size"] > 0
    for run in runs
)
fa_true_pass = source_identity and runs_clean and forbidden_clean

infra_reasons: list[str] = []
if not source_identity:
    infra_reasons.append("checked-in selected/worktree/HEAD source identity is not established")
if not all(run["executed"] and run["log_exists"] for run in runs):
    infra_reasons.append("one or both checked-in FA direct commands were not executed")

result = {
    "classification": "TRUE_PASS" if fa_true_pass else "INFRA_FAILURE" if infra_reasons else "LEAN_FAILURE",
    "authority": "checked-in source direct Lean CLI run twice",
    "selected_sha256": selected_sha,
    "checked_in_source_sha256": source_sha,
    "source_identity_ok": source_identity,
    "runs": runs,
    "forbidden_audit": audit,
    "forbidden_clean": forbidden_clean,
    "FA_TRUE_PASS": fa_true_pass,
    "infra_reasons": infra_reasons,
    "maxErrors_cap": 1,
    "maxErrors_interpretation": "first-error cap only; exit 0 plus nonempty olean/ilean is required",
}
(D / "FA_FINAL.json").write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
(D / "FA_FINAL.txt").write_text(
    "\n".join(f"{key}={value}" for key, value in result.items()) + "\n",
    encoding="utf-8",
)
print(json.dumps(result, indent=2))
write_output("fa_true_pass", str(fa_true_pass).lower())
write_output("classification", result["classification"])
