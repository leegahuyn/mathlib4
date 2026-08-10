#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import json
import os
import re
import subprocess
from pathlib import Path
from typing import Any

ROOT = Path.cwd()
VARIANT = os.environ["VARIANT"]
OUT = ROOT / f"build-logs/fa443-matrix/candidates/{VARIANT}"
SRC = ROOT / "PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean"
EXPECTED_BASELINE_SHA = "71dc36f16ebea92d537aa40a5d420443e4bcb93ccb76fea31efb40a6cb5c3aa0"
EXPECTED_LINES = 60453
TARGET_DECLARATION = "actualEdgeAmbientParam_hasDerivAt"

DECL_RE = re.compile(
    r"^(?:protected\s+|private\s+|noncomputable\s+)?"
    r"(?:theorem|lemma|def|abbrev|instance|structure|class)\s+([^\s(:]+)"
)
ERROR_RE_TEMPLATE = r"{stem}\.lean:(\d+):(\d+):\s+error(?:\([^)]*\))?:\s*(.*)"


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def read_text(path: Path) -> str:
    return path.read_text(encoding="utf-8", errors="replace") if path.exists() else ""


def read_int(path: Path, default: int = 999) -> int:
    try:
        return int(path.read_text(encoding="utf-8").strip())
    except Exception:
        return default


def git_output(*args: str) -> str:
    proc = subprocess.run(
        ["git", *args], cwd=ROOT, text=True, stdout=subprocess.PIPE,
        stderr=subprocess.PIPE, check=False
    )
    return proc.stdout.strip() if proc.returncode == 0 else f"<git-error:{proc.stderr.strip()}>"


def parse_errors(stem: str) -> dict[str, Any]:
    log_path = OUT / f"{stem}.log"
    log = read_text(log_path)
    pattern = re.compile(ERROR_RE_TEMPLATE.format(stem=re.escape(stem)))
    matches = list(pattern.finditer(log))
    first_line = int(matches[0].group(1)) if matches else 0
    first_col = int(matches[0].group(2)) if matches else 0
    first_message = ""
    if matches:
        start = matches[0].start()
        excerpt = log[start:].splitlines()
        captured: list[str] = []
        for index, line in enumerate(excerpt[:30]):
            if index > 0 and re.search(r"\.lean:\d+:\d+:\s+(?:error|warning)", line):
                break
            captured.append(line)
        first_message = "\n".join(captured).strip()
    return {
        "error_headers_captured": len(matches),
        "first_error_line": first_line,
        "first_error_col": first_col,
        "first_error_message": first_message,
        "log_exists": log_path.exists(),
    }


def declaration_at(text: str, line_number: int) -> tuple[str, int]:
    if line_number <= 0:
        return "<none>", -1
    current_name = "<unknown>"
    current_index = -1
    for i, line in enumerate(text.splitlines(), start=1):
        match = DECL_RE.match(line)
        if match:
            current_index += 1
            current_name = match.group(1)
        if i >= line_number:
            return current_name, current_index
    return current_name, current_index


def load_json(path: Path) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
        return value if isinstance(value, dict) else {}
    except Exception:
        return {}


def file_sha(path: Path) -> str:
    return sha256_bytes(path.read_bytes()) if path.exists() else ""


OUT.mkdir(parents=True, exist_ok=True)
prepare_ok = os.environ.get("PREPARE_OK", "false").lower() == "true"
metadata = load_json(OUT / "CANDIDATE.json")
source_data = SRC.read_bytes() if SRC.exists() else b""
source_text = source_data.decode("utf-8", errors="replace")
source_sha = sha256_bytes(source_data) if source_data else ""
line_count = source_data.count(b"\n") + (0 if not source_data or source_data.endswith(b"\n") else 1)

stems = ["Mock2", "Mock2_Advanced", "Mock2_FunctionalAnalysis"]
exit_codes = {stem: read_int(OUT / f"{stem}.exit") for stem in stems}
error_data = {stem: parse_errors(stem) for stem in stems}
executed = {
    stem: (OUT / f"{stem}.executed").exists()
    and (OUT / f"{stem}.command.txt").exists()
    and (OUT / f"{stem}.exit").exists()
    and (OUT / f"{stem}.log").exists()
    for stem in stems
}
commands = {stem: read_text(OUT / f"{stem}.command.txt").strip() for stem in stems}

fa_first_line = int(error_data["Mock2_FunctionalAnalysis"]["first_error_line"])
fa_declaration, fa_declaration_index = declaration_at(source_text, fa_first_line)

candidate_forbidden = metadata.get("candidate_forbidden_counts", {})
if not isinstance(candidate_forbidden, dict):
    candidate_forbidden = {}
forbidden_clean = bool(candidate_forbidden) and all(int(v) == 0 for v in candidate_forbidden.values())

infra_reasons: list[str] = []
if not prepare_ok:
    infra_reasons.append("candidate preparation failed")
if not metadata:
    infra_reasons.append("CANDIDATE.json missing or invalid")
if not SRC.exists():
    infra_reasons.append("candidate repository source missing")
if source_sha != str(metadata.get("candidate_sha256", "")):
    infra_reasons.append("candidate source SHA does not match metadata")
if line_count != EXPECTED_LINES:
    infra_reasons.append(f"candidate line count {line_count} != {EXPECTED_LINES}")
if not metadata.get("target_header_sha256"):
    infra_reasons.append("target theorem header hash missing")
if not all(executed.values()):
    missing = [stem for stem, value in executed.items() if not value]
    infra_reasons.append("direct Lean CLI not executed for: " + ", ".join(missing))
if not forbidden_clean:
    infra_reasons.append("forbidden-token audit is not clean")

classification = "INFRA_FAILURE" if infra_reasons else "VERIFIED"
if classification == "INFRA_FAILURE":
    result_classification = "INFRA_FAILURE"
elif exit_codes["Mock2"] != 0 or exit_codes["Mock2_Advanced"] != 0:
    result_classification = "LEAN_FAILURE_PREREQUISITE"
elif exit_codes["Mock2_FunctionalAnalysis"] == 0:
    result_classification = "FA_PASS_CANDIDATE"
elif fa_first_line <= 0:
    result_classification = "LEAN_FAILURE_NO_PARSED_ERROR"
else:
    result_classification = "LEAN_FAILURE"

lean_version = read_text(OUT / "lean-version.txt").strip()
lake_version = read_text(OUT / "lake-version.txt").strip()
lean_toolchain = read_text(ROOT / "lean-toolchain").strip()
lake_manifest_sha = file_sha(ROOT / "lake-manifest.json")

metric: dict[str, Any] = {
    "classification": classification,
    "result_classification": result_classification,
    "authority": "actual direct Lean CLI on generated repository source path",
    "variant": VARIANT,
    "prepare_ok": prepare_ok,
    "infra_reasons": infra_reasons,
    "lean_executed": executed,
    "all_required_lean_commands_executed": all(executed.values()),
    "source_sha256": source_sha,
    "candidate_metadata_sha256": metadata.get("candidate_sha256", ""),
    "source_metadata_identity": source_sha == metadata.get("candidate_sha256", ""),
    "baseline_sha256": metadata.get("baseline_sha256", EXPECTED_BASELINE_SHA),
    "line_count": line_count,
    "expected_line_count": EXPECTED_LINES,
    "same_height": line_count == EXPECTED_LINES,
    "target_declaration": TARGET_DECLARATION,
    "target_header_sha256": metadata.get("target_header_sha256", ""),
    "theorem_header_unchanged": bool(metadata.get("target_header_sha256")),
    "Mock2_exit": exit_codes["Mock2"],
    "Mock2_errors_under_cap": error_data["Mock2"]["error_headers_captured"],
    "Mock2_Advanced_exit": exit_codes["Mock2_Advanced"],
    "Mock2_Advanced_errors_under_cap": error_data["Mock2_Advanced"]["error_headers_captured"],
    "FA_exit": exit_codes["Mock2_FunctionalAnalysis"],
    "FA_error_headers_captured": error_data["Mock2_FunctionalAnalysis"]["error_headers_captured"],
    "FA_first_actual_error_line": fa_first_line,
    "FA_first_actual_error_col": error_data["Mock2_FunctionalAnalysis"]["first_error_col"],
    "FA_first_error_message": error_data["Mock2_FunctionalAnalysis"]["first_error_message"],
    "FA_first_error_declaration": fa_declaration,
    "FA_error_declaration_index": fa_declaration_index,
    "maxErrors_cap": int(os.environ.get("MAX_ERRORS", "80")),
    "maxErrors_interpretation": "diagnostic cap only; never interpreted as total errors or completion progress",
    "compile_commands": commands,
    "lean_version": lean_version,
    "lake_version": lake_version,
    "lean_toolchain": lean_toolchain,
    "workflow_commit_identity": git_output("rev-parse", "HEAD"),
    "trigger_commit_identity": os.environ.get("GITHUB_SHA", ""),
    "baseline_commit_identity": os.environ.get("BASELINE_COMMIT", ""),
    "lake_manifest_sha256": lake_manifest_sha,
    "candidate_forbidden_counts": candidate_forbidden,
    "forbidden_clean": forbidden_clean,
    "repairs": metadata.get("repairs", []),
}

(OUT / "METRIC.json").write_text(json.dumps(metric, indent=2) + "\n", encoding="utf-8")
(OUT / "METRIC.txt").write_text(
    "\n".join(f"{key}={value}" for key, value in metric.items()) + "\n",
    encoding="utf-8",
)
print(json.dumps(metric, indent=2))
