#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import importlib.util
import json
import os
import re
import sys
from pathlib import Path
from typing import Any

ROOT = Path.cwd()
D = ROOT / "build-logs/fa443-matrix/selected"
SRC = ROOT / "PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean"
EXPECTED_LINES = 60453
BASELINE_LINE = 31726
BASELINE_COL = 2
BASELINE_DECLARATION = "actualEdgeAmbientParam_hasDerivAt"
DECL_RE = re.compile(
    r"^(?:protected\s+|private\s+|noncomputable\s+)?"
    r"(?:theorem|lemma|def|abbrev|instance|structure|class)\s+([^\s(:]+)"
)


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def read_text(path: Path) -> str:
    return path.read_text(encoding="utf-8", errors="replace") if path.exists() else ""


def read_int(path: Path, default: int = 999) -> int:
    try:
        return int(path.read_text(encoding="utf-8").strip())
    except Exception:
        return default


def parse_errors(stem: str) -> dict[str, Any]:
    log = read_text(D / f"confirm-{stem}.log")
    pattern = re.compile(
        rf"{re.escape(stem)}\.lean:(\d+):(\d+):\s+error(?:\([^)]*\))?:\s*(.*)"
    )
    matches = list(pattern.finditer(log))
    line = int(matches[0].group(1)) if matches else 0
    col = int(matches[0].group(2)) if matches else 0
    message = ""
    if matches:
        excerpt = log[matches[0].start():].splitlines()
        captured: list[str] = []
        for index, value in enumerate(excerpt[:30]):
            if index > 0 and re.search(r"\.lean:\d+:\d+:\s+(?:error|warning)", value):
                break
            captured.append(value)
        message = "\n".join(captured).strip()
    return {
        "error_headers_captured": len(matches),
        "first_error_line": line,
        "first_error_col": col,
        "first_error_message": message,
    }


def declaration_at(text: str, line_number: int) -> tuple[str, int]:
    if line_number <= 0:
        return "<none>", -1
    current_name = "<unknown>"
    current_index = -1
    for index, line in enumerate(text.splitlines(), start=1):
        match = DECL_RE.match(line)
        if match:
            current_index += 1
            current_name = match.group(1)
        if index >= line_number:
            return current_name, current_index
    return current_name, current_index


def load_json(path: Path) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
        return value if isinstance(value, dict) else {}
    except Exception:
        return {}


def forbidden_counts(text: str) -> dict[str, int]:
    module_path = ROOT / "scripts/fa442_prepare_same_height_candidate.py"
    spec = importlib.util.spec_from_file_location("fa443_trust_audit", module_path)
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
selection = load_json(D / "SELECTION.json")
chosen = selection.get("chosen", {}) if isinstance(selection.get("chosen"), dict) else {}
baseline = selection.get("baseline", {}) if isinstance(selection.get("baseline"), dict) else {}
selected_sha = os.environ.get("SELECTED_SHA", "")
selection_mode = os.environ.get("SELECTION_MODE", "")
selected_variant = os.environ.get("SELECTED_VARIANT", "")

data = SRC.read_bytes() if SRC.exists() else b""
text = data.decode("utf-8", errors="replace")
source_sha = sha256_bytes(data) if data else ""
line_count = data.count(b"\n") + (0 if not data or data.endswith(b"\n") else 1)

stems = ["Mock2", "Mock2_Advanced", "Mock2_FunctionalAnalysis"]
exit_codes = {stem: read_int(D / f"confirm-{stem}.exit") for stem in stems}
errors = {stem: parse_errors(stem) for stem in stems}
executed = {
    stem: (D / f"confirm-{stem}.executed").exists()
    and (D / f"confirm-{stem}.command.txt").exists()
    and (D / f"confirm-{stem}.exit").exists()
    and (D / f"confirm-{stem}.log").exists()
    for stem in stems
}
commands = {stem: read_text(D / f"confirm-{stem}.command.txt").strip() for stem in stems}
fa_line = int(errors["Mock2_FunctionalAnalysis"]["first_error_line"])
fa_col = int(errors["Mock2_FunctionalAnalysis"]["first_error_col"])
fa_declaration, fa_declaration_index = declaration_at(text, fa_line)
audit = forbidden_counts(text) if text else {}
forbidden_clean = bool(audit) and all(value == 0 for value in audit.values())

matrix_exit = int(chosen.get("FA_exit", 999))
matrix_decl_index = int(chosen.get("FA_error_declaration_index", -1))
matrix_position = (
    int(chosen.get("FA_first_actual_error_line", 0)),
    int(chosen.get("FA_first_actual_error_col", 0)),
)
confirmation_position = (fa_line, fa_col)
if matrix_exit == 0:
    reproduces_matrix = exit_codes["Mock2_FunctionalAnalysis"] == 0
else:
    reproduces_matrix = (
        exit_codes["Mock2_FunctionalAnalysis"] == 0
        or fa_declaration_index > matrix_decl_index
        or (
            fa_declaration_index == matrix_decl_index
            and confirmation_position >= matrix_position
        )
    )

baseline_decl_index = int(baseline.get("FA_error_declaration_index", -1))
strict_vs_baseline = (
    exit_codes["Mock2_FunctionalAnalysis"] == 0
    or fa_declaration_index > baseline_decl_index
    or (
        fa_declaration_index == baseline_decl_index
        and confirmation_position > (BASELINE_LINE, BASELINE_COL)
    )
)
if selection_mode == "strict_promotion":
    selected_metric_condition = strict_vs_baseline
else:
    selected_metric_condition = (
        source_sha == baseline.get("source_sha256")
        and exit_codes["Mock2_FunctionalAnalysis"] == 1
        and fa_declaration == BASELINE_DECLARATION
        and confirmation_position >= (BASELINE_LINE, BASELINE_COL)
    )

infra_reasons: list[str] = []
if not selection:
    infra_reasons.append("SELECTION.json missing or invalid")
if source_sha != selected_sha:
    infra_reasons.append("selected SHA and repository worktree SHA differ")
if source_sha != chosen.get("source_sha256"):
    infra_reasons.append("selected source SHA differs from chosen metric SHA")
if line_count != EXPECTED_LINES:
    infra_reasons.append(f"selected source line count {line_count} != {EXPECTED_LINES}")
if not all(executed.values()):
    missing = [stem for stem, value in executed.items() if not value]
    infra_reasons.append("independent direct Lean CLI not executed for: " + ", ".join(missing))
if exit_codes["Mock2"] != 0 or errors["Mock2"]["error_headers_captured"] != 0:
    infra_reasons.append("Mock2 independent confirmation regressed")
if exit_codes["Mock2_Advanced"] != 0 or errors["Mock2_Advanced"]["error_headers_captured"] != 0:
    infra_reasons.append("Mock2_Advanced independent confirmation regressed")
if not reproduces_matrix:
    infra_reasons.append("independent FA confirmation did not reproduce selected matrix metric")
if not selected_metric_condition:
    infra_reasons.append("selected source does not satisfy its baseline/promotion metric condition")
if not forbidden_clean:
    infra_reasons.append("selected source forbidden-token audit is not clean")

verified = not infra_reasons
if not verified:
    result_classification = "INFRA_FAILURE"
elif exit_codes["Mock2_FunctionalAnalysis"] == 0:
    result_classification = "FA_PASS_CANDIDATE"
elif strict_vs_baseline and fa_declaration_index > baseline_decl_index:
    result_classification = "DECLARATION_BREAKTHROUGH"
elif strict_vs_baseline:
    result_classification = "SMALL_SAME_DECLARATION_ADVANCE"
else:
    result_classification = "NO_IMPROVEMENT"

result: dict[str, Any] = {
    "classification": "VERIFIED" if verified else "INFRA_FAILURE",
    "result_classification": result_classification,
    "authority": "independent actual direct Lean CLI on selected repository source path",
    "selection_mode": selection_mode,
    "variant": selected_variant,
    "source_sha256": source_sha,
    "selected_sha256": selected_sha,
    "source_identity_ok": source_sha == selected_sha == chosen.get("source_sha256"),
    "line_count": line_count,
    "same_height": line_count == EXPECTED_LINES,
    "lean_executed": executed,
    "compile_commands": commands,
    "Mock2_exit": exit_codes["Mock2"],
    "Mock2_errors_under_cap": errors["Mock2"]["error_headers_captured"],
    "Mock2_Advanced_exit": exit_codes["Mock2_Advanced"],
    "Mock2_Advanced_errors_under_cap": errors["Mock2_Advanced"]["error_headers_captured"],
    "FA_exit": exit_codes["Mock2_FunctionalAnalysis"],
    "FA_error_headers_captured": errors["Mock2_FunctionalAnalysis"]["error_headers_captured"],
    "FA_first_actual_error_line": fa_line,
    "FA_first_actual_error_col": fa_col,
    "FA_first_error_message": errors["Mock2_FunctionalAnalysis"]["first_error_message"],
    "FA_first_error_declaration": fa_declaration,
    "FA_error_declaration_index": fa_declaration_index,
    "matrix_metric_reproduced_or_better": reproduces_matrix,
    "strictly_better_than_31726": strict_vs_baseline,
    "forbidden_audit": audit,
    "forbidden_clean": forbidden_clean,
    "maxErrors_cap": int(os.environ.get("MAX_ERRORS", "120")),
    "maxErrors_interpretation": "diagnostic cap only; not total errors or progress",
    "infra_reasons": infra_reasons,
    "verified": verified,
}
(D / "CONFIRMATION.json").write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
(D / "CONFIRMATION.txt").write_text(
    "\n".join(f"{key}={value}" for key, value in result.items()) + "\n",
    encoding="utf-8",
)
(D / ("VERIFIED" if verified else "CONFIRMATION_INFRA_FAILURE")).touch()
print(json.dumps(result, indent=2))
write_output("verified", str(verified).lower())
write_output("result_classification", result_classification)
write_output("fa_exit", exit_codes["Mock2_FunctionalAnalysis"])
write_output("first_line", fa_line)
write_output("first_col", fa_col)
write_output("declaration", fa_declaration)
write_output("declaration_index", fa_declaration_index)
write_output("worktree_sha", source_sha)
