#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import json
import os
import re
from pathlib import Path

VARIANT = os.environ["VARIANT"]
ROOT = Path.cwd()
OUT = ROOT / f"build-logs/fa442-same-height/candidates/{VARIANT}"
SRC = ROOT / "PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean"
DECL_RE = re.compile(
    r"^(?:protected\s+|private\s+|noncomputable\s+)?"
    r"(?:theorem|lemma|def|abbrev|instance|structure|class)\s+([^\s(:]+)"
)


def parse_errors(stem: str) -> tuple[int, int, int]:
    path = OUT / f"{stem}.log"
    log = path.read_text(encoding="utf-8", errors="replace") if path.exists() else ""
    pattern = re.compile(
        rf"(?:^|/){re.escape(stem)}\.lean:(\d+):(\d+):\s+error:",
        re.MULTILINE,
    )
    matches = list(pattern.finditer(log))
    if not matches:
        # Absolute paths may contain a different slash prefix; retain only the filename anchor.
        pattern = re.compile(
            rf"{re.escape(stem)}\.lean:(\d+):(\d+):\s+error:"
        )
        matches = list(pattern.finditer(log))
    return (
        len(matches),
        int(matches[0].group(1)) if matches else 0,
        int(matches[0].group(2)) if matches else 0,
    )


def declaration_at(text: str, line_number: int) -> tuple[str, int]:
    if line_number <= 0:
        return "<none>", -1
    lines = text.splitlines()
    declaration_index = -1
    current_index = -1
    current_name = "<unknown>"
    for i, line in enumerate(lines):
        match = DECL_RE.match(line)
        if match:
            current_index += 1
            current_name = match.group(1)
        if i + 1 >= line_number:
            declaration_index = current_index
            break
    return current_name, declaration_index


data = SRC.read_bytes()
text = data.decode("utf-8")
source_sha = hashlib.sha256(data).hexdigest()
line_count = data.count(b"\n") + (0 if data.endswith(b"\n") else 1)
metadata = json.loads((OUT / "CANDIDATE.json").read_text(encoding="utf-8"))

m2_errors, _, _ = parse_errors("Mock2")
m2a_errors, _, _ = parse_errors("Mock2_Advanced")
fa_errors, first_line, first_col = parse_errors("Mock2_FunctionalAnalysis")
declaration, declaration_index = declaration_at(text, first_line)

candidate_forbidden = metadata.get("candidate_forbidden_counts", {})
baseline_forbidden = metadata.get("baseline_forbidden_counts", {})
forbidden_not_increased = all(
    int(candidate_forbidden.get(key, 0)) <= int(baseline_forbidden.get(key, 0))
    for key in baseline_forbidden
)
forbidden_clean = all(int(value) == 0 for value in candidate_forbidden.values())
metric = {
    "classification": "VERIFIED",
    "authority": "direct Lean CLI on repository source path",
    "variant": VARIANT,
    "source_sha256": source_sha,
    "candidate_metadata_sha256": metadata["candidate_sha256"],
    "source_metadata_identity": source_sha == metadata["candidate_sha256"],
    "line_count": line_count,
    "target_header_sha256": metadata["target_header_sha256"],
    "Mock2_exit": int(os.environ["M2_EXIT"]),
    "Mock2_errors_under_cap": m2_errors,
    "Mock2_Advanced_exit": int(os.environ["M2A_EXIT"]),
    "Mock2_Advanced_errors_under_cap": m2a_errors,
    "FA_exit": int(os.environ["FA_EXIT"]),
    "FA_error_headers_captured": fa_errors,
    "FA_first_actual_error_line": first_line,
    "FA_first_actual_error_col": first_col,
    "FA_first_error_declaration": declaration,
    "FA_error_declaration_index": declaration_index,
    "maxErrors_cap": int(os.environ.get("MAX_ERRORS", "50")),
    "maxErrors_interpretation": "diagnostic cap only; not total errors or proof progress",
    "candidate_forbidden_counts": candidate_forbidden,
    "forbidden_not_increased": forbidden_not_increased,
    "forbidden_clean": forbidden_clean,
    "repairs": metadata.get("repairs", []),
}
(OUT / "METRIC.json").write_text(
    json.dumps(metric, indent=2) + "\n", encoding="utf-8"
)
(OUT / "METRIC.txt").write_text(
    "\n".join(f"{key}={value}" for key, value in metric.items()) + "\n",
    encoding="utf-8",
)
print(json.dumps(metric, indent=2))
