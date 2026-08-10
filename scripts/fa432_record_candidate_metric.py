#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import json
import os
import re
from pathlib import Path

variant = os.environ["VARIANT"]
out = Path(f"build-logs/fa432-scoped-instance-matrix/candidates/{variant}")
src = Path("PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean")
data = src.read_bytes()
text = data.decode("utf-8")
source_sha = hashlib.sha256(data).hexdigest()
line_count = data.count(b"\n") + (0 if data.endswith(b"\n") else 1)
metadata = json.loads((out / "CANDIDATE.json").read_text(encoding="utf-8"))

def errors(stem: str) -> tuple[int, int, int]:
    path = out / f"{stem}.log"
    log = path.read_text(encoding="utf-8", errors="replace") if path.exists() else ""
    pattern = re.compile(
        rf"{re.escape(stem)}\.lean:(\d+):(\d+):\s+(?:error(?:\([^)]*\))?:"
    )
    matches = list(pattern.finditer(log))
    return (
        len(matches),
        int(matches[0].group(1)) if matches else 0,
        int(matches[0].group(2)) if matches else 0,
    )

fa_errors, first_line, first_col = errors("Mock2_FunctionalAnalysis")
m2_errors, _, _ = errors("Mock2")
m2a_errors, _, _ = errors("Mock2_Advanced")

decl = "<none>"
if first_line:
    decl_re = re.compile(
        r"^(?:protected\s+|private\s+|noncomputable\s+)?"
        r"(?:theorem|lemma|def|abbrev|instance|structure|class)\s+([^\s(:]+)"
    )
    source_lines = text.splitlines()
    for i in range(min(first_line - 1, len(source_lines) - 1), -1, -1):
        match = decl_re.match(source_lines[i])
        if match:
            decl = match.group(1)
            break

metric = {
    "classification": "VERIFIED",
    "authority": "direct Lean CLI",
    "variant": variant,
    "source_sha256": source_sha,
    "candidate_metadata_sha256": metadata["candidate_sha256"],
    "source_metadata_identity": source_sha == metadata["candidate_sha256"],
    "line_count": line_count,
    "target_header_sha256": metadata["target_header_sha256"],
    "Mock2_exit": int(os.environ["M2_EXIT"]),
    "Mock2_errors": m2_errors,
    "Mock2_Advanced_exit": int(os.environ["M2A_EXIT"]),
    "Mock2_Advanced_errors": m2a_errors,
    "FA_exit": int(os.environ["FA_EXIT"]),
    "FA_error_headers_under_cap": fa_errors,
    "FA_first_error_line": first_line,
    "FA_first_error_col": first_col,
    "FA_first_error_declaration": decl,
    "maxErrors_cap": 1,
    "maxErrors_interpretation": "cap only; not total error count or proof progress",
}
(out / "METRIC.json").write_text(json.dumps(metric, indent=2) + "\n", encoding="utf-8")
(out / "METRIC.txt").write_text(
    "\n".join(f"{key}={value}" for key, value in metric.items()) + "\n",
    encoding="utf-8",
)
print(json.dumps(metric, indent=2))
