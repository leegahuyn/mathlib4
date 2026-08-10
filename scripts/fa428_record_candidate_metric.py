#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import json
import os
import re
from pathlib import Path

VARIANT = os.environ["VARIANT"]
D = Path(f"build-logs/fa428-cumulative-matrix/candidates/{VARIANT}")
SRC = Path("PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean")
DECL_RE = re.compile(
    r"^(?:protected\s+|private\s+|noncomputable\s+)?"
    r"(?:theorem|lemma|def|abbrev|instance|structure|class)\s+([^\s(:]+)"
)


def error_count(stem: str) -> tuple[int, int, int]:
    path = D / f"{stem}.log"
    text = path.read_text(encoding="utf-8", errors="replace") if path.exists() else ""
    pattern = re.compile(
        rf"{re.escape(stem)}\.lean:(\d+):(\d+):\s+(?:error(?:\([^)]*\))?:"
    )
    matches = list(pattern.finditer(text))
    return (
        len(matches),
        int(matches[0].group(1)) if matches else 0,
        int(matches[0].group(2)) if matches else 0,
    )


def declaration_at(text: str, line: int) -> str:
    if line <= 0:
        return "<none>"
    lines = text.splitlines()
    for i in range(min(line - 1, len(lines) - 1), -1, -1):
        m = DECL_RE.match(lines[i])
        if m:
            return m.group(1)
    return "<unknown>"


data = SRC.read_bytes()
text = data.decode("utf-8")
sha = hashlib.sha256(data).hexdigest()
line_count = data.count(b"\n") + (0 if data.endswith(b"\n") else 1)
metadata = json.loads((D / "CANDIDATE.json").read_text())
fa_errors, first, col = error_count("Mock2_FunctionalAnalysis")
m2_errors, _, _ = error_count("Mock2")
m2a_errors, _, _ = error_count("Mock2_Advanced")
metric = {
    "classification": "VERIFIED",
    "authority": "direct Lean CLI",
    "variant": VARIANT,
    "source_sha256": sha,
    "candidate_metadata_sha256": metadata["candidate_sha256"],
    "source_metadata_identity": sha == metadata["candidate_sha256"],
    "line_count": line_count,
    "target_header_sha256": metadata["target_header_sha256"],
    "Mock2_exit": int(os.environ["M2"]),
    "Mock2_errors": m2_errors,
    "Mock2_Advanced_exit": int(os.environ["M2A"]),
    "Mock2_Advanced_errors": m2a_errors,
    "FA_exit": int(os.environ["FA"]),
    "FA_error_headers_under_cap": fa_errors,
    "FA_first_error_line": first,
    "FA_first_error_col": col,
    "FA_first_error_declaration": declaration_at(text, first),
    "maxErrors_cap": 1,
    "maxErrors_interpretation": "cap only; not total error count or proof progress",
}
(D / "METRIC.json").write_text(json.dumps(metric, indent=2) + "\n")
(D / "METRIC.txt").write_text(
    "\n".join(f"{k}={v}" for k, v in metric.items()) + "\n"
)
print(json.dumps(metric, indent=2))
