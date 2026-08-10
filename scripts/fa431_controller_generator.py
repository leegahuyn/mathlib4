#!/usr/bin/env python3
from __future__ import annotations

import argparse
import re
import subprocess
from pathlib import Path

ERROR_RE = re.compile(r"Mock2_FunctionalAnalysis\.lean:(\d+):(\d+):\s+(?:error(?:\([^)]*\))?:|error:)")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--baseline", required=True)
    parser.add_argument("--output", required=True)
    parser.add_argument("--refs", required=True)
    parser.add_argument("--limit", type=int, default=14)
    args = parser.parse_args()

    logs = [
        Path("build-logs/fa425-strict-theorem-tournament/FA-baseline-direct.log"),
        Path("build-logs/fa425-strict-theorem-tournament/Mock2_FunctionalAnalysis-baseline.log"),
    ]
    first = 0
    for log in logs:
        if not log.exists():
            continue
        match = ERROR_RE.search(log.read_text(encoding="utf-8", errors="replace"))
        if match:
            first = int(match.group(1))
            break
    if not first:
        baseline_json = Path("build-logs/fa425-strict-theorem-tournament/BASELINE.json")
        if baseline_json.exists():
            import json
            data = json.loads(baseline_json.read_text(encoding="utf-8"))
            row = data.get("FA") or data.get("baseline") or {}
            first = int(row.get("first_error_line", 0))
    if not first:
        raise SystemExit("cannot recover direct baseline first-error line for evidence donor mining")

    command = [
        "python3", "scripts/fa431_evidence_donor_candidates.py",
        "--baseline", args.baseline,
        "--output", args.output,
        "--refs", args.refs,
        "--first-error-line", str(first),
        "--limit", str(args.limit),
    ]
    raise SystemExit(subprocess.run(command, check=False).returncode)


if __name__ == "__main__":
    main()
