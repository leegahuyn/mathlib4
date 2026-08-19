#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import json
import shutil
import sys

BASE_ERRORS = 85
BASE_FIRST_LINE = 41515


def first_line(row: dict) -> int:
    first = row.get("first_error")
    return int(first["line"]) if isinstance(first, dict) and first.get("line") is not None else 10**12


def forbidden_clean(row: dict) -> bool:
    values = row.get("forbidden") or {}
    return bool(values) and all(int(value) == 0 for value in values.values())


def strict(row: dict) -> bool:
    errors = int(row.get("error_headers", 10**9))
    return (
        int(row.get("panic_lines", 1)) == 0
        and forbidden_clean(row)
        and (
            errors < BASE_ERRORS
            or (errors == BASE_ERRORS and first_line(row) > BASE_FIRST_LINE)
        )
    )


def rank(row: dict) -> tuple:
    return (
        int(row.get("panic_lines", 10**9)),
        int(row.get("error_headers", 10**9)),
        -first_line(row),
        len(row.get("normalized_signatures") or []),
        str(row.get("variant") or ""),
    )


def main() -> None:
    if len(sys.argv) != 5:
        raise SystemExit("usage: select.py DOWNLOAD_ROOT RESULT_JSON WINNER_LEAN WINNER_PATH")
    root = Path(sys.argv[1])
    result_path = Path(sys.argv[2])
    winner_lean = Path(sys.argv[3])
    winner_path = Path(sys.argv[4])

    rows: list[dict] = []
    for full_path in root.rglob("full.json"):
        try:
            row = json.loads(full_path.read_text(encoding="utf-8"))
        except Exception:
            continue
        directory = full_path.parent
        variant_file = directory / "variant.txt"
        variant = variant_file.read_text(encoding="utf-8").strip() if variant_file.exists() else directory.name
        candidate = directory / "QYM.lean"
        row.update({
            "variant": variant,
            "artifact_directory": str(directory),
            "candidate_path": str(candidate),
            "strict_improvement": strict(row),
            "actual_zero_error": (
                int(row.get("lean_exit", 1)) == 0
                and int(row.get("error_headers", 1)) == 0
                and int(row.get("panic_lines", 1)) == 0
            ),
        })
        rows.append(row)

    diagnostics: list[dict] = []
    for local_path in root.rglob("local.json"):
        directory = local_path.parent
        if (directory / "full.json").exists():
            continue
        try:
            local = json.loads(local_path.read_text(encoding="utf-8"))
        except Exception:
            continue
        variant_file = directory / "variant.txt"
        variant = variant_file.read_text(encoding="utf-8").strip() if variant_file.exists() else directory.name
        diagnostics.append({"variant": variant, "local_only": True, **local})

    rows.sort(key=rank)
    eligible = [row for row in rows if row["strict_improvement"]]
    winner = eligible[0] if eligible else None
    if winner is not None:
        source = Path(winner["candidate_path"])
        if not source.exists():
            raise SystemExit(f"winner source missing: {source}")
        winner_lean.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, winner_lean)
        winner_path.parent.mkdir(parents=True, exist_ok=True)
        winner_path.write_text(str(source) + "\n", encoding="utf-8")

    result = {
        "schema": "qym-gb85-c2-v12-parallel-selection",
        "baseline_error_headers": BASE_ERRORS,
        "baseline_first_error_line": BASE_FIRST_LINE,
        "full_compile_executed": bool(rows),
        "strict_improvement": winner is not None,
        "actual_zero_error": bool(winner and winner["actual_zero_error"]),
        "winner": winner,
        "candidates": rows,
        "local_only_diagnostics": diagnostics,
    }
    result_path.parent.mkdir(parents=True, exist_ok=True)
    result_path.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
