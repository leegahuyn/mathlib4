#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import json
import shutil
import sys


def first_line(row: dict) -> int:
    first = row.get("first_error")
    return int(first["line"]) if isinstance(first, dict) and first.get("line") is not None else 10**12


def rank(row: dict) -> tuple:
    return (
        int(row.get("panic_lines", 10**9)),
        int(row.get("error_headers", 10**9)),
        -first_line(row),
        len(row.get("normalized_signatures") or []),
    )


def forbidden_clean(row: dict) -> bool:
    values = row.get("forbidden") or {}
    return bool(values) and all(int(value) == 0 for value in values.values())


def main() -> None:
    if len(sys.argv) != 5:
        raise SystemExit("usage: select.py DOWNLOAD_ROOT FRONTIER_JSON RESULT_JSON WINNER_LEAN")
    root = Path(sys.argv[1])
    frontier = json.loads(Path(sys.argv[2]).read_text(encoding="utf-8"))
    result_path = Path(sys.argv[3])
    winner_path = Path(sys.argv[4])
    starting_rank = rank(frontier)

    rows: list[dict] = []
    local_only: list[dict] = []
    for local_path in root.rglob("local.json"):
        directory = local_path.parent
        try:
            local = json.loads(local_path.read_text(encoding="utf-8"))
        except Exception:
            continue
        metadata_path = directory / "metadata.json"
        metadata = json.loads(metadata_path.read_text(encoding="utf-8")) if metadata_path.exists() else {"name": directory.name}
        full_path = directory / "full.json"
        if not full_path.exists():
            local_only.append({"metadata": metadata, "local": local})
            continue
        full = json.loads(full_path.read_text(encoding="utf-8"))
        candidate = directory / "QYM.lean"
        strict = (
            int(full.get("panic_lines", 1)) == 0
            and forbidden_clean(full)
            and rank(full) < starting_rank
        )
        actual_zero = (
            int(full.get("lean_exit", 1)) == 0
            and int(full.get("error_headers", 1)) == 0
            and int(full.get("panic_lines", 1)) == 0
            and forbidden_clean(full)
        )
        rows.append({
            "metadata": metadata,
            "candidate_path": str(candidate),
            "strict_improvement": strict,
            "actual_zero_error": actual_zero,
            **full,
        })

    rows.sort(key=rank)
    eligible = [row for row in rows if row["strict_improvement"]]
    winner = eligible[0] if eligible else None
    if winner is not None:
        source = Path(winner["candidate_path"])
        if not source.exists():
            raise SystemExit(f"winner source missing: {source}")
        winner_path.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, winner_path)

    result = {
        "schema": "qym-gb85-v15-generic-frontier-selection",
        "starting_frontier": frontier,
        "full_compile_executed": bool(rows),
        "strict_improvement": winner is not None,
        "actual_zero_error": bool(winner and winner["actual_zero_error"]),
        "winner": winner,
        "candidates": rows,
        "local_only_diagnostics": local_only,
    }
    result_path.parent.mkdir(parents=True, exist_ok=True)
    result_path.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
