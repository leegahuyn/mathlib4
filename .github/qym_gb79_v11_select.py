#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import hashlib
import json
import shutil
import sys

BASE_ERRORS = 79


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def rank(row: dict[str, object]) -> tuple[int, int, int, int, int, str]:
    result = row["result"]
    first = result.get("first_error") or {}
    first_line = int(first.get("line") or 0) if isinstance(first, dict) else 0
    codes = result.get("error_codes") or {}
    synth = int(codes.get("lean.synthInstanceFailed", 0)) if isinstance(codes, dict) else 0
    return (
        0 if bool(result.get("semantic_pass")) else 1,
        int(result.get("error_headers", 10**9)),
        int(result.get("panic_lines", 10**9)),
        synth,
        -first_line,
        str(result.get("variant") or ""),
    )


def main() -> int:
    if len(sys.argv) != 3:
        raise SystemExit("usage: qym_gb79_v11_select.py DOWNLOADED_ROOT OUT_DIR")
    root = Path(sys.argv[1])
    out = Path(sys.argv[2])
    out.mkdir(parents=True, exist_ok=True)

    rows: list[dict[str, object]] = []
    rejected: list[dict[str, object]] = []
    for result_path in sorted(root.rglob("RESULT.json")):
        try:
            result = json.loads(result_path.read_text(encoding="utf-8"))
        except Exception as exc:
            rejected.append({"result_file": str(result_path), "reason": f"json: {exc}"})
            continue
        if not isinstance(result, dict):
            rejected.append({"result_file": str(result_path), "reason": "not an object"})
            continue
        variant = str(result.get("variant") or result_path.parent.name)
        source = result_path.parent / f"QYM.candidate-{variant}.lean"
        if not source.is_file():
            rejected.append({"result_file": str(result_path), "reason": "candidate source absent"})
            continue
        expected = result.get("candidate_qym_sha256")
        actual = sha256(source)
        if expected != actual:
            rejected.append({
                "result_file": str(result_path),
                "reason": "candidate SHA mismatch",
                "expected": expected,
                "actual": actual,
            })
            continue
        rows.append({"result_file": str(result_path), "source_file": str(source), "result": result})

    eligible = [
        row for row in rows
        if int(row["result"].get("panic_lines", 1)) == 0
        and (
            bool(row["result"].get("semantic_pass"))
            or int(row["result"].get("error_headers", BASE_ERRORS)) < BASE_ERRORS
        )
    ]
    eligible.sort(key=rank)

    selection: dict[str, object] = {
        "schema": "qym-gb79-v11-selection-v1",
        "baseline_error_headers": BASE_ERRORS,
        "candidate_count": len(rows),
        "eligible_count": len(eligible),
        "strict_improvement_found": bool(eligible),
        "candidates": [row["result"] for row in sorted(rows, key=rank)],
        "rejected": rejected,
    }
    if eligible:
        best = eligible[0]
        result = best["result"]
        selection["best_variant"] = result.get("variant")
        selection["best"] = result
        shutil.copy2(Path(best["source_file"]), out / "QYM.best.lean")
        write_json(out / "BEST_RESULT.json", result)
    write_json(out / "SELECTION.json", selection)
    print(json.dumps(selection, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
