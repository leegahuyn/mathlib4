#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import hashlib
import json
import shutil
import sys


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def blob(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def dump(path: Path, value: object) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def first_line(row: dict) -> int:
    first = row.get("first_error")
    return int(first["line"]) if first else 10**9


def main() -> int:
    if len(sys.argv) != 3:
        raise SystemExit(f"usage: {Path(sys.argv[0]).name} ARTIFACT_ROOT OUTPUT_DIR")
    root = Path(sys.argv[1])
    out = Path(sys.argv[2])
    out.mkdir(parents=True, exist_ok=True)
    rows: list[dict] = []
    valid: list[tuple[dict, Path]] = []
    baselines: set[tuple[int, str, str]] = set()

    for result_path in sorted(root.rglob("RESULT.json")):
        try:
            row = json.loads(result_path.read_text(encoding="utf-8"))
        except Exception as exc:
            rows.append({"result_path": str(result_path), "parse_error": repr(exc)})
            continue
        row["artifact_result_path"] = str(result_path)
        candidate = result_path.parent / "QYM.candidate.lean"
        row["artifact_candidate_path"] = str(candidate)
        rows.append(row)
        try:
            baseline = (
                int(row["baseline_error_headers"]),
                str(row["baseline_qym_sha256"]),
                str(row["baseline_qym_blob"]),
            )
            baselines.add(baseline)
        except Exception:
            continue
        if not (
            row.get("full_compile_executed") is True
            and int(row.get("panic_lines", 1)) == 0
            and row.get("strict_improvement") is True
            and int(row.get("error_headers", baseline[0])) < baseline[0]
            and candidate.is_file()
        ):
            continue
        raw = candidate.read_bytes()
        if sha(raw) != row.get("candidate_qym_sha256") or blob(raw) != row.get("candidate_qym_blob"):
            continue
        forbidden = row.get("forbidden") or (row.get("patch") or {}).get("forbidden") or {}
        if any(int(value) for value in forbidden.values()):
            continue
        valid.append((row, candidate))

    if len(baselines) > 1:
        raise SystemExit(f"mixed authority baselines in one selector: {sorted(baselines)}")
    baseline_value = next(iter(baselines), None)
    valid.sort(key=lambda pair: (
        int(pair[0]["error_headers"]),
        int(pair[0].get("warning_headers", 10**9)),
        -first_line(pair[0]),
        str(pair[0].get("variant", "")),
    ))
    selection: dict = {
        "schema": "qym-dynamic-selection-v1",
        "baseline": {
            "error_headers": baseline_value[0],
            "qym_sha256": baseline_value[1],
            "qym_blob": baseline_value[2],
        } if baseline_value else None,
        "candidate_result_count": len(rows),
        "valid_strict_improvement_count": len(valid),
        "results": rows,
        "strict_improvement_found": bool(valid),
    }
    if valid:
        best, source = valid[0]
        shutil.copy2(source, out / "QYM.best.lean")
        dump(out / "BEST_RESULT.json", best)
        selection["best_variant"] = best["variant"]
        selection["best"] = best
    dump(out / "SELECTION.json", selection)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
