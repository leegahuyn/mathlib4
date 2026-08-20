#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import hashlib
import json
import shutil
import sys

BASE_ERRORS = 77


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def blob(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def dump(path: Path, value: object) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def first_line(row: dict) -> int:
    first = row.get("first_error")
    return int(first["line"]) if first else 10**9


def compile_cost(row: dict) -> float:
    local = row.get("local") or {}
    full = row.get("full") or {}
    return float(local.get("elapsed_seconds", 10**9)) + float(
        full.get("elapsed_seconds", 10**9)
    )


def main() -> int:
    if len(sys.argv) != 3:
        raise SystemExit(f"usage: {Path(sys.argv[0]).name} ARTIFACT_ROOT OUTPUT_DIR")
    root = Path(sys.argv[1])
    out = Path(sys.argv[2])
    out.mkdir(parents=True, exist_ok=True)
    rows: list[dict] = []
    valid: list[tuple[dict, Path]] = []
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
        if not (
            row.get("full_compile_executed") is True
            and int(row.get("panic_lines", 1)) == 0
            and row.get("strict_improvement") is True
            and int(row.get("error_headers", BASE_ERRORS)) < BASE_ERRORS
            and candidate.is_file()
        ):
            continue
        raw = candidate.read_bytes()
        if sha(raw) != row.get("candidate_qym_sha256") or blob(raw) != row.get("candidate_qym_blob"):
            continue
        forbidden = (row.get("patch") or {}).get("forbidden") or {}
        if any(int(v) for v in forbidden.values()):
            continue
        valid.append((row, candidate))

    # One monotone frontier only.  After the authoritative mathematical
    # metrics, prefer the smaller exact source as the simpler proof, then the
    # lower observed direct-Lean cost.  Variant names are only a final stable
    # deterministic tie-break and never evidence by themselves.
    valid.sort(key=lambda pair: (
        int(pair[0]["error_headers"]),
        int(pair[0].get("warning_headers", 10**9)),
        -first_line(pair[0]),
        pair[1].stat().st_size,
        compile_cost(pair[0]),
        str(pair[0].get("variant", "")),
    ))
    selection: dict = {
        "schema": "qym-gb77-v14-right-normal-im-selection-v2",
        "baseline_error_headers": BASE_ERRORS,
        "candidate_result_count": len(rows),
        "valid_strict_improvement_count": len(valid),
        "tie_break": [
            "error_headers",
            "warning_headers",
            "later_first_error",
            "smaller_exact_source",
            "lower_direct_lean_cost",
            "variant_name_final_only",
        ],
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
