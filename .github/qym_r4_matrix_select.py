#!/usr/bin/env python3
from __future__ import annotations

import json
import pathlib
import shutil
import sys

BASE_ERRORS = 5


def score(row: dict[str, object]) -> tuple[object, ...]:
    first = row.get("first_error") or {}
    return (
        0 if row.get("pass") is True else 1,
        int(row.get("error_headers", 10**9)),
        int(row.get("panic_lines", 10**9)),
        -int(first.get("line", 0)),
        str(row.get("variant", "")),
    )


def main() -> None:
    if len(sys.argv) != 3:
        raise SystemExit("usage: select.py ARTIFACT_ROOT OUT")
    root = pathlib.Path(sys.argv[1])
    out = pathlib.Path(sys.argv[2])
    shutil.rmtree(out, ignore_errors=True)
    out.mkdir(parents=True, exist_ok=True)

    rows: list[dict[str, object]] = []
    locations: dict[str, pathlib.Path] = {}
    for result_path in sorted(root.rglob("RESULT.json")):
        row = json.loads(result_path.read_text())
        variant = str(row.get("variant"))
        if variant in locations:
            raise SystemExit(f"duplicate variant artifact: {variant}")
        locations[variant] = result_path.parent
        rows.append(row)
    if len(rows) != 8:
        raise SystemExit(f"expected 8 candidate results, found {len(rows)}")
    eligible = [
        row for row in rows
        if row.get("forbidden_zero") is True and int(row.get("panic_lines", 1)) == 0
    ]
    if not eligible:
        raise SystemExit("no eligible matrix candidate")
    best = min(eligible, key=score)
    best_dir = locations[str(best["variant"])]
    promote = best.get("pass") is True or int(best.get("error_headers", BASE_ERRORS)) < BASE_ERRORS

    for row in rows:
        variant = str(row["variant"])
        variant_out = out / "candidates" / variant
        variant_out.mkdir(parents=True, exist_ok=True)
        source_dir = locations[variant]
        for name in ("RESULT.json", "FORBIDDEN_AUDIT.json", "generator.log", "full.log"):
            source = source_dir / name
            if source.exists():
                shutil.copy2(source, variant_out / name)
    shutil.copy2(best_dir / "QYM.candidate.lean", out / "QYM.best.lean")
    shutil.copy2(best_dir / "full.log", out / "best.full.log")
    selector = {
        "schema": "qym-r4-targeted-matrix-selector-v1",
        "candidate_count": len(rows),
        "eligible_count": len(eligible),
        "base_error_headers": BASE_ERRORS,
        "best": best,
        "promote": promote,
        "true_pass": best.get("pass") is True,
        "ranking": [
            {
                "variant": row.get("variant"),
                "pass": row.get("pass"),
                "error_headers": row.get("error_headers"),
                "panic_lines": row.get("panic_lines"),
                "first_error": row.get("first_error"),
                "source_sha256": row.get("source_sha256"),
                "source_blob": row.get("source_blob"),
            }
            for row in sorted(rows, key=score)
        ],
    }
    (out / "SELECTOR_RESULT.json").write_text(json.dumps(selector, indent=2) + "\n")
    print(json.dumps(selector, indent=2))


if __name__ == "__main__":
    main()
