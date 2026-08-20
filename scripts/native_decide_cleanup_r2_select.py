#!/usr/bin/env python3
from __future__ import annotations

import json
import pathlib
import shutil
import sys


def score(row: dict[str, object]) -> tuple[object, ...]:
    mock = row.get("files", {}).get("Mock1_Advanced", {})
    first = mock.get("first_error") or {}
    return (
        0 if row.get("pass") is True else 1,
        int(row.get("total_error_headers", 10**9)),
        int(row.get("total_panic_lines", 10**9)),
        -int(first.get("line", 0)),
        str(row.get("variant", "")),
    )


def main() -> None:
    if len(sys.argv) != 3:
        raise SystemExit("usage: select.py DOWNLOAD_ROOT OUT")
    root = pathlib.Path(sys.argv[1])
    out = pathlib.Path(sys.argv[2])
    shutil.rmtree(out, ignore_errors=True)
    out.mkdir(parents=True, exist_ok=True)

    rows: list[dict[str, object]] = []
    locations: dict[str, pathlib.Path] = {}
    for path in sorted(root.rglob("RESULT.json")):
        row = json.loads(path.read_text())
        variant = str(row.get("variant"))
        if not variant or variant in locations:
            raise SystemExit(f"invalid or duplicate variant: {variant!r}")
        rows.append(row)
        locations[variant] = path.parent
    if len(rows) != 4:
        raise SystemExit(f"expected four candidate results, found {len(rows)}")
    best = min(rows, key=score)
    best_dir = locations[str(best["variant"])]
    shutil.copy2(best_dir / "candidate/Spt1.lean", out / "Spt1.best.lean")
    shutil.copy2(best_dir / "candidate/Mock1_Advanced.lean", out / "Mock1_Advanced.best.lean")
    shutil.copy2(best_dir / "Spt1.log", out / "Spt1.best.log")
    shutil.copy2(best_dir / "Mock1_Advanced.log", out / "Mock1_Advanced.best.log")

    ranking = []
    for row in sorted(rows, key=score):
        mock = row["files"]["Mock1_Advanced"]
        ranking.append({
            "variant": row["variant"],
            "pass": row["pass"],
            "total_error_headers": row["total_error_headers"],
            "total_panic_lines": row["total_panic_lines"],
            "mock1_advanced_first_error": mock.get("first_error"),
            "mock1_advanced_sha256": mock.get("source_sha256"),
            "mock1_advanced_blob": mock.get("source_blob"),
        })
    selector = {
        "schema": "final13-native-decide-cleanup-r2-selector-v1",
        "candidate_count": len(rows),
        "best": best,
        "true_pass": best.get("pass") is True,
        "promote": best.get("pass") is True,
        "ranking": ranking,
    }
    (out / "SELECTOR_RESULT.json").write_text(json.dumps(selector, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "true_pass": selector["true_pass"],
        "promote": selector["promote"],
        "ranking": ranking,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
