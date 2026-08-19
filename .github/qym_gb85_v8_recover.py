#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import hashlib
import json
import shutil
import sys


def git_blob(raw: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest()


def main() -> None:
    if len(sys.argv) != 6:
        raise SystemExit(
            "usage: qym_gb85_v8_recover.py ARTIFACT_DIR OUTPUT SHA256 BLOB ERRORS"
        )
    root = Path(sys.argv[1])
    output = Path(sys.argv[2])
    expected_sha = sys.argv[3]
    expected_blob = sys.argv[4]
    expected_errors = int(sys.argv[5])

    sources: list[Path] = []
    for path in root.rglob("*.lean"):
        raw = path.read_bytes()
        if hashlib.sha256(raw).hexdigest() == expected_sha and git_blob(raw) == expected_blob:
            sources.append(path)
    if len(sources) != 1:
        raise SystemExit(f"exact GB85 source count={len(sources)}")

    results: list[tuple[Path, dict]] = []
    for path in root.rglob("RESULT.json"):
        try:
            value = json.loads(path.read_text(encoding="utf-8"))
        except Exception:
            continue
        if (
            value.get("candidate_qym_sha256") == expected_sha
            and value.get("candidate_qym_blob") == expected_blob
            and int(value.get("error_headers", -1)) == expected_errors
            and int(value.get("panic_lines", -1)) == 0
            and bool(value.get("full_compile_executed", True))
        ):
            results.append((path, value))
    if len(results) != 1:
        raise SystemExit(f"verified GB85 RESULT count={len(results)}")

    output.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(sources[0], output)
    (output.parent / "GB85_RESULT.json").write_text(
        json.dumps(results[0][1], indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(json.dumps({
        "source": str(sources[0]),
        "output": str(output),
        "sha256": expected_sha,
        "blob": expected_blob,
        "errors": expected_errors,
        "result": str(results[0][0]),
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
