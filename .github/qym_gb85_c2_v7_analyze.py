#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import collections
import hashlib
import json
import os
import re
import shutil
import sys
from typing import Any

HEADER_RE = re.compile(
    r"^(?P<file>.*?\.lean):(?P<line>\d+):(?P<column>\d+): "
    r"(?P<severity>error|warning)(?:\((?P<code>[^)]*)\))?:\s*"
    r"(?P<message>.*)$",
    re.M,
)
PANIC_RE = re.compile(
    r"(?im)^.*(?:internal error|uncaught exception|panic(?:!|:|\s)).*$"
)


def sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def git_blob(raw: bytes) -> str:
    return hashlib.sha1(
        b"blob " + str(len(raw)).encode() + b"\0" + raw
    ).hexdigest()


def write_json(path: Path, value: Any) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


def read_json(path: Path) -> Any:
    return json.loads(path.read_text())


def parse_headers(text: str) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for match in HEADER_RE.finditer(text):
        row: dict[str, Any] = match.groupdict()
        row["line"] = int(row["line"])
        row["column"] = int(row["column"])
        rows.append(row)
    return rows


def recover(argv: list[str]) -> None:
    if len(argv) != 5:
        raise SystemExit(
            "recover ARTIFACT_DIR OUTPUT EXPECTED_SHA EXPECTED_BLOB EXPECTED_ERRORS"
        )
    root = Path(argv[0])
    output = Path(argv[1])
    expected_sha = argv[2]
    expected_blob = argv[3]
    expected_errors = int(argv[4])

    sources: list[Path] = []
    for path in root.rglob("*.lean"):
        raw = path.read_bytes()
        if sha256(raw) == expected_sha and git_blob(raw) == expected_blob:
            sources.append(path)
    if len(sources) != 1:
        raise SystemExit(f"exact GB85 source count={len(sources)}")

    results: list[tuple[Path, dict[str, Any]]] = []
    for path in root.rglob("RESULT.json"):
        try:
            value = read_json(path)
        except Exception:
            continue
        if not isinstance(value, dict):
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
    write_json(output.parent / "GB85_RESULT.json", results[0][1])
    value = {
        "source": str(sources[0]),
        "result": str(results[0][0]),
        "sha256": expected_sha,
        "blob": expected_blob,
        "errors": expected_errors,
    }
    write_json(output.parent / "RECOVERY.json", value)
    print(json.dumps(value, indent=2, sort_keys=True))


def local_result(argv: list[str]) -> None:
    if len(argv) != 1:
        raise SystemExit("local DIRECTORY")
    directory = Path(argv[0])
    patch = read_json(directory / "PATCH_RESULT.json")
    raw = (directory / "local.log").read_bytes()
    text = raw.decode(errors="replace")
    rows = parse_headers(text)
    errors = [row for row in rows if row["severity"] == "error"]
    panics = PANIC_RE.findall(text)
    rc = int((directory / "local.exit").read_text().strip())
    gate = int(patch["gate_line"])
    first = errors[0] if errors else None
    fixed = not panics and (
        rc == 0 or (first is not None and int(first["line"]) >= gate)
    )
    value = {
        "schema": "qym-gb85-c2-v7-local",
        "variant": patch["variant"],
        "exit": rc,
        "gate_line": gate,
        "error_headers": len(errors),
        "first_error": first,
        "panic_lines": len(panics),
        "log_sha256": sha256(raw),
        "c2_fixed": fixed,
    }
    write_json(directory / "LOCAL_RESULT.json", value)
    print(json.dumps(value, indent=2, sort_keys=True))


def full_result(argv: list[str]) -> None:
    if len(argv) != 2:
        raise SystemExit("full DIRECTORY BASELINE_ERRORS")
    directory = Path(argv[0])
    baseline_errors = int(argv[1])
    patch = read_json(directory / "PATCH_RESULT.json")
    candidate = directory / "QYM.candidate.lean"

    executed = (
        (directory / "full.log").is_file()
        and (directory / "full.exit").is_file()
        and (directory / "full.log").stat().st_size > 0
    )
    raw = (directory / "full.log").read_bytes() if executed else b""
    text = raw.decode(errors="replace")
    rows = parse_headers(text)
    errors = [row for row in rows if row["severity"] == "error"]
    warnings = [row for row in rows if row["severity"] == "warning"]
    panics = PANIC_RE.findall(text)
    rc = int((directory / "full.exit").read_text()) if executed else None
    olean_ok = (directory / "QYM.olean").is_file() and (directory / "QYM.olean").stat().st_size > 0
    ilean_ok = (directory / "QYM.ilean").is_file() and (directory / "QYM.ilean").stat().st_size > 0
    semantic_pass = bool(
        executed and rc == 0 and not errors and not panics and olean_ok and ilean_ok
    )
    strict = bool(
        executed
        and (
            semantic_pass
            or (not panics and len(errors) < baseline_errors)
        )
    )
    candidate_raw = candidate.read_bytes()
    candidate_sha = sha256(candidate_raw)
    candidate_blob = git_blob(candidate_raw)
    if candidate_sha != patch["candidate_sha256"]:
        raise SystemExit("candidate SHA256 changed after patch")
    if candidate_blob != patch["candidate_blob"]:
        raise SystemExit("candidate blob changed after patch")

    value = {
        "schema": "qym-gb85-c2-v7-result",
        "run_id": int(os.environ["GITHUB_RUN_ID"]),
        "run_attempt": int(os.environ.get("GITHUB_RUN_ATTEMPT", "1")),
        "trigger_sha": os.environ["GITHUB_SHA"],
        "variant": patch["variant"],
        "baseline_qym_sha256": os.environ["BASE_SHA256"],
        "baseline_qym_blob": os.environ["BASE_BLOB"],
        "baseline_error_headers": baseline_errors,
        "candidate_qym_sha256": candidate_sha,
        "candidate_qym_blob": candidate_blob,
        "forbidden": patch["forbidden"],
        "full_compile_executed": executed,
        "exit": rc,
        "error_headers": len(errors) if executed else None,
        "warning_headers": len(warnings) if executed else None,
        "panic_lines": len(panics) if executed else None,
        "first_error": errors[0] if errors else None,
        "last_error": errors[-1] if errors else None,
        "error_codes": dict(sorted(collections.Counter(
            row["code"] or "uncoded" for row in errors
        ).items())) if executed else {},
        "log_sha256": sha256(raw) if executed else None,
        "olean_exists": olean_ok,
        "ilean_exists": ilean_ok,
        "semantic_pass": semantic_pass,
        "strict_improvement": strict,
    }
    write_json(directory / "RESULT.json", value)
    (directory / "diagnostics.jsonl").write_text(
        "".join(json.dumps(row, sort_keys=True) + "\n" for row in rows)
    )
    (directory / "error-headers.txt").write_text(
        "".join(
            f"{row['file']}:{row['line']}:{row['column']}: error"
            f"{('(' + row['code'] + ')') if row['code'] else ''}: "
            f"{row['message']}\n"
            for row in errors
        )
    )
    print(json.dumps(value, indent=2, sort_keys=True))


def select_result(argv: list[str]) -> None:
    if len(argv) < 3:
        raise SystemExit("select OUT BASELINE_ERRORS VARIANT [VARIANT ...]")
    out = Path(argv[0])
    baseline_errors = int(argv[1])
    variants = argv[2:]
    inspected: list[dict[str, Any]] = []
    eligible: list[tuple[tuple[int, int, int, str], str, dict[str, Any]]] = []

    for variant in variants:
        directory = out / variant
        result_path = directory / "RESULT.json"
        if not result_path.is_file():
            inspected.append({"variant": variant, "result": "missing"})
            continue
        value = read_json(result_path)
        inspected.append({
            "variant": variant,
            "full_compile_executed": value.get("full_compile_executed"),
            "exit": value.get("exit"),
            "error_headers": value.get("error_headers"),
            "panic_lines": value.get("panic_lines"),
            "first_error": value.get("first_error"),
            "semantic_pass": value.get("semantic_pass"),
            "strict_improvement": value.get("strict_improvement"),
        })
        forbidden = value.get("forbidden", {})
        forbidden_total = sum(int(item) for item in forbidden.values())
        if not (
            value.get("full_compile_executed")
            and int(value.get("panic_lines", -1)) == 0
            and forbidden_total == 0
            and value.get("strict_improvement")
        ):
            continue
        error_count = int(value.get("error_headers", baseline_errors + 1))
        first = value.get("first_error")
        first_line = int(first.get("line", 0)) if isinstance(first, dict) else 10**9
        rank = (
            0 if value.get("semantic_pass") else 1,
            error_count,
            -first_line,
            variant,
        )
        eligible.append((rank, variant, value))

    eligible.sort(key=lambda item: item[0])
    selected_variant: str | None = None
    selected_value: dict[str, Any] | None = None
    if eligible:
        _, selected_variant, selected_value = eligible[0]
        source = out / selected_variant / "QYM.candidate.lean"
        shutil.copy2(source, out / "QYM.SELECTED.lean")
        write_json(out / "SELECTED_RESULT.json", selected_value)

    selection = {
        "schema": "qym-gb85-c2-v7-selection",
        "run_id": int(os.environ["GITHUB_RUN_ID"]),
        "baseline_error_headers": baseline_errors,
        "selected": selected_variant,
        "selected_result": selected_value,
        "inspected": inspected,
    }
    write_json(out / "SELECTION.json", selection)
    print(json.dumps(selection, indent=2, sort_keys=True))


def main() -> None:
    if len(sys.argv) < 2:
        raise SystemExit("expected subcommand: recover | local | full | select")
    command = sys.argv[1]
    argv = sys.argv[2:]
    if command == "recover":
        recover(argv)
    elif command == "local":
        local_result(argv)
    elif command == "full":
        full_result(argv)
    elif command == "select":
        select_result(argv)
    else:
        raise SystemExit(f"unknown subcommand: {command}")


if __name__ == "__main__":
    main()
