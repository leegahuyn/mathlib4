#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import hashlib
import json
import re
import sys

ERROR_RE = re.compile(r"(?m)^(?P<file>[^\n]*\.lean):(?P<line>\d+):(?P<col>\d+): error: ?(?P<msg>.*)$")
PANIC_RE = re.compile(r"(?im)^.*(?:panic|internal compiler error|internal error).*$")
FORBIDDEN = {
    "sorry": re.compile(r"\bsorry\b"),
    "admit": re.compile(r"\badmit\b"),
    "native_decide": re.compile(r"\bnative_decide\b"),
    "Lean.ofReduceBool": re.compile(r"Lean\.ofReduceBool"),
    "global_axiom": re.compile(r"(?m)^\s*axiom\s+"),
    "unsafe": re.compile(r"(?m)^\s*unsafe\s+"),
    "maxHeartbeats_zero": re.compile(r"set_option\s+maxHeartbeats\s+0\b"),
}
BASE_ERRORS = 85
BASE_FIRST_LINE = 41515


def git_blob(raw: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest()


def parse_log(log: Path, lean_exit: int, source: Path | None = None) -> dict:
    text = log.read_text(encoding="utf-8", errors="replace")
    errors = [m.groupdict() for m in ERROR_RE.finditer(text)]
    panics = PANIC_RE.findall(text)
    result: dict = {
        "lean_exit": lean_exit,
        "error_headers": len(errors),
        "panic_lines": len(panics),
        "first_error": None,
        "normalized_signatures": sorted({e["msg"].strip() for e in errors}),
        "log_sha256": hashlib.sha256(log.read_bytes()).hexdigest(),
    }
    if errors:
        first = errors[0]
        result["first_error"] = {
            "file": first["file"],
            "line": int(first["line"]),
            "col": int(first["col"]),
            "message": first["msg"].strip(),
        }
    if source is not None:
        raw = source.read_bytes()
        source_text = raw.decode("utf-8")
        result.update({
            "candidate_qym_sha256": hashlib.sha256(raw).hexdigest(),
            "candidate_qym_blob": git_blob(raw),
            "candidate_bytes": len(raw),
            "candidate_lf": raw.count(b"\n"),
            "forbidden": {name: len(regex.findall(source_text)) for name, regex in FORBIDDEN.items()},
        })
    return result


def cmd_parse() -> None:
    if len(sys.argv) not in (5, 6):
        raise SystemExit("usage: metrics.py parse LOG EXIT OUTPUT [SOURCE]")
    log = Path(sys.argv[2])
    exit_code = int(sys.argv[3])
    output = Path(sys.argv[4])
    source = Path(sys.argv[5]) if len(sys.argv) == 6 else None
    value = parse_log(log, exit_code, source)
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(value, indent=2, sort_keys=True))


def cmd_gate() -> None:
    if len(sys.argv) != 4:
        raise SystemExit("usage: metrics.py gate LOCAL_JSON PATCH_JSON")
    local = json.loads(Path(sys.argv[2]).read_text(encoding="utf-8"))
    patch = json.loads(Path(sys.argv[3]).read_text(encoding="utf-8"))
    first = local.get("first_error")
    gate_line = int(patch["gate_line"])
    clean_through_c2 = (
        int(local.get("panic_lines", 1)) == 0
        and (first is None or int(first["line"]) >= gate_line)
    )
    print("true" if clean_through_c2 else "false")


def cmd_select() -> None:
    if len(sys.argv) < 5:
        raise SystemExit("usage: metrics.py select OUTPUT WINNER_PATH VARIANT_DIR...")
    output = Path(sys.argv[2])
    winner_path = Path(sys.argv[3])
    rows: list[dict] = []
    for directory_arg in sys.argv[4:]:
        directory = Path(directory_arg)
        full_path = directory / "full.json"
        if not full_path.exists():
            continue
        full = json.loads(full_path.read_text(encoding="utf-8"))
        variant = directory.name
        first = full.get("first_error")
        first_line = int(first["line"]) if first else 10**12
        forbidden = full.get("forbidden", {})
        forbidden_clean = all(int(v) == 0 for v in forbidden.values())
        actual_success = (
            int(full.get("lean_exit", 1)) == 0
            and int(full.get("error_headers", 1)) == 0
            and int(full.get("panic_lines", 1)) == 0
        )
        strict = (
            int(full.get("panic_lines", 1)) == 0
            and forbidden_clean
            and (
                int(full.get("error_headers", 10**9)) < BASE_ERRORS
                or (
                    int(full.get("error_headers", 10**9)) == BASE_ERRORS
                    and first_line > BASE_FIRST_LINE
                )
            )
        )
        rows.append({
            "variant": variant,
            "directory": str(directory),
            "candidate": str(directory / "QYM.lean"),
            "actual_success": actual_success,
            "strict_improvement": strict,
            **full,
        })
    rows.sort(key=lambda r: (
        int(r.get("panic_lines", 10**9)),
        int(r.get("error_headers", 10**9)),
        int(r.get("first_error", {}).get("line", 10**12)) if r.get("first_error") else 10**12,
        len(r.get("normalized_signatures", [])),
        r["variant"],
    ))
    eligible = [r for r in rows if r["strict_improvement"]]
    best = eligible[0] if eligible else None
    if best is not None:
        winner_path.parent.mkdir(parents=True, exist_ok=True)
        winner_path.write_text(best["candidate"] + "\n", encoding="utf-8")
    value = {
        "schema": "qym-gb85-v8-selection",
        "baseline_error_headers": BASE_ERRORS,
        "baseline_first_error_line": BASE_FIRST_LINE,
        "strict_improvement": best is not None,
        "winner": best,
        "candidates": rows,
    }
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(value, indent=2, sort_keys=True))


def main() -> None:
    if len(sys.argv) < 2:
        raise SystemExit("commands: parse | gate | select")
    command = sys.argv[1]
    if command == "parse":
        cmd_parse()
    elif command == "gate":
        cmd_gate()
    elif command == "select":
        cmd_select()
    else:
        raise SystemExit(f"unknown command: {command}")


if __name__ == "__main__":
    main()
