#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path

TRUST = ("sorry", "admit", "axiom", "unsafe", "native_decide", "Lean.ofReduceBool")
DECL_RE = re.compile(
    r"(?m)^(?:protected\s+|private\s+|noncomputable\s+|local\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance|structure|class)\s+([^\s(:]+)"
)
HEADER_RE = re.compile(
    r"(?m)^(?P<path>.*?):(?P<line>\d+):(?P<col>\d+):\s+"
    r"(?P<severity>error|warning|information):\s*(?P<message>.*)$"
)
CODE_RE = re.compile(r"\[(?P<code>lean\.[A-Za-z0-9_.-]+)\]\s*$")


def strip_noncode(text: str) -> str:
    out = list(text)
    i = 0
    depth = 0
    string = False
    esc = False
    while i < len(out):
        if depth:
            if text.startswith("/-", i):
                out[i] = out[i + 1] = " "
                depth += 1
                i += 2
                continue
            if text.startswith("-/", i):
                out[i] = out[i + 1] = " "
                depth -= 1
                i += 2
                continue
            if out[i] != "\n":
                out[i] = " "
            i += 1
            continue
        if string:
            ch = out[i]
            if ch != "\n":
                out[i] = " "
            if esc:
                esc = False
            elif ch == "\\":
                esc = True
            elif ch == '"':
                string = False
            i += 1
            continue
        if text.startswith("/-", i):
            out[i] = out[i + 1] = " "
            depth = 1
            i += 2
            continue
        if text.startswith("--", i):
            while i < len(out) and out[i] != "\n":
                out[i] = " "
                i += 1
            continue
        if out[i] == '"':
            out[i] = " "
            string = True
        i += 1
    return "".join(out)


def trust_counts(text: str) -> dict[str, int]:
    code = strip_noncode(text)
    return {
        token: len(
            re.findall(
                r"(?<![A-Za-z0-9_])" + re.escape(token) + r"(?![A-Za-z0-9_])",
                code,
            )
        )
        for token in TRUST
    }


def declarations(text: str) -> list[dict[str, int | str]]:
    matches = list(DECL_RE.finditer(text))
    result: list[dict[str, int | str]] = []
    for index, match in enumerate(matches):
        start = match.start()
        end = matches[index + 1].start() if index + 1 < len(matches) else len(text)
        result.append(
            {
                "name": match.group(1),
                "index": index + 1,
                "start_line": text.count("\n", 0, start) + 1,
                "end_line": text.count("\n", 0, end) + 1,
            }
        )
    return result


def declaration_at(rows: list[dict[str, int | str]], line: int) -> dict[str, int | str] | None:
    for row in rows:
        if int(row["start_line"]) <= line <= int(row["end_line"]):
            return row
    return None


def normalize(message: str) -> str:
    message = re.sub(r"0x[0-9a-fA-F]+", "<HEX>", message)
    message = re.sub(r"\b\d+\b", "<N>", message)
    message = re.sub(r"\s+", " ", message).strip()
    return message[:1000]


def parse_diagnostics(log: str, decls: list[dict[str, int | str]]) -> list[dict[str, object]]:
    matches = list(HEADER_RE.finditer(log))
    rows: list[dict[str, object]] = []
    for index, match in enumerate(matches):
        start = match.end()
        end = matches[index + 1].start() if index + 1 < len(matches) else len(log)
        continuation = log[start:end].strip("\n")
        line = int(match.group("line"))
        message = match.group("message").strip()
        code_match = CODE_RE.search(message)
        code = code_match.group("code") if code_match else None
        enclosing = declaration_at(decls, line)
        full = message if not continuation else message + "\n" + continuation
        rows.append(
            {
                "path": match.group("path"),
                "line": line,
                "col": int(match.group("col")),
                "severity": match.group("severity"),
                "message": full,
                "first_line_message": message,
                "normalized_message": normalize(full),
                "code": code,
                "declaration": enclosing["name"] if enclosing else None,
                "declaration_index": enclosing["index"] if enclosing else None,
            }
        )
    return rows


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--log", type=Path, required=True)
    parser.add_argument("--exit-file", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--label", required=True)
    parser.add_argument("--max-errors", type=int, default=2000)
    args = parser.parse_args()

    if not args.source.exists():
        raise SystemExit(f"source missing: {args.source}")
    if not args.log.exists():
        raise SystemExit(f"raw Lean log missing: {args.log}")
    if not args.exit_file.exists():
        raise SystemExit(f"Lean exit file missing: {args.exit_file}")

    exit_text = args.exit_file.read_text().strip()
    if not exit_text.isdigit():
        raise SystemExit(f"invalid Lean exit: {exit_text!r}")
    lean_exit = int(exit_text)
    raw = args.source.read_bytes()
    text = raw.decode()
    log = args.log.read_text(errors="replace")
    decls = declarations(text)
    diagnostic_rows = parse_diagnostics(log, decls)
    errors = [row for row in diagnostic_rows if row["severity"] == "error"]
    warnings = [row for row in diagnostic_rows if row["severity"] == "warning"]
    trust = trust_counts(text)
    sorry_warnings = [
        row
        for row in warnings
        if "declaration uses 'sorry'" in str(row.get("message", ""))
        or "declaration uses ‘sorry’" in str(row.get("message", ""))
    ]
    unique_declarations = sorted(
        {str(row["declaration"]) for row in errors if row.get("declaration")}
    )
    unique_signatures = sorted({str(row["normalized_message"]) for row in errors})
    first = errors[0] if errors else None
    cap_sentinel = any(
        "maximum number of errors" in str(row.get("message", "")).lower()
        for row in diagnostic_rows
    )

    args.out.mkdir(parents=True, exist_ok=True)
    diagnostics_path = args.out / "DIAGNOSTICS.jsonl"
    diagnostics_path.write_text(
        "".join(json.dumps(row, ensure_ascii=False, sort_keys=True) + "\n" for row in diagnostic_rows)
    )
    metric = {
        "schema": "lean-exact-diagnostic-metric-v1",
        "label": args.label,
        "source_path": str(args.source),
        "source_sha256": hashlib.sha256(raw).hexdigest(),
        "source_bytes": len(raw),
        "source_lines": len(text.splitlines()),
        "source_declaration_count": len(decls),
        "source_executable_trust_counts": trust,
        "source_executable_trust_six_zero": all(value == 0 for value in trust.values()),
        "lean_exit": lean_exit,
        "compiler_exit_clean": lean_exit == 0,
        "direct_lean_verified": True,
        "diagnostic_headers_captured": len(diagnostic_rows),
        "error_headers_captured": len(errors),
        "warning_headers_captured": len(warnings),
        "compile_max_errors": args.max_errors,
        "error_cap_sentinel_present": cap_sentinel,
        "inventory_complete_by_header_evidence": not cap_sentinel and len(errors) < args.max_errors,
        "first_actual_error_line": first.get("line") if first else None,
        "first_actual_error_col": first.get("col") if first else None,
        "first_error_message": first.get("first_line_message") if first else None,
        "first_error_code": first.get("code") if first else None,
        "first_error_declaration": first.get("declaration") if first else None,
        "first_error_declaration_index": first.get("declaration_index") if first else None,
        "unique_declarations_with_errors": len(unique_declarations),
        "unique_error_declarations": unique_declarations,
        "unique_normalized_message_signatures": len(unique_signatures),
        "normalized_message_signatures": unique_signatures,
        "synthetic_declaration_uses_sorry_warning_count": len(sorry_warnings),
        "semantic_clean": lean_exit == 0 and not errors,
        "raw_log_sha256": hashlib.sha256(args.log.read_bytes()).hexdigest(),
        "diagnostics_sha256": hashlib.sha256(diagnostics_path.read_bytes()).hexdigest(),
    }
    (args.out / "METRIC.json").write_text(
        json.dumps(metric, ensure_ascii=False, indent=2, sort_keys=True) + "\n"
    )
    gate = {
        "schema": "lean-exact-final-gate-v1",
        "label": args.label,
        "source_sha256": metric["source_sha256"],
        "lean_exit": lean_exit,
        "direct_lean_verified": True,
        "error_count": len(errors),
        "first_error_line": metric["first_actual_error_line"],
        "first_error_col": metric["first_actual_error_col"],
        "first_error_declaration": metric["first_error_declaration"],
        "first_error_declaration_index": metric["first_error_declaration_index"],
        "unique_error_declarations": len(unique_declarations),
        "unique_signatures": len(unique_signatures),
        "trust_six_zero": metric["source_executable_trust_six_zero"],
        "synthetic_sorry_count": len(sorry_warnings),
        "status": "PASS"
        if lean_exit == 0
        and not errors
        and metric["source_executable_trust_six_zero"]
        and not sorry_warnings
        else "FAIL",
    }
    (args.out / "FINAL_GATE.json").write_text(
        json.dumps(gate, ensure_ascii=False, indent=2, sort_keys=True) + "\n"
    )
    print(json.dumps(metric, ensure_ascii=False, indent=2, sort_keys=True))
    print(json.dumps(gate, ensure_ascii=False, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
