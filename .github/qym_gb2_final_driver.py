#!/usr/bin/env python3
from __future__ import annotations

import bisect
import collections
import hashlib
import json
import os
import pathlib
import re
import shutil
import subprocess
import sys
import time

QYM = pathlib.Path(os.environ.get("QYM", "PrimalitySheafVerification/QYM.lean"))
PATCH = pathlib.Path(os.environ.get("PATCH", ".github/qym_patch_gb2_final.py"))
OUT = pathlib.Path(os.environ.get("OUT", "/tmp/qym-gb2-final-v1"))
BASE_SHA256 = "1e545a316c33741875b5c0ca252105f5a0d858f327b44b0e79e8e5193a7986d4"
BASE_ERRORS = 2


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git_blob(path: pathlib.Path) -> str:
    raw = path.read_bytes()
    return hashlib.sha1(f"blob {len(raw)}\0".encode() + raw).hexdigest()


def code_only(text: str) -> tuple[str, int]:
    out: list[str] = []
    i = 0
    depth = 0
    in_string = False
    in_line_comment = False
    while i < len(text):
        if in_line_comment:
            if text[i] == "\n":
                in_line_comment = False
                out.append("\n")
            else:
                out.append(" ")
            i += 1
            continue
        if depth:
            if text.startswith("/-", i):
                depth += 1
                out.extend("  ")
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                out.extend("  ")
                i += 2
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
            continue
        if in_string:
            if text[i] == "\\" and i + 1 < len(text):
                out.extend("  ")
                i += 2
            elif text[i] == '"':
                in_string = False
                out.append(" ")
                i += 1
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
            continue
        if text.startswith("--", i):
            in_line_comment = True
            out.extend("  ")
            i += 2
        elif text.startswith("/-", i):
            depth = 1
            out.extend("  ")
            i += 2
        elif text[i] == '"':
            in_string = True
            out.append(" ")
            i += 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out), depth


def audit_candidate(candidate: pathlib.Path) -> dict[str, object]:
    code, depth = code_only(candidate.read_text())
    patterns = {
        "sorry": r"\bsorry\b",
        "admit": r"\badmit\b",
        "unsafe": r"\bunsafe\b",
        "native_decide": r"\bnative_decide\b",
        "Lean.ofReduceBool": r"\bLean\.ofReduceBool\b",
        "axiom": r"(?m)^\s*(?:public\s+|private\s+)?axiom\b",
        "maxHeartbeats_zero": r"\bmaxHeartbeats\s*(?::=|=)\s*0\b",
    }
    counts = {
        name: len(re.findall(pattern, code))
        for name, pattern in patterns.items()
    }
    ok = depth == 0 and all(value == 0 for value in counts.values())
    result = {
        "forbidden_zero": ok,
        "counts": counts,
        "comment_depth": depth,
    }
    (OUT / "FORBIDDEN_AUDIT.json").write_text(
        json.dumps(result, indent=2) + "\n"
    )
    if not ok:
        raise SystemExit(json.dumps(result, indent=2))
    return result


def parse_errors(candidate: pathlib.Path, log_text: str) -> list[dict[str, object]]:
    lines = candidate.read_text().splitlines()
    decl_re = re.compile(
        r"^\s*(?:(?:noncomputable|private|protected|public)\s+)*"
        r"(?:theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque)\s+"
        r"([^\s({:\[]+)"
    )
    decl_lines: list[int] = []
    decl_names: list[str] = []
    for number, line in enumerate(lines, 1):
        match = decl_re.match(line)
        if match:
            decl_lines.append(number)
            decl_names.append(match.group(1))

    header = re.compile(
        r"^(.*\.lean):(\d+):(\d+): error(?:\(([^)]+)\))?:\s*(.*)$"
    )
    errors: list[dict[str, object]] = []
    for line in log_text.splitlines():
        match = header.match(line)
        if not match:
            continue
        source_line = int(match.group(2))
        index = bisect.bisect_right(decl_lines, source_line) - 1
        errors.append({
            "file": match.group(1),
            "line": source_line,
            "column": int(match.group(3)),
            "code": match.group(4),
            "message": match.group(5),
            "enclosing_declaration": decl_names[index] if index >= 0 else None,
        })
    return errors


def main() -> None:
    OUT.mkdir(parents=True, exist_ok=True)
    actual_base = sha256(QYM)
    if actual_base != BASE_SHA256:
        raise SystemExit(f"wrong canonical QYM two-error base bytes: {actual_base}")

    base_copy = OUT / "QYM.GB2.base.lean"
    candidate = OUT / "QYM.candidate.lean"
    shutil.copy2(QYM, base_copy)
    with (OUT / "patch.log").open("w") as handle:
        subprocess.run(
            [sys.executable, "-B", str(PATCH), str(base_copy), str(candidate)],
            check=True,
            stdout=handle,
            stderr=subprocess.STDOUT,
        )

    audit = audit_candidate(candidate)
    shutil.copy2(candidate, QYM)

    log = OUT / "full.log"
    start = time.time()
    with log.open("w") as handle:
        completed = subprocess.run(
            [
                "lake", "env", "lean",
                "-DmaxErrors=10000", "-DwarningAsError=false",
                "-o", str(OUT / "QYM.olean"),
                "-i", str(OUT / "QYM.ilean"),
                str(QYM),
            ],
            stdout=handle,
            stderr=subprocess.STDOUT,
            check=False,
        )
    elapsed = int(time.time() - start)

    log_text = log.read_text(errors="replace")
    errors = parse_errors(candidate, log_text)
    warnings = sum(
        bool(re.match(r"^.*\.lean:\d+:\d+: warning", line))
        for line in log_text.splitlines()
    )
    panic = sum(
        bool(re.search(r"internal error|uncaught exception|panic(!|:| )", line, re.I))
        for line in log_text.splitlines()
    )
    olean = (OUT / "QYM.olean").is_file() and (OUT / "QYM.olean").stat().st_size > 0
    ilean = (OUT / "QYM.ilean").is_file() and (OUT / "QYM.ilean").stat().st_size > 0
    codes = collections.Counter((error["code"] or "uncoded") for error in errors)
    declarations = collections.Counter(
        (error["enclosing_declaration"] or "<none>") for error in errors
    )

    result: dict[str, object] = {
        "schema": "qym-gb2-final-v1",
        "authority": "actual full-QYM direct Lean",
        "run_id": int(os.environ.get("GITHUB_RUN_ID", "0")),
        "trigger_sha": os.environ.get("GITHUB_SHA"),
        "base_source_sha256": BASE_SHA256,
        "base_error_headers": BASE_ERRORS,
        "exit": completed.returncode,
        "error_headers": len(errors),
        "warning_headers": warnings,
        "panic_lines": panic,
        "elapsed_seconds": elapsed,
        "first_error": errors[0] if errors else None,
        "source_sha256": sha256(candidate),
        "source_blob": git_blob(candidate),
        "source_lines": len(candidate.read_text().splitlines()),
        "source_bytes": candidate.stat().st_size,
        "log_sha256": sha256(log),
        "forbidden_zero": bool(audit["forbidden_zero"]),
        "olean_exists": olean,
        "ilean_exists": ilean,
        "error_codes": dict(codes),
        "error_declarations": dict(declarations),
        "errors": errors,
    }
    result["strict_improvement"] = (
        len(errors) < BASE_ERRORS
        and panic == 0
        and bool(audit["forbidden_zero"])
    )
    result["pass"] = (
        completed.returncode == 0
        and not errors
        and panic == 0
        and bool(audit["forbidden_zero"])
        and olean
        and ilean
    )

    (OUT / "FULL_RESULT.json").write_text(json.dumps(result, indent=2) + "\n")
    compact = {key: value for key, value in result.items() if key != "errors"}
    (OUT / "RESULT.json").write_text(json.dumps(compact, indent=2) + "\n")
    print(json.dumps(compact, indent=2))


if __name__ == "__main__":
    main()
