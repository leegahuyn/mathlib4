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

EXPECTED = {
    "direct-manual": "b26bc262dd0f47271ee54e5ad95335737a6b8e98bcbfab5d40f30147d71bef9c",
    "direct-cast": "8b5be34ba3e8ca4e3545c7d70bc04cdf93ca3258a414b2776e33b29f661a6819",
    "simpa-manual": "873aa704d23a69acf2208fa70bd597867683e0485a4e42f1410e287deb1ce19a",
    "simpa-simp": "8e0779d0cb38a2781fcd081f7b3d70421ad5bbbba3bcf9ced84f48318b47a183",
    "tolp-manual": "af4944cfc629cc407f05e0b3ee03106103d1fd0f35ec514d3f09888638206068",
    "tolp-cast": "28431dba8d755ff394869e00fb5d800fa98220db2dae787e39bba4a9c529e7d4",
    "convert-manual": "c4594c838d9b123d921149e246c7ec29c9ba2e7eeb850f9e09bd7df66cb78db2",
    "convert-change": "c798cc256e41e19073cc57aef0723e213ef234e353dde65daf47790a91efcd7f",
}
BASE_SHA256 = "231efe9a0b8f9d05aae5e65ff3904b3636182ef6f1c93c11eac0c05313730998"
BASE_ERRORS = 5


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def code_only(text: str) -> tuple[str, int]:
    out: list[str] = []
    i = 0
    depth = 0
    in_string = False
    in_line = False
    while i < len(text):
        if in_line:
            if text[i] == "\n":
                in_line = False
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
            in_line = True
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


def audit(candidate: pathlib.Path, out: pathlib.Path) -> dict[str, object]:
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
    counts = {name: len(re.findall(pattern, code)) for name, pattern in patterns.items()}
    result = {
        "forbidden_zero": depth == 0 and all(value == 0 for value in counts.values()),
        "counts": counts,
        "comment_depth": depth,
    }
    (out / "FORBIDDEN_AUDIT.json").write_text(json.dumps(result, indent=2) + "\n")
    return result


def parse_errors(candidate: pathlib.Path, text: str) -> list[dict[str, object]]:
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
    header = re.compile(r"^(.*\.lean):(\d+):(\d+): error(?:\(([^)]+)\))?:\s*(.*)$")
    errors: list[dict[str, object]] = []
    for line in text.splitlines():
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
    if len(sys.argv) != 7:
        raise SystemExit("usage: runner.py VARIANT GENERATOR BASE CANONICAL_QYM OUT OLEAN_DIR")
    variant = sys.argv[1]
    generator = pathlib.Path(sys.argv[2])
    base = pathlib.Path(sys.argv[3])
    qym = pathlib.Path(sys.argv[4])
    out = pathlib.Path(sys.argv[5])
    _olean_dir = pathlib.Path(sys.argv[6])
    if variant not in EXPECTED:
        raise SystemExit(f"unknown variant: {variant}")
    out.mkdir(parents=True, exist_ok=True)
    if sha256(base) != BASE_SHA256:
        raise SystemExit(f"wrong 5-error authority bytes: {sha256(base)}")

    candidate = out / "QYM.candidate.lean"
    with (out / "generator.log").open("w") as handle:
        subprocess.run(
            [sys.executable, "-B", str(generator), variant, str(base), str(candidate)],
            check=True,
            stdout=handle,
            stderr=subprocess.STDOUT,
        )
    actual_sha = sha256(candidate)
    if actual_sha != EXPECTED[variant]:
        raise SystemExit(f"candidate hash drift for {variant}: expected {EXPECTED[variant]}, got {actual_sha}")
    forbidden = audit(candidate, out)
    shutil.copy2(candidate, qym)

    log = out / "full.log"
    olean = out / "QYM.olean"
    ilean = out / "QYM.ilean"
    start = time.time()
    with log.open("w") as handle:
        completed = subprocess.run(
            ["lake", "env", "lean", "-DmaxErrors=10000", "-DwarningAsError=false",
             "-o", str(olean), "-i", str(ilean), str(qym)],
            stdout=handle,
            stderr=subprocess.STDOUT,
            check=False,
        )
    elapsed = int(time.time() - start)
    log_text = log.read_text(errors="replace")
    errors = parse_errors(candidate, log_text)
    warnings = sum(bool(re.match(r"^.*\.lean:\d+:\d+: warning", line)) for line in log_text.splitlines())
    panics = sum(bool(re.search(r"internal error|uncaught exception|panic(!|:| )", line, re.I)) for line in log_text.splitlines())
    codes = collections.Counter((row["code"] or "uncoded") for row in errors)
    declarations = collections.Counter((row["enclosing_declaration"] or "<none>") for row in errors)
    has_olean = olean.is_file() and olean.stat().st_size > 0
    has_ilean = ilean.is_file() and ilean.stat().st_size > 0
    result: dict[str, object] = {
        "schema": "qym-r4-targeted-matrix-candidate-v1",
        "authority": "actual full-QYM direct Lean",
        "variant": variant,
        "run_id": int(os.environ.get("GITHUB_RUN_ID", "0")),
        "trigger_sha": os.environ.get("GITHUB_SHA"),
        "base_sha256": BASE_SHA256,
        "base_error_headers": BASE_ERRORS,
        "source_sha256": actual_sha,
        "source_blob": subprocess.check_output(["git", "hash-object", str(candidate)], text=True).strip(),
        "exit": completed.returncode,
        "error_headers": len(errors),
        "warning_headers": warnings,
        "panic_lines": panics,
        "elapsed_seconds": elapsed,
        "first_error": errors[0] if errors else None,
        "forbidden_zero": bool(forbidden["forbidden_zero"]),
        "olean_exists": has_olean,
        "ilean_exists": has_ilean,
        "error_codes": dict(codes),
        "error_declarations": dict(declarations),
        "errors": errors,
    }
    result["pass"] = (
        completed.returncode == 0 and not errors and panics == 0
        and bool(forbidden["forbidden_zero"]) and has_olean and has_ilean
    )
    result["strict_improvement"] = (
        len(errors) < BASE_ERRORS and panics == 0 and bool(forbidden["forbidden_zero"])
    )
    (out / "RESULT.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({key: value for key, value in result.items() if key != "errors"}, indent=2))


if __name__ == "__main__":
    main()
