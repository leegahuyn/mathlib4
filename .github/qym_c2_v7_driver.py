#!/usr/bin/env python3
from __future__ import annotations

import argparse
import collections
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time
from typing import Any

ERROR_RE = re.compile(
    r"^(?P<file>.*?\.lean):(?P<line>\d+):(?P<column>\d+): "
    r"(?P<severity>error|warning)(?:\((?P<code>[^)]*)\))?:\s*"
    r"(?P<message>.*)$",
    re.M,
)
FIRST_ERROR_RE = re.compile(
    r"^.*?\.lean:(\d+):(\d+): error(?:\([^)]*\))?:\s*(.*)$",
    re.M,
)
PANIC_RE = re.compile(
    r"(?im)^.*(?:internal error|uncaught exception|panic(?:!|:|\s)).*$"
)
VARIANTS = (
    "ofreal_apply_mulinv_simpa",
    "ofreal_apply_mulinv_rw",
    "ofreal_apply_mulinv_change",
)


def git_blob(raw: bytes) -> str:
    return hashlib.sha1(
        b"blob " + str(len(raw)).encode() + b"\0" + raw
    ).hexdigest()


def sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_json(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise RuntimeError(f"{path} is not a JSON object")
    return value


def write_json(path: Path, value: Any) -> None:
    path.write_text(
        json.dumps(value, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )


def parse_diagnostics(text: str) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for match in ERROR_RE.finditer(text):
        row: dict[str, Any] = match.groupdict()
        row["line"] = int(row["line"])
        row["column"] = int(row["column"])
        rows.append(row)
    return rows


def first_error(text: str) -> dict[str, Any] | None:
    match = FIRST_ERROR_RE.search(text)
    if match is None:
        return None
    return {
        "line": int(match.group(1)),
        "column": int(match.group(2)),
        "message": match.group(3),
    }


def run_logged(
    command: list[str],
    log_path: Path,
    exit_path: Path,
    timing_path: Path,
) -> int:
    started = time.monotonic()
    with log_path.open("wb") as stream:
        process = subprocess.run(
            command,
            stdout=stream,
            stderr=subprocess.STDOUT,
            check=False,
        )
    elapsed = time.monotonic() - started
    exit_path.write_text(f"{process.returncode}\n", encoding="utf-8")
    write_json(
        timing_path,
        {
            "command": command,
            "elapsed_seconds": elapsed,
            "exit": process.returncode,
        },
    )
    return process.returncode


def recover(args: argparse.Namespace) -> None:
    root = Path(args.artifact_dir)
    output = Path(args.output)
    expected_sha = args.sha256
    expected_blob = args.blob
    expected_errors = int(args.errors)

    sources: list[Path] = []
    for path in root.rglob("*.lean"):
        raw = path.read_bytes()
        if (
            hashlib.sha256(raw).hexdigest() == expected_sha
            and git_blob(raw) == expected_blob
        ):
            sources.append(path)
    if len(sources) != 1:
        raise SystemExit(f"exact GB85 source count={len(sources)}")

    results: list[tuple[Path, dict[str, Any]]] = []
    for path in root.rglob("RESULT.json"):
        try:
            value = read_json(path)
        except Exception:
            continue
        if (
            value.get("candidate_qym_sha256") == expected_sha
            and value.get("candidate_qym_blob") == expected_blob
            and int(value.get("error_headers", -1)) == expected_errors
            and int(value.get("panic_lines", -1)) == 0
            and value.get("full_compile_executed", True)
        ):
            results.append((path, value))
    if len(results) != 1:
        raise SystemExit(f"verified GB85 RESULT count={len(results)}")

    output.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(sources[0], output)
    write_json(output.parent / "GB85_RESULT.json", results[0][1])
    summary = {
        "source": str(sources[0]),
        "sha256": expected_sha,
        "blob": expected_blob,
        "errors": expected_errors,
        "result": str(results[0][0]),
    }
    write_json(output.parent / "GB85_RECOVERY.json", summary)
    print(json.dumps(summary, indent=2, sort_keys=True))


def full_result(
    *,
    directory: Path,
    patch: dict[str, Any],
    baseline_errors: int,
    full_executed: bool,
    full_rc: int | None,
) -> dict[str, Any]:
    raw = (directory / "full.log").read_bytes() if full_executed else b""
    text = raw.decode(errors="replace")
    rows = parse_diagnostics(text)
    errors = [row for row in rows if row["severity"] == "error"]
    warnings = [row for row in rows if row["severity"] == "warning"]
    panics = PANIC_RE.findall(text)
    semantic_pass = (
        full_executed
        and full_rc == 0
        and not errors
        and not panics
    )
    strict = (
        full_executed
        and (
            semantic_pass
            or (not panics and len(errors) < baseline_errors)
        )
    )
    result = {
        "schema": "qym-gb85-c2-mulinv-v7-result",
        "run_id": int(os.environ["GITHUB_RUN_ID"]),
        "trigger_sha": os.environ["GITHUB_SHA"],
        "variant": patch["variant"],
        "baseline_qym_sha256": os.environ["BASE_SHA256"],
        "baseline_qym_blob": os.environ["BASE_BLOB"],
        "baseline_error_headers": baseline_errors,
        "candidate_qym_sha256": patch["candidate_sha256"],
        "candidate_qym_blob": patch["candidate_blob"],
        "forbidden": patch["forbidden"],
        "full_compile_executed": full_executed,
        "exit": full_rc,
        "error_headers": len(errors) if full_executed else None,
        "warning_headers": len(warnings) if full_executed else None,
        "panic_lines": len(panics) if full_executed else None,
        "first_error": errors[0] if errors else None,
        "last_error": errors[-1] if errors else None,
        "error_codes": (
            dict(
                sorted(
                    collections.Counter(
                        row["code"] or "uncoded" for row in errors
                    ).items()
                )
            )
            if full_executed
            else {}
        ),
        "log_sha256": hashlib.sha256(raw).hexdigest()
        if full_executed
        else None,
        "semantic_pass": semantic_pass,
        "strict_improvement": strict,
        "qym_olean_sha256": (
            sha256_file(directory / "QYM.olean")
            if semantic_pass and (directory / "QYM.olean").is_file()
            else None
        ),
        "qym_ilean_sha256": (
            sha256_file(directory / "QYM.ilean")
            if semantic_pass and (directory / "QYM.ilean").is_file()
            else None
        ),
    }
    write_json(directory / "RESULT.json", result)
    (directory / "diagnostics.jsonl").write_text(
        "".join(json.dumps(row, sort_keys=True) + "\n" for row in rows),
        encoding="utf-8",
    )
    (directory / "error-headers.txt").write_text(
        "".join(
            f"{row['file']}:{row['line']}:{row['column']}: error"
            f"{('(' + row['code'] + ')') if row['code'] else ''}: "
            f"{row['message']}\n"
            for row in errors
        ),
        encoding="utf-8",
    )
    print(json.dumps(result, indent=2, sort_keys=True))
    return result


def rank(row: dict[str, Any]) -> tuple[Any, ...]:
    first = row.get("first_error") or {}
    return (
        0 if row.get("semantic_pass") else 1,
        int(
            row.get("error_headers")
            if row.get("error_headers") is not None
            else 10**9
        ),
        int(
            row.get("panic_lines")
            if row.get("panic_lines") is not None
            else 10**9
        ),
        -int(first.get("line") or 0),
        row.get("variant") or "",
    )


def tournament(args: argparse.Namespace) -> None:
    qym = Path(args.qym)
    baseline = Path(args.baseline)
    patcher = Path(args.patcher)
    out = Path(args.out)
    runner_temp = Path(args.runner_temp)
    baseline_errors = int(args.errors)
    python = sys.executable

    out.mkdir(parents=True, exist_ok=True)
    runner_temp.mkdir(parents=True, exist_ok=True)
    checked_in = out / "QYM.checked-in.lean"
    shutil.copy2(qym, checked_in)

    rows: list[dict[str, Any]] = []
    try:
        for variant in VARIANTS:
            directory = out / variant
            directory.mkdir(parents=True, exist_ok=True)
            shutil.copy2(baseline, qym)

            patch_process = subprocess.run(
                [python, "-B", str(patcher), variant, str(qym)],
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                check=False,
            )
            (directory / "PATCH_RESULT.json").write_text(
                patch_process.stdout, encoding="utf-8"
            )
            (directory / "patch.stderr").write_text(
                patch_process.stderr, encoding="utf-8"
            )
            (directory / "patch.exit").write_text(
                f"{patch_process.returncode}\n", encoding="utf-8"
            )
            if patch_process.returncode != 0:
                write_json(
                    directory / "INFRA_FAILURE.json",
                    {
                        "stage": "patch",
                        "variant": variant,
                        "exit": patch_process.returncode,
                        "stderr": patch_process.stderr,
                    },
                )
                continue

            patch = read_json(directory / "PATCH_RESULT.json")
            if patch.get("input_sha256") != os.environ["BASE_SHA256"]:
                raise RuntimeError(f"{variant}: input SHA256 mismatch")
            if patch.get("input_blob") != os.environ["BASE_BLOB"]:
                raise RuntimeError(f"{variant}: input Git blob mismatch")
            forbidden = patch.get("forbidden") or {}
            if sum(int(value) for value in forbidden.values()) != 0:
                raise RuntimeError(f"{variant}: forbidden-token audit failed")
            shutil.copy2(qym, directory / "QYM.candidate.lean")

            local_olean = runner_temp / f"{variant}.local.olean"
            local_ilean = runner_temp / f"{variant}.local.ilean"
            local_rc = run_logged(
                [
                    "lake",
                    "env",
                    "lean",
                    "-DmaxErrors=1",
                    "-DwarningAsError=false",
                    "-o",
                    str(local_olean),
                    "-i",
                    str(local_ilean),
                    str(qym),
                ],
                directory / "local.log",
                directory / "local.exit",
                directory / "local.timing.json",
            )
            local_text = (directory / "local.log").read_text(errors="replace")
            local_first = first_error(local_text)
            local_panics = PANIC_RE.findall(local_text)
            gate = int(patch["gate_line"])
            c2_fixed = not local_panics and (
                local_first is None or int(local_first["line"]) >= gate
            )
            local_result = {
                "variant": variant,
                "exit": local_rc,
                "gate_line": gate,
                "first_error": local_first,
                "panic_lines": len(local_panics),
                "c2_fixed": c2_fixed,
            }
            write_json(directory / "LOCAL_RESULT.json", local_result)
            print(json.dumps(local_result, indent=2, sort_keys=True))

            full_executed = False
            full_rc: int | None = None
            if c2_fixed:
                full_olean = runner_temp / f"{variant}.QYM.olean"
                full_ilean = runner_temp / f"{variant}.QYM.ilean"
                full_rc = run_logged(
                    [
                        "lake",
                        "env",
                        "lean",
                        "-DmaxErrors=10000",
                        "-DwarningAsError=false",
                        "-o",
                        str(full_olean),
                        "-i",
                        str(full_ilean),
                        str(qym),
                    ],
                    directory / "full.log",
                    directory / "full.exit",
                    directory / "full.timing.json",
                )
                full_executed = True
                if full_rc == 0:
                    if not full_olean.is_file() or not full_ilean.is_file():
                        raise RuntimeError(
                            f"{variant}: Lean exit 0 without QYM objects"
                        )
                    shutil.copy2(full_olean, directory / "QYM.olean")
                    shutil.copy2(full_ilean, directory / "QYM.ilean")

            result = full_result(
                directory=directory,
                patch=patch,
                baseline_errors=baseline_errors,
                full_executed=full_executed,
                full_rc=full_rc,
            )
            result["local"] = local_result
            result["source"] = str(directory / "QYM.candidate.lean")
            rows.append(result)
    finally:
        shutil.copy2(checked_in, qym)

    rows.sort(key=rank)
    valid = [row for row in rows if row.get("strict_improvement")]
    best = valid[0] if valid else None
    selection = {
        "schema": "qym-gb85-c2-mulinv-v7-selection",
        "baseline_error_headers": baseline_errors,
        "best": best,
        "all": rows,
        "promoted": best is not None,
    }
    write_json(out / "SELECTION.json", selection)
    print(json.dumps(selection, indent=2, sort_keys=True))

    if best is None:
        raise SystemExit("no corrected C2 candidate strictly improved GB85")

    source = Path(best["source"])
    shutil.copy2(source, out / "QYM.C2.V7.BEST.lean")
    if best.get("semantic_pass"):
        shutil.copy2(source.parent / "QYM.olean", out / "QYM.olean")
        shutil.copy2(source.parent / "QYM.ilean", out / "QYM.ilean")
    write_json(out / "C2_V7_RESULT.json", best)


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers(dest="command", required=True)

    recover_parser = subparsers.add_parser("recover")
    recover_parser.add_argument("artifact_dir")
    recover_parser.add_argument("output")
    recover_parser.add_argument("sha256")
    recover_parser.add_argument("blob")
    recover_parser.add_argument("errors", type=int)
    recover_parser.set_defaults(func=recover)

    tournament_parser = subparsers.add_parser("tournament")
    tournament_parser.add_argument("qym")
    tournament_parser.add_argument("baseline")
    tournament_parser.add_argument("patcher")
    tournament_parser.add_argument("out")
    tournament_parser.add_argument("errors", type=int)
    tournament_parser.add_argument("runner_temp")
    tournament_parser.set_defaults(func=tournament)
    return parser


def main() -> None:
    parser = build_parser()
    args = parser.parse_args()
    args.func(args)


if __name__ == "__main__":
    main()
