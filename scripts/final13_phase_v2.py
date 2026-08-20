#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import time
from pathlib import Path

ROOTS = [
    "PrimalitySheafVerification/Spt1.lean",
    "PrimalitySheafVerification/Spt2.lean",
    "PrimalitySheafVerification/Spt3.lean",
    "PrimalitySheafVerification/Spt4.lean",
    "PrimalitySheafVerification/Spt5.lean",
    "PrimalitySheafVerification/Spt6.lean",
    "PrimalitySheafVerification/Spt7.lean",
    "PrimalitySheafVerification/Mock1.lean",
    "PrimalitySheafVerification/Mock1_Advanced.lean",
    "PrimalitySheafVerification/Mock2.lean",
    "PrimalitySheafVerification/Mock2_Advanced.lean",
    "PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean",
    "PrimalitySheafVerification/QYM.lean",
]
BRIDGE = "PrimalitySheafVerification/Mock2_FunctionalAnalysis_Integrated.lean"
CORE = [
    "PrimalitySheafVerification/Mock2.lean",
    "PrimalitySheafVerification/Mock2_Advanced.lean",
    "PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean",
    BRIDGE,
    "PrimalitySheafVerification/QYM.lean",
]
TRUST = ("sorry", "admit", "axiom", "unsafe", "native_decide", "Lean.ofReduceBool")
DECL_RE = re.compile(
    r"(?m)^\s*(?:(?:protected|private|noncomputable|local|public)\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque)\s+"
    r"([^\s({:\[]+)"
)
ERROR_RE = re.compile(r"^.*\.lean:\d+:\d+: error(?:\(|:)")
WARNING_RE = re.compile(r"^.*\.lean:\d+:\d+: warning(?:\(|:)")
PANIC_RE = re.compile(r"internal error|uncaught exception|panic(!|:| )", re.I)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def strip_noncode(text: str) -> str:
    out = list(text)
    i = 0
    depth = 0
    in_string = False
    escaped = False
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
        if in_string:
            ch = out[i]
            if ch != "\n":
                out[i] = " "
            if escaped:
                escaped = False
            elif ch == "\\":
                escaped = True
            elif ch == '"':
                in_string = False
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
            in_string = True
        i += 1
    if depth != 0 or in_string:
        raise ValueError("unterminated comment or string")
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


def inventory(repo: Path, phase: str) -> dict[str, object]:
    rows: list[dict[str, object]] = []
    for relative in ROOTS:
        path = repo / relative
        if not path.is_file():
            rows.append({"file": relative, "exists": False})
            continue
        raw = path.read_bytes()
        text = raw.decode()
        declarations = DECL_RE.findall(text)
        trust = trust_counts(text)
        rows.append(
            {
                "file": relative,
                "exists": True,
                "sha256": hashlib.sha256(raw).hexdigest(),
                "git_blob": subprocess.check_output(
                    ["git", "hash-object", relative], cwd=repo, text=True
                ).strip(),
                "bytes": len(raw),
                "lines": len(text.splitlines()),
                "declaration_count": len(declarations),
                "declaration_sequence_sha256": hashlib.sha256(
                    "\n".join(declarations).encode()
                ).hexdigest(),
                "trust_counts": trust,
                "trust_six_zero": all(value == 0 for value in trust.values()),
            }
        )
    bridge_path = repo / BRIDGE
    bridge = {
        "file": BRIDGE,
        "exists": bridge_path.is_file(),
        "sha256": sha256(bridge_path) if bridge_path.is_file() else None,
        "git_blob": subprocess.check_output(
            ["git", "hash-object", BRIDGE], cwd=repo, text=True
        ).strip() if bridge_path.is_file() else None,
    }
    return {
        "schema": "final13-source-inventory-v2",
        "phase": phase,
        "expected_roots": ROOTS,
        "expected_root_count": 13,
        "existing_root_count": sum(row.get("exists") is True for row in rows),
        "all_present": all(row.get("exists") is True for row in rows),
        "all_nonempty": all(
            row.get("exists") is True
            and int(row.get("bytes", 0)) > 0
            and int(row.get("lines", 0)) > 0
            and int(row.get("declaration_count", 0)) > 0
            for row in rows
        ),
        "all_trust_six_zero": all(row.get("trust_six_zero") is True for row in rows),
        "bridge": bridge,
        "files": rows,
    }


def inventories_identical(before: dict[str, object], after: dict[str, object]) -> bool:
    before_rows = {row["file"]: row for row in before.get("files", []) if row.get("exists")}
    after_rows = {row["file"]: row for row in after.get("files", []) if row.get("exists")}
    keys = (
        "sha256",
        "git_blob",
        "bytes",
        "lines",
        "declaration_count",
        "declaration_sequence_sha256",
        "trust_counts",
    )
    return (
        set(before_rows) == set(after_rows)
        and all(
            all(before_rows[name].get(key) == after_rows[name].get(key) for key in keys)
            for name in before_rows
        )
        and before.get("bridge") == after.get("bridge")
    )


def run_command(command: list[str], log: Path, cwd: Path) -> dict[str, object]:
    log.parent.mkdir(parents=True, exist_ok=True)
    start = time.time()
    with log.open("w") as handle:
        completed = subprocess.run(
            command,
            cwd=cwd,
            stdout=handle,
            stderr=subprocess.STDOUT,
            check=False,
        )
    return {
        "command": command,
        "exit": completed.returncode,
        "elapsed_seconds": int(time.time() - start),
        "log": str(log),
    }


def module_output(repo: Path, source: str) -> tuple[Path, Path]:
    relative = Path(source).with_suffix("")
    base = repo / ".lake/build/lib/lean" / relative
    base.parent.mkdir(parents=True, exist_ok=True)
    return base.with_suffix(".olean"), base.with_suffix(".ilean")


def compile_source(repo: Path, source: str, log: Path) -> dict[str, object]:
    olean, ilean = module_output(repo, source)
    olean.unlink(missing_ok=True)
    ilean.unlink(missing_ok=True)
    result = run_command(
        [
            "lake",
            "env",
            "lean",
            "-DmaxErrors=10000",
            "-DwarningAsError=false",
            "-o",
            str(olean),
            "-i",
            str(ilean),
            source,
        ],
        log,
        repo,
    )
    result.update(
        {
            "source": source,
            "olean": str(olean),
            "ilean": str(ilean),
            "olean_exists": olean.is_file() and olean.stat().st_size > 0,
            "ilean_exists": ilean.is_file() and ilean.stat().st_size > 0,
        }
    )
    return result


def compile_roots(repo: Path, out: Path) -> tuple[list[dict[str, object]], dict[str, object]]:
    rows: list[dict[str, object]] = []
    bridge_result: dict[str, object] | None = None
    for source in ROOTS:
        if source.endswith("/QYM.lean"):
            bridge_result = compile_source(repo, BRIDGE, out / "logs/bridge.log")
        key = Path(source).stem
        rows.append(compile_source(repo, source, out / f"logs/roots/{key}.log"))
    if bridge_result is None:
        raise RuntimeError("bridge was not compiled before QYM")
    return rows, bridge_result


def compile_core(repo: Path, out: Path) -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    for source in CORE:
        key = Path(source).stem
        rows.append(compile_source(repo, source, out / f"logs/core/{key}.log"))
    return rows


def compile_build_all(repo: Path, out: Path) -> dict[str, object]:
    generated = out / "generated/BuildAll.lean"
    generated.parent.mkdir(parents=True, exist_ok=True)
    modules = [Path(path).with_suffix("").as_posix().replace("/", ".") for path in ROOTS]
    bridge_module = Path(BRIDGE).with_suffix("").as_posix().replace("/", ".")
    imports = [f"import {module}" for module in modules]
    if f"import {bridge_module}" not in imports:
        imports.insert(-1, f"import {bridge_module}")
    generated.write_text("\n".join(imports) + "\n")
    olean = out / "generated/BuildAll.olean"
    ilean = out / "generated/BuildAll.ilean"
    result = run_command(
        [
            "lake",
            "env",
            "lean",
            "-DmaxErrors=10000",
            "-DwarningAsError=false",
            "-o",
            str(olean),
            "-i",
            str(ilean),
            str(generated),
        ],
        out / "logs/BuildAll.log",
        repo,
    )
    result.update(
        {
            "source": str(generated),
            "source_sha256": sha256(generated),
            "olean_exists": olean.is_file() and olean.stat().st_size > 0,
            "ilean_exists": ilean.is_file() and ilean.stat().st_size > 0,
            "imports": imports,
        }
    )
    return result


def audit_logs(out: Path) -> dict[str, object]:
    error_headers: list[dict[str, str]] = []
    warning_headers: list[dict[str, str]] = []
    panic_lines: list[dict[str, str]] = []
    sorry_warnings: list[dict[str, str]] = []
    cap_sentinels: list[dict[str, str]] = []
    logs = sorted(out.glob("logs/**/*.log"))
    for path in logs:
        text = path.read_text(errors="replace")
        for line in text.splitlines():
            row = {"log": str(path.relative_to(out)), "line": line[:1000]}
            if ERROR_RE.match(line):
                error_headers.append(row)
            if WARNING_RE.match(line):
                warning_headers.append(row)
            if PANIC_RE.search(line):
                panic_lines.append(row)
            if "declaration uses 'sorry'" in line or "declaration uses ‘sorry’" in line:
                sorry_warnings.append(row)
            if "maximum number of errors" in line.lower():
                cap_sentinels.append(row)
    return {
        "schema": "final13-compiler-log-audit-v2",
        "logs_examined": len(logs),
        "error_header_count": len(error_headers),
        "warning_header_count": len(warning_headers),
        "panic_line_count": len(panic_lines),
        "synthetic_sorry_warning_count": len(sorry_warnings),
        "max_error_cap_sentinel_count": len(cap_sentinels),
        "error_headers": error_headers,
        "panic_lines": panic_lines,
        "synthetic_sorry_warnings": sorry_warnings,
        "max_error_cap_sentinels": cap_sentinels,
    }


def all_compiles_pass(rows: list[dict[str, object]]) -> bool:
    return all(
        row.get("exit") == 0
        and row.get("olean_exists") is True
        and row.get("ilean_exists") is True
        for row in rows
    )


def clean_project_outputs(repo: Path) -> None:
    shutil.rmtree(repo / ".lake/build/lib/lean/PrimalitySheafVerification", ignore_errors=True)
    source_root = repo / "PrimalitySheafVerification"
    for pattern in ("*.olean", "*.ilean", "*.c"):
        for path in source_root.rglob(pattern):
            path.unlink(missing_ok=True)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", default=".")
    parser.add_argument("--out", required=True)
    parser.add_argument("--mode", choices=("baseline", "clean1", "clean2"), required=True)
    args = parser.parse_args()

    repo = Path(args.repo).resolve()
    out = Path(args.out).resolve()
    shutil.rmtree(out, ignore_errors=True)
    out.mkdir(parents=True, exist_ok=True)

    before = inventory(repo, f"{args.mode}-before")
    (out / "SOURCE_MANIFEST.before.json").write_text(
        json.dumps(before, indent=2, sort_keys=True) + "\n"
    )

    environment: dict[str, object] = {}
    if args.mode.startswith("clean"):
        clean_project_outputs(repo)
        environment["lake_clean"] = run_command(
            ["lake", "clean"], out / "logs/environment/lake-clean.log", repo
        )
        environment["cache_restore"] = run_command(
            ["lake", "exe", "cache", "get"],
            out / "logs/environment/cache-restore.log",
            repo,
        )
        environment["lake_build"] = run_command(
            ["lake", "build"], out / "logs/environment/lake-build.log", repo
        )

    roots, bridge = compile_roots(repo, out)
    core = compile_core(repo, out) if args.mode == "baseline" else []
    build_all = compile_build_all(repo, out)

    after = inventory(repo, f"{args.mode}-after")
    (out / "SOURCE_MANIFEST.after.json").write_text(
        json.dumps(after, indent=2, sort_keys=True) + "\n"
    )
    audit = audit_logs(out)
    (out / "COMPILER_LOG_AUDIT.json").write_text(
        json.dumps(audit, indent=2, sort_keys=True) + "\n"
    )

    environment_pass = True
    if args.mode.startswith("clean"):
        environment_pass = all(
            row.get("exit") == 0 for row in environment.values()
        )
    source_identical = inventories_identical(before, after)
    logs_clean = (
        audit["error_header_count"] == 0
        and audit["panic_line_count"] == 0
        and audit["synthetic_sorry_warning_count"] == 0
        and audit["max_error_cap_sentinel_count"] == 0
    )
    result = {
        "schema": "final13-phase-result-v2",
        "mode": args.mode,
        "github_sha": os.environ.get("GITHUB_SHA"),
        "run_id": int(os.environ.get("GITHUB_RUN_ID", "0")),
        "root_count": len(roots),
        "roots": roots,
        "bridge": bridge,
        "core": core,
        "build_all": build_all,
        "environment": environment,
        "inventory_before": {
            "all_present": before["all_present"],
            "all_nonempty": before["all_nonempty"],
            "all_trust_six_zero": before["all_trust_six_zero"],
        },
        "source_identical": source_identical,
        "compiler_log_audit": audit,
        "root_pass": len(roots) == 13 and all_compiles_pass(roots),
        "bridge_pass": all_compiles_pass([bridge]),
        "core_pass": args.mode != "baseline" or (len(core) == 5 and all_compiles_pass(core)),
        "build_all_pass": all_compiles_pass([build_all]),
        "environment_pass": environment_pass,
        "logs_clean": logs_clean,
    }
    result["pass"] = (
        before["all_present"] is True
        and before["all_nonempty"] is True
        and before["all_trust_six_zero"] is True
        and source_identical
        and result["root_pass"]
        and result["bridge_pass"]
        and result["core_pass"]
        and result["build_all_pass"]
        and environment_pass
        and logs_clean
    )
    (out / "PHASE_RESULT.json").write_text(
        json.dumps(result, indent=2, sort_keys=True) + "\n"
    )
    print(json.dumps({k: v for k, v in result.items() if k not in {"roots", "core"}}, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
