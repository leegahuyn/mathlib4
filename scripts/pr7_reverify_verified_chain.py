#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any

ERROR_RE = re.compile(r"\.lean:(\d+):(\d+):\s+(?:error(?:\([^)]*\))?:|error:)")


@dataclass
class Metric:
    stem: str
    run: int
    source_sha256: str
    line_count: int
    exit_code: int
    error_headers: int
    first_error_line: int
    first_error_col: int
    olean: bool
    ilean: bool
    log: str


def source_sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def strip_comments_and_strings(text: str) -> str:
    out: list[str] = []
    i = 0
    block = 0
    string = False
    while i < len(text):
        if block:
            if text.startswith("/-", i):
                block += 1; out.extend("  "); i += 2
            elif text.startswith("-/", i):
                block -= 1; out.extend("  "); i += 2
            else:
                out.append("\n" if text[i] == "\n" else " "); i += 1
        elif string:
            if text[i] == "\\" and i + 1 < len(text):
                out.extend("  "); i += 2
            elif text[i] == '"':
                string = False; out.append(" "); i += 1
            else:
                out.append("\n" if text[i] == "\n" else " "); i += 1
        elif text.startswith("--", i):
            while i < len(text) and text[i] != "\n":
                out.append(" "); i += 1
        elif text.startswith("/-", i):
            block = 1; out.extend("  "); i += 2
        elif text[i] == '"':
            string = True; out.append(" "); i += 1
        else:
            out.append(text[i]); i += 1
    return "".join(out)


def trust_audit(paths: list[Path]) -> dict[str, Any]:
    patterns = {
        "sorry": re.compile(r"\bsorry\b"),
        "admit": re.compile(r"\badmit\b"),
        "global_axiom": re.compile(r"(?m)^\s*axiom\s+"),
        "unsafe": re.compile(r"(?m)^\s*(?:private\s+|protected\s+)?unsafe\b"),
        "native_decide": re.compile(r"\bnative_decide\b"),
        "Lean.ofReduceBool": re.compile(r"\bLean\.ofReduceBool\b"),
    }
    per_file: dict[str, Any] = {}
    total = {key: 0 for key in patterns}
    for path in paths:
        cleaned = strip_comments_and_strings(path.read_text(encoding="utf-8", errors="replace"))
        counts = {key: len(list(pattern.finditer(cleaned))) for key, pattern in patterns.items()}
        per_file[str(path)] = counts
        for key, count in counts.items():
            total[key] += count
    return {"per_file": per_file, "total": total, "clean": all(value == 0 for value in total.values())}


def compile_one(worktree: Path, logs: Path, stem: str, run: int, max_errors: int = 2500) -> Metric:
    source = worktree / "PrimalitySheafVerification" / f"{stem}.lean"
    build = worktree / ".lake/build/lib/lean/PrimalitySheafVerification"
    build.mkdir(parents=True, exist_ok=True)
    olean = build / f"{stem}.olean"
    ilean = build / f"{stem}.ilean"
    olean.unlink(missing_ok=True)
    ilean.unlink(missing_ok=True)
    log = logs / f"{stem}-run{run}.log"
    command = [
        "lake", "env", "lean", f"-DmaxErrors={max_errors}", "-DwarningAsError=false",
        "-o", str(olean), "-i", str(ilean), str(source),
    ]
    with log.open("wb") as output:
        proc = subprocess.run(command, cwd=worktree, stdout=output, stderr=subprocess.STDOUT, check=False)
    text = log.read_text(encoding="utf-8", errors="replace")
    matches = list(ERROR_RE.finditer(text))
    return Metric(
        stem=stem,
        run=run,
        source_sha256=source_sha(source),
        line_count=len(source.read_text(encoding="utf-8", errors="replace").splitlines()),
        exit_code=proc.returncode,
        error_headers=len(matches),
        first_error_line=int(matches[0].group(1)) if matches else 0,
        first_error_col=int(matches[0].group(2)) if matches else 0,
        olean=olean.exists() and olean.stat().st_size > 0,
        ilean=ilean.exists() and ilean.stat().st_size > 0,
        log=str(log),
    )


def passed(metric: Metric) -> bool:
    return metric.exit_code == 0 and metric.error_headers == 0 and metric.olean and metric.ilean


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--worktree", required=True)
    parser.add_argument("--output", required=True)
    args = parser.parse_args()

    worktree = Path(args.worktree).resolve()
    output = Path(args.output).resolve()
    logs = output / "logs"
    logs.mkdir(parents=True, exist_ok=True)
    source_dir = worktree / "PrimalitySheafVerification"

    rows: list[Metric] = []
    blocked = ""

    for stem in ("Mock2", "Mock2_Advanced"):
        metric = compile_one(worktree, logs, stem, 1)
        rows.append(metric)
        if not passed(metric):
            blocked = f"{stem} prerequisite regression"
            break

    ordered: list[str] = []
    if not blocked:
        required = source_dir / "Mock2_FunctionalAnalysis_Integrated.lean"
        qym = source_dir / "QYM.lean"
        if not required.exists():
            blocked = "Mock2_FunctionalAnalysis_Integrated.lean missing"
        elif not qym.exists():
            blocked = "QYM.lean missing"
        else:
            ordered.append("Mock2_FunctionalAnalysis")
            ordered.append("Mock2_FunctionalAnalysis_Integrated")
            ordered.extend(sorted(path.stem for path in source_dir.glob("Mock3*.lean")))
            ordered.append("QYM")

    if not blocked:
        for stem in ordered:
            for run in (1, 2):
                metric = compile_one(worktree, logs, stem, run)
                rows.append(metric)
                if not passed(metric):
                    blocked = f"{stem} run {run} failed"
                    break
            if blocked:
                break

    target_paths = [source_dir / f"{stem}.lean" for stem in ordered if (source_dir / f"{stem}.lean").exists()]
    audit = trust_audit(target_paths)
    if not audit["clean"] and not blocked:
        blocked = "forbidden-token trust audit failed"

    complete = not blocked and all(passed(row) for row in rows) and bool(ordered)
    status = {
        "classification": "VERIFIED" if complete else "INFRA FAILURE",
        "authority": "fresh direct Lean CLI on the exact PR7 integration candidate source",
        "complete": complete,
        "blocked": blocked,
        "ordered_targets": ordered,
        "metrics": [asdict(row) for row in rows],
        "trust_audit": audit,
    }
    (output / "CURRENT.json").write_text(json.dumps(status, indent=2) + "\n", encoding="utf-8")
    (output / "CURRENT.txt").write_text(
        f"classification={status['classification']}\n"
        f"complete={str(complete).lower()}\n"
        f"blocked={blocked}\n" +
        "\n".join(
            f"{row.stem}-run{row.run}: exit={row.exit_code} errors={row.error_headers} first={row.first_error_line}:{row.first_error_col} sha={row.source_sha256}"
            for row in rows
        ) + "\n",
        encoding="utf-8",
    )
    print(json.dumps(status, indent=2))
    if not complete:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
