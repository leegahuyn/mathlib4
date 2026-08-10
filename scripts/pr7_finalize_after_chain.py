#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import re
import shutil
import subprocess
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any

ERROR_RE = re.compile(r"\.lean:(\d+):(\d+):\s+(?:error(?:\([^)]*\))?:|error:)")
DECL_RE = re.compile(r"^(?:(?:protected|noncomputable)\s+)*(?:theorem|lemma)\s+([^\s(:]+)")
NAMESPACE_RE = re.compile(r"^namespace\s+([^\s]+)")
END_RE = re.compile(r"^end(?:\s+([^\s]+))?\s*$")


@dataclass
class Metric:
    phase: str
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


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def strip_comments_and_strings(text: str) -> str:
    out: list[str] = []
    i = 0
    block = 0
    string = False
    while i < len(text):
        if block:
            if text.startswith("/-", i): block += 1; out.extend("  "); i += 2
            elif text.startswith("-/", i): block -= 1; out.extend("  "); i += 2
            else: out.append("\n" if text[i] == "\n" else " "); i += 1
        elif string:
            if text[i] == "\\" and i + 1 < len(text): out.extend("  "); i += 2
            elif text[i] == '"': string = False; out.append(" "); i += 1
            else: out.append("\n" if text[i] == "\n" else " "); i += 1
        elif text.startswith("--", i):
            while i < len(text) and text[i] != "\n": out.append(" "); i += 1
        elif text.startswith("/-", i): block = 1; out.extend("  "); i += 2
        elif text[i] == '"': string = True; out.append(" "); i += 1
        else: out.append(text[i]); i += 1
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
    total = {key: 0 for key in patterns}
    per_file: dict[str, dict[str, int]] = {}
    for path in paths:
        cleaned = strip_comments_and_strings(path.read_text(encoding="utf-8", errors="replace"))
        counts = {key: len(list(pattern.finditer(cleaned))) for key, pattern in patterns.items()}
        per_file[str(path)] = counts
        for key, value in counts.items(): total[key] += value
    return {"total": total, "per_file": per_file, "clean": all(value == 0 for value in total.values())}


def compile_one(worktree: Path, logs: Path, phase: str, stem: str, run: int, max_errors: int = 3000) -> Metric:
    source = worktree / "PrimalitySheafVerification" / f"{stem}.lean"
    build = worktree / ".lake/build/lib/lean/PrimalitySheafVerification"
    build.mkdir(parents=True, exist_ok=True)
    olean = build / f"{stem}.olean"
    ilean = build / f"{stem}.ilean"
    olean.unlink(missing_ok=True); ilean.unlink(missing_ok=True)
    phase_dir = logs / phase
    phase_dir.mkdir(parents=True, exist_ok=True)
    log = phase_dir / f"{stem}-run{run}.log"
    command = [
        "lake", "env", "lean", f"-DmaxErrors={max_errors}", "-DwarningAsError=false",
        "-o", str(olean), "-i", str(ilean), str(source),
    ]
    with log.open("wb") as output:
        proc = subprocess.run(command, cwd=worktree, stdout=output, stderr=subprocess.STDOUT, check=False)
    text = log.read_text(encoding="utf-8", errors="replace")
    matches = list(ERROR_RE.finditer(text))
    return Metric(
        phase=phase, stem=stem, run=run,
        source_sha256=sha(source),
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


def module_order(source_dir: Path) -> list[str]:
    order = [f"Spt{i}" for i in range(1, 8)]
    order += ["Mock1", "Mock1_Advanced", "Mock2", "Mock2_Advanced", "Mock2_FunctionalAnalysis"]
    if (source_dir / "Mock2_FunctionalAnalysis_Integrated.lean").exists():
        order.append("Mock2_FunctionalAnalysis_Integrated")
    order.extend(sorted(path.stem for path in source_dir.glob("Mock3*.lean")))
    if (source_dir / "QYM.lean").exists(): order.append("QYM")
    if (source_dir / "BuildAll.lean").exists(): order.append("BuildAll")
    return [stem for stem in order if (source_dir / f"{stem}.lean").exists()]


def spt5_declarations(path: Path) -> list[str]:
    namespaces: list[str] = []
    names: list[str] = []
    in_block = 0
    for raw in path.read_text(encoding="utf-8", errors="replace").splitlines():
        stripped = raw.strip()
        if in_block:
            in_block += stripped.count("/-") - stripped.count("-/")
            continue
        if stripped.startswith(("/-", "/--", "/-!")):
            in_block += stripped.count("/-") - stripped.count("-/")
            if in_block < 0: in_block = 0
            continue
        if not raw or raw[0].isspace() or stripped.startswith("--"):
            continue
        namespace = NAMESPACE_RE.match(stripped)
        if namespace:
            namespaces.append(namespace.group(1)); continue
        end = END_RE.match(stripped)
        if end:
            if namespaces: namespaces.pop()
            continue
        if stripped.startswith("private "):
            continue
        declaration = DECL_RE.match(stripped)
        if declaration:
            local_name = declaration.group(1)
            names.append(".".join(namespaces + [local_name]) if namespaces else local_name)
    return names


def spt5_axiom_audit(worktree: Path, output: Path) -> dict[str, Any]:
    source = worktree / "PrimalitySheafVerification/Spt5.lean"
    declarations = spt5_declarations(source)
    audit_file = worktree / "PrimalitySheafVerification/Spt5WholeFileAxiomAudit.lean"
    lines = ["import PrimalitySheafVerification.Spt5\n"]
    lines += [f"#print axioms {name}\n" for name in declarations]
    audit_file.write_text("".join(lines), encoding="utf-8")
    log = output / "Spt5WholeFileAxiomAudit.log"
    with log.open("wb") as handle:
        proc = subprocess.run(
            ["lake", "env", "lean", "-DwarningAsError=false", str(audit_file)],
            cwd=worktree, stdout=handle, stderr=subprocess.STDOUT, check=False,
        )
    text = log.read_text(encoding="utf-8", errors="replace")
    audit_file.unlink(missing_ok=True)
    return {
        "declaration_count": len(declarations),
        "exit_code": proc.returncode,
        "sorryAx_occurrences": text.count("sorryAx"),
        "clean": proc.returncode == 0 and "sorryAx" not in text,
        "log": str(log),
    }


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

    integration = worktree / "build-logs/pr7-verified-chain-integration/CURRENT.json"
    if not integration.exists():
        raise SystemExit("verified chain integration evidence missing")
    integration_status = json.loads(integration.read_text(encoding="utf-8"))
    if integration_status.get("complete") is not True:
        raise SystemExit("verified chain integration evidence is not complete")

    metrics: list[Metric] = []
    blocked = ""
    mock1_targets = sorted(path.stem for path in source_dir.glob("Mock1*.lean"))
    for stem in mock1_targets:
        for run in (1, 2):
            metric = compile_one(worktree, logs, "mock1-final", stem, run)
            metrics.append(metric)
            if not passed(metric): blocked = f"{stem} final run {run} failed"; break
        if blocked: break

    if not blocked:
        build_all = compile_one(worktree, logs, "buildall-direct", "BuildAll", 1)
        metrics.append(build_all)
        if not passed(build_all): blocked = "BuildAll direct compile failed"

    order = module_order(source_dir)
    clean_runs: list[dict[str, Any]] = []
    if not blocked:
        for clean_run in (1, 2):
            shutil.rmtree(worktree / ".lake/build/lib/lean/PrimalitySheafVerification", ignore_errors=True)
            shutil.rmtree(worktree / ".lake/build/ir/PrimalitySheafVerification", ignore_errors=True)
            row_metrics: list[Metric] = []
            for stem in order:
                metric = compile_one(worktree, logs, f"clean-rebuild-{clean_run}", stem, 1)
                metrics.append(metric); row_metrics.append(metric)
                if not passed(metric): blocked = f"clean rebuild {clean_run} failed at {stem}"; break
            clean_runs.append({"run": clean_run, "complete": not blocked, "metrics": [asdict(m) for m in row_metrics]})
            if blocked: break

    project_sources = sorted(source_dir.glob("*.lean"))
    audit = trust_audit(project_sources)
    if not audit["clean"] and not blocked:
        blocked = "whole-project forbidden-token audit failed"

    spt5 = spt5_axiom_audit(worktree, output) if not blocked else {"clean": False, "skipped": True}
    if not spt5.get("clean") and not blocked:
        blocked = "Spt5 whole-file sorryAx audit failed"

    complete = not blocked
    status = {
        "classification": "VERIFIED" if complete else "INFRA FAILURE",
        "authority": "fresh direct Lean source compiles on PR7 integration worktree",
        "complete": complete,
        "blocked": blocked,
        "integration_evidence": integration_status,
        "mock1_targets": mock1_targets,
        "module_order": order,
        "metrics": [asdict(metric) for metric in metrics],
        "clean_rebuilds": clean_runs,
        "whole_project_trust_audit": audit,
        "Spt5_whole_file_axiom_audit": spt5,
    }
    (output / "CURRENT.json").write_text(json.dumps(status, indent=2) + "\n", encoding="utf-8")
    (output / "CURRENT.txt").write_text(
        f"classification={status['classification']}\ncomplete={str(complete).lower()}\nblocked={blocked}\n"
        f"mock1_targets={','.join(mock1_targets)}\nmodule_count={len(order)}\n"
        f"clean_rebuild_1={str(bool(clean_runs and clean_runs[0]['complete'])).lower()}\n"
        f"clean_rebuild_2={str(bool(len(clean_runs)>1 and clean_runs[1]['complete'])).lower()}\n"
        f"spt5_sorryAx_clean={str(bool(spt5.get('clean'))).lower()}\n",
        encoding="utf-8",
    )
    print(json.dumps(status, indent=2))
    if not complete: raise SystemExit(1)


if __name__ == "__main__":
    main()
