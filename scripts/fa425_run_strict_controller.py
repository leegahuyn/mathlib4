#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import json
import os
import re
import shutil
import subprocess
from dataclasses import dataclass, asdict
from pathlib import Path
from typing import Any

ROOT = Path.cwd()
SRC_DIR = ROOT / "PrimalitySheafVerification"
FA = SRC_DIR / "Mock2_FunctionalAnalysis.lean"
BASELINE = Path("/tmp/fa425-baseline.lean")
REFS = Path("/tmp/fa425-donor-refs.txt")
LOG_DIR = ROOT / "build-logs/fa425-strict-theorem-tournament"
CANDIDATES = LOG_DIR / "candidates"
BUILD_DIR = ROOT / ".lake/build/lib/lean/PrimalitySheafVerification"
EXPECTED_SHA_31725 = "07f6efd3309c3cc23b86adf5811918b752b72c33a3f7a76213ce9beb10796da4"
EXPECTED_SHA_31726 = "71dc36f16ebea92d537aa40a5d420443e4bcb93ccb76fea31efb40a6cb5c3aa0"
EXPECTED_LINES = 60453
BLOCKER = "actualEdgeAmbientParam_hasDerivAt"
ERROR_RE = re.compile(r"\.lean:(\d+):(\d+):\s+(?:error(?:\([^)]*\))?:|error:)")
DECL_RE = re.compile(
    r"^(?:theorem|lemma|def|noncomputable\s+def|abbrev|noncomputable\s+abbrev|instance|structure|class)\s+([^\s(:]+)"
)


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def line_count(path: Path) -> int:
    return len(path.read_text(encoding="utf-8").splitlines())


def declaration_at(path: Path, line: int) -> str:
    if line <= 0:
        return ""
    current = ""
    for idx, text in enumerate(path.read_text(encoding="utf-8", errors="replace").splitlines(), 1):
        if idx > line:
            break
        m = DECL_RE.match(text)
        if m:
            current = m.group(1)
    return current


@dataclass
class Metric:
    label: str
    stem: str
    source_sha256: str
    line_count: int
    exit_code: int
    error_headers: int
    first_error_line: int
    first_error_col: int
    first_error_declaration: str
    olean: bool
    ilean: bool
    max_errors: int
    log: str


def compile_source(stem: str, label: str, max_errors: int) -> Metric:
    src = SRC_DIR / f"{stem}.lean"
    olean = BUILD_DIR / f"{stem}.olean"
    ilean = BUILD_DIR / f"{stem}.ilean"
    olean.parent.mkdir(parents=True, exist_ok=True)
    olean.unlink(missing_ok=True)
    ilean.unlink(missing_ok=True)
    log_path = LOG_DIR / f"{label}.log"
    cmd = [
        "lake", "env", "lean",
        f"-DmaxErrors={max_errors}",
        "-DwarningAsError=false",
        "-o", str(olean),
        "-i", str(ilean),
        str(src),
    ]
    with log_path.open("wb") as out:
        proc = subprocess.run(cmd, stdout=out, stderr=subprocess.STDOUT, check=False)
    text = log_path.read_text(encoding="utf-8", errors="replace")
    matches = list(ERROR_RE.finditer(text))
    first_line = int(matches[0].group(1)) if matches else 0
    first_col = int(matches[0].group(2)) if matches else 0
    metric = Metric(
        label=label,
        stem=stem,
        source_sha256=sha(src),
        line_count=line_count(src),
        exit_code=proc.returncode,
        error_headers=len(matches),
        first_error_line=first_line,
        first_error_col=first_col,
        first_error_declaration=declaration_at(src, first_line),
        olean=olean.exists() and olean.stat().st_size > 0,
        ilean=ilean.exists() and ilean.stat().st_size > 0,
        max_errors=max_errors,
        log=str(log_path.relative_to(ROOT)),
    )
    (LOG_DIR / f"{label}.metric.json").write_text(json.dumps(asdict(metric), indent=2) + "\n", encoding="utf-8")
    return metric


def passed(m: Metric) -> bool:
    return m.exit_code == 0 and m.error_headers == 0 and m.olean and m.ilean


def strictly_better(candidate: Metric, baseline: Metric) -> bool:
    if candidate.line_count != baseline.line_count:
        return False
    if passed(candidate):
        return True
    if candidate.exit_code == 0 or candidate.first_error_line <= 0:
        return False
    return candidate.first_error_line > baseline.first_error_line


def metric_rank(m: Metric) -> tuple[int, int, int]:
    return (1 if passed(m) else 0, m.first_error_line, m.first_error_col)


def write_context(metric: Metric, source: Path, destination: Path) -> None:
    log_path = ROOT / metric.log
    lines = log_path.read_text(encoding="utf-8", errors="replace").splitlines()
    log_context: list[str] = []
    if metric.first_error_line:
        needle = f".lean:{metric.first_error_line}:{metric.first_error_col}:"
        for i, line in enumerate(lines):
            if needle in line:
                log_context = lines[max(0, i - 5) : min(len(lines), i + 65)]
                break
    src_lines = source.read_text(encoding="utf-8", errors="replace").splitlines()
    lo = max(1, metric.first_error_line - 20)
    hi = min(len(src_lines), metric.first_error_line + 35)
    source_context = [f"{i}: {src_lines[i-1]}" for i in range(lo, hi + 1)] if metric.first_error_line else []
    destination.write_text(
        "[METRIC]\n" + json.dumps(asdict(metric), indent=2) +
        "\n\n[LEAN LOG CONTEXT]\n" + "\n".join(log_context) +
        "\n\n[SOURCE CONTEXT]\n" + "\n".join(source_context) + "\n",
        encoding="utf-8",
    )


def strip_lean_comments_and_strings(text: str) -> str:
    out: list[str] = []
    i = 0
    block = 0
    in_string = False
    while i < len(text):
        if block:
            if text.startswith("/-", i):
                block += 1
                i += 2
            elif text.startswith("-/", i):
                block -= 1
                i += 2
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif in_string:
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
        elif text.startswith("--", i):
            while i < len(text) and text[i] != "\n":
                out.append(" ")
                i += 1
        elif text.startswith("/-", i):
            block = 1
            out.extend("  ")
            i += 2
        elif text[i] == '"':
            in_string = True
            out.append(" ")
            i += 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def trust_audit(path: Path) -> dict[str, Any]:
    cleaned = strip_lean_comments_and_strings(path.read_text(encoding="utf-8", errors="replace"))
    patterns = {
        "sorry": re.compile(r"\bsorry\b"),
        "admit": re.compile(r"\badmit\b"),
        "global_axiom": re.compile(r"(?m)^\s*axiom\s+"),
        "unsafe": re.compile(r"(?m)^\s*(?:private\s+|protected\s+)?unsafe\b"),
        "native_decide": re.compile(r"\bnative_decide\b"),
        "Lean.ofReduceBool": re.compile(r"\bLean\.ofReduceBool\b"),
    }
    counts = {name: len(list(pattern.finditer(cleaned))) for name, pattern in patterns.items()}
    return {"counts": counts, "clean": all(v == 0 for v in counts.values())}


def run_ordered_downstream() -> dict[str, Any]:
    result: dict[str, Any] = {"Integrated": [], "Mock3": {}, "QYM": []}
    integrated = SRC_DIR / "Mock2_FunctionalAnalysis_Integrated.lean"
    if not integrated.exists():
        result["complete"] = False
        result["blocked"] = "Mock2_FunctionalAnalysis_Integrated.lean missing"
        return result
    for run in (1, 2):
        m = compile_source("Mock2_FunctionalAnalysis_Integrated", f"Integrated-run{run}", 2000)
        result["Integrated"].append(asdict(m))
        if not passed(m):
            result["complete"] = False
            result["blocked"] = f"Integrated run {run} failed"
            return result

    bridges = sorted(p for p in SRC_DIR.glob("Mock3*.lean") if p.name != "QYM.lean")
    for bridge in bridges:
        stem = bridge.stem
        result["Mock3"][stem] = []
        for run in (1, 2):
            m = compile_source(stem, f"{stem}-run{run}", 2000)
            result["Mock3"][stem].append(asdict(m))
            if not passed(m):
                result["complete"] = False
                result["blocked"] = f"{stem} run {run} failed"
                return result

    qym = SRC_DIR / "QYM.lean"
    if not qym.exists():
        result["complete"] = False
        result["blocked"] = "QYM.lean missing"
        return result
    for run in (1, 2):
        m = compile_source("QYM", f"QYM-run{run}", 2000)
        result["QYM"].append(asdict(m))
        if not passed(m):
            result["complete"] = False
            result["blocked"] = f"QYM run {run} failed"
            return result
    result["complete"] = True
    result["bridge_count"] = len(bridges)
    return result


def emit_outputs(values: dict[str, str]) -> None:
    output = os.environ.get("GITHUB_OUTPUT")
    if not output:
        return
    with open(output, "a", encoding="utf-8") as f:
        for key, value in values.items():
            f.write(f"{key}={value}\n")


def main() -> None:
    LOG_DIR.mkdir(parents=True, exist_ok=True)
    if not BASELINE.exists():
        raise SystemExit("resolved baseline source is missing")
    shutil.copy2(BASELINE, FA)
    baseline_sha = sha(FA)
    baseline_lines = line_count(FA)
    original_sha = Path("/tmp/fa425-original-source.sha").read_text().strip() if Path("/tmp/fa425-original-source.sha").exists() else ""
    origin = Path("/tmp/fa425-champion-origin.txt").read_text(encoding="utf-8").strip() if Path("/tmp/fa425-champion-origin.txt").exists() else "unknown"

    m2 = compile_source("Mock2", "Mock2-prerequisite", 400)
    m2a = compile_source("Mock2_Advanced", "Mock2_Advanced-prerequisite", 400)
    baseline_metric = compile_source("Mock2_FunctionalAnalysis", "FA-baseline-direct", 1) if passed(m2) and passed(m2a) else Metric(
        label="FA-baseline-direct", stem="Mock2_FunctionalAnalysis", source_sha256=baseline_sha,
        line_count=baseline_lines, exit_code=125, error_headers=0, first_error_line=0,
        first_error_col=0, first_error_declaration="", olean=False, ilean=False, max_errors=1,
        log="build-logs/fa425-strict-theorem-tournament/FA-baseline-direct.log")

    minimum = 31726 if baseline_sha == EXPECTED_SHA_31726 else 31725
    baseline_verified = (
        passed(m2) and passed(m2a) and baseline_lines == EXPECTED_LINES and
        baseline_sha in {EXPECTED_SHA_31725, EXPECTED_SHA_31726} and
        (passed(baseline_metric) or baseline_metric.first_error_line >= minimum)
    )
    baseline_record = {
        "classification": "VERIFIED" if baseline_verified else "INFRA FAILURE",
        "origin": origin,
        "source_sha256": baseline_sha,
        "line_count": baseline_lines,
        "minimum_frontier": minimum,
        "Mock2": asdict(m2),
        "Mock2_Advanced": asdict(m2a),
        "FA": asdict(baseline_metric),
        "verified": baseline_verified,
    }
    (LOG_DIR / "BASELINE.json").write_text(json.dumps(baseline_record, indent=2) + "\n", encoding="utf-8")
    write_context(baseline_metric, FA, LOG_DIR / "BASELINE_FIRST_ERROR_CONTEXT.txt")

    status: dict[str, Any] = {
        "classification": "INFRA FAILURE" if not baseline_verified else "VERIFIED",
        "stage": "baseline reverify",
        "baseline": baseline_record,
        "original_branch_source_sha256": original_sha,
        "materialize_verified_baseline": baseline_verified and original_sha != baseline_sha,
        "strict_promotion": False,
        "fa_true_pass": False,
        "all_required_targets_2x_pass": False,
    }

    if not baseline_verified:
        shutil.copy2(BASELINE, FA)
        (LOG_DIR / "BASELINE_NOT_REPRODUCED").touch()
        (LOG_DIR / "CURRENT.json").write_text(json.dumps(status, indent=2) + "\n", encoding="utf-8")
        emit_outputs({"source_should_commit": "false", "strict_promotion": "false", "fa_true_pass": "false", "all_chain_pass": "false", "controller_success": "false"})
        return

    # A directly passing baseline skips the tournament and enters the final gates.
    selected_metric = baseline_metric
    selected_file = BASELINE
    tournament_rows: list[dict[str, Any]] = []

    if not passed(baseline_metric):
        subprocess.run([
            "python3", "scripts/fa425_strict_theorem_tournament.py",
            "--baseline", str(BASELINE),
            "--output", str(CANDIDATES),
            "--refs", str(REFS),
            "--limit", "14",
        ], check=True)
        manifest = json.loads((CANDIDATES / "MANIFEST.json").read_text(encoding="utf-8"))
        best: tuple[Metric, Path, dict[str, Any]] | None = None
        for idx, item in enumerate(manifest["candidates"]):
            candidate_path = CANDIDATES / item["file"]
            if item["sha256"] == baseline_sha:
                continue
            shutil.copy2(candidate_path, FA)
            label = f"candidate-{idx:02d}-{re.sub(r'[^A-Za-z0-9_.-]+', '-', item['name'])[:80]}"
            metric = compile_source("Mock2_FunctionalAnalysis", label, 1)
            row = {"candidate": item, "metric": asdict(metric), "strictly_better": strictly_better(metric, baseline_metric)}
            tournament_rows.append(row)
            if row["strictly_better"] and (best is None or metric_rank(metric) > metric_rank(best[0])):
                best = (metric, candidate_path, item)

        (LOG_DIR / "TOURNAMENT.json").write_text(json.dumps({
            "authority": "direct Lean CLI",
            "maxErrors_cap": 1,
            "maxErrors_interpretation": "cap used only to stop after the first actual error; not a total-error count",
            "baseline": asdict(baseline_metric),
            "rows": tournament_rows,
        }, indent=2) + "\n", encoding="utf-8")

        if best is not None:
            first_metric, best_path, best_item = best
            shutil.copy2(best_path, FA)
            verify1 = compile_source("Mock2_FunctionalAnalysis", "FA-promotion-reverify-run1", 1)
            verify2 = compile_source("Mock2_FunctionalAnalysis", "FA-promotion-reverify-run2", 1)
            consistent = (
                verify1.source_sha256 == verify2.source_sha256 == best_item["sha256"] and
                verify1.line_count == verify2.line_count == baseline_lines and
                strictly_better(verify1, baseline_metric) and strictly_better(verify2, baseline_metric) and
                metric_rank(verify1) == metric_rank(verify2)
            )
            promotion_record = {
                "candidate": best_item,
                "screening_metric": asdict(first_metric),
                "reverify_run1": asdict(verify1),
                "reverify_run2": asdict(verify2),
                "consistent": consistent,
            }
            (LOG_DIR / "PROMOTION_REVERIFY.json").write_text(json.dumps(promotion_record, indent=2) + "\n", encoding="utf-8")
            if consistent:
                selected_metric = verify2
                selected_file = best_path
                status["strict_promotion"] = True
                status["promotion"] = promotion_record
                (LOG_DIR / "STRICT_PROMOTION").touch()
                write_context(verify2, FA, LOG_DIR / "PROMOTED_FIRST_ERROR_CONTEXT.txt")
            else:
                shutil.copy2(BASELINE, FA)
                (LOG_DIR / "PROMOTION_REVERIFY_REJECTED").touch()
        else:
            shutil.copy2(BASELINE, FA)
            (LOG_DIR / "NO_STRICT_PROMOTION").touch()
    else:
        shutil.copy2(BASELINE, FA)

    # If the selected source exits zero, require two fresh direct passes and a clean trust audit.
    if passed(selected_metric):
        shutil.copy2(selected_file, FA)
        fa1 = compile_source("Mock2_FunctionalAnalysis", "FA-final-direct-run1", 2000)
        fa2 = compile_source("Mock2_FunctionalAnalysis", "FA-final-direct-run2", 2000)
        audit = trust_audit(FA)
        fa_true_pass = passed(fa1) and passed(fa2) and fa1.source_sha256 == fa2.source_sha256 == sha(FA) and audit["clean"]
        status["FA_final_run1"] = asdict(fa1)
        status["FA_final_run2"] = asdict(fa2)
        status["trust_audit"] = audit
        status["fa_true_pass"] = fa_true_pass
        if fa_true_pass:
            (LOG_DIR / "FA_TRUE_PASS_2X_AUDIT_CLEAN").touch()
            downstream = run_ordered_downstream()
            status["downstream"] = downstream
            status["all_required_targets_2x_pass"] = bool(downstream.get("complete"))
            if status["all_required_targets_2x_pass"]:
                (LOG_DIR / "ALL_REQUIRED_TARGETS_2X_PASS").touch()

    source_should_commit = bool(status["strict_promotion"] or status["materialize_verified_baseline"] or status["fa_true_pass"])
    if not status["strict_promotion"] and not status["fa_true_pass"]:
        shutil.copy2(BASELINE, FA)
    status["checked_in_candidate_sha256"] = sha(FA)
    status["checked_in_candidate_line_count"] = line_count(FA)
    status["source_should_commit"] = source_should_commit
    status["stage"] = (
        "all ordered targets 2x pass" if status["all_required_targets_2x_pass"] else
        "FA true pass" if status["fa_true_pass"] else
        "strict FA frontier promoted" if status["strict_promotion"] else
        "verified baseline materialized" if status["materialize_verified_baseline"] else
        "no strict promotion"
    )
    status["classification"] = "VERIFIED"
    (LOG_DIR / "CURRENT.json").write_text(json.dumps(status, indent=2) + "\n", encoding="utf-8")
    (LOG_DIR / "CURRENT.txt").write_text(
        f"classification={status['classification']}\n"
        f"stage={status['stage']}\n"
        f"baseline_sha256={baseline_sha}\n"
        f"baseline_first_error={baseline_metric.first_error_line}:{baseline_metric.first_error_col}\n"
        f"baseline_declaration={baseline_metric.first_error_declaration}\n"
        f"strict_promotion={str(status['strict_promotion']).lower()}\n"
        f"checked_in_candidate_sha256={status['checked_in_candidate_sha256']}\n"
        f"fa_true_pass={str(status['fa_true_pass']).lower()}\n"
        f"all_required_targets_2x_pass={str(status['all_required_targets_2x_pass']).lower()}\n",
        encoding="utf-8",
    )
    emit_outputs({
        "source_should_commit": str(source_should_commit).lower(),
        "strict_promotion": str(status["strict_promotion"]).lower(),
        "fa_true_pass": str(status["fa_true_pass"]).lower(),
        "all_chain_pass": str(status["all_required_targets_2x_pass"]).lower(),
        "controller_success": str(bool(status["strict_promotion"] or status["materialize_verified_baseline"] or status["fa_true_pass"])).lower(),
    })


if __name__ == "__main__":
    main()
