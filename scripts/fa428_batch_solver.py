#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import importlib.util
import json
import os
import re
import shutil
import subprocess
import sys
from dataclasses import asdict
from pathlib import Path
from typing import Any

ROOT = Path.cwd()
SOURCE = ROOT / "PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean"
BASELINE = Path("/tmp/fa428-baseline.lean")
SELECTION = Path("/tmp/fa428-selection.json")
REFS = Path("/tmp/fa425-donor-refs.txt")
LOG_DIR = ROOT / "build-logs/fa428-batch-blocker-screen"
GENERATED = LOG_DIR / "generated"
FULL_CANDIDATES = LOG_DIR / "full-candidates"
THEOREM = "actualEdgeAmbientParam_hasDerivAt"
TOP_RE = re.compile(r"^(?:/--|/-!|theorem\s|lemma\s|def\s|noncomputable\s+def\s|abbrev\s|noncomputable\s+abbrev\s|instance\s|local\s+instance\s|attribute\s|structure\s|class\s|namespace\s|(?:public\s+|noncomputable\s+)?section\s|end\b)")
ERROR_RE = re.compile(r"\.lean:(\d+):(\d+):\s+(?:error(?:\([^)]*\))?:|error:)")
MAX_BATCH_CANDIDATES = 60
MAX_FULL_SUCCESSES = 10

spec = importlib.util.spec_from_file_location("fa428_common", ROOT / "scripts/fa425_run_strict_controller.py")
if spec is None or spec.loader is None:
    raise RuntimeError("cannot import direct compiler helper")
common = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = common
spec.loader.exec_module(common)
common.LOG_DIR = LOG_DIR


def sha_text(text: str) -> str:
    return hashlib.sha256(text.encode()).hexdigest()


def locate(lines: list[str]) -> tuple[int, int, int]:
    starts = [i for i, s in enumerate(lines) if s.startswith(f"theorem {THEOREM}")]
    if len(starts) != 1:
        raise RuntimeError(f"expected one {THEOREM}, found {len(starts)}")
    start = starts[0]
    by_line = next(i for i in range(start, min(len(lines), start + 120)) if ":= by" in lines[i])
    end = next(i for i in range(by_line + 1, len(lines)) if lines[i] and not lines[i][0].isspace() and TOP_RE.match(lines[i]))
    return start, by_line, end


def doc_start(lines: list[str], start: int) -> int:
    i = start - 1
    while i >= 0 and not lines[i].strip():
        i -= 1
    if i >= 0 and lines[i].strip().endswith("-/"):
        j = i
        while j >= 0 and not lines[j].lstrip().startswith(("/--", "/-!")):
            j -= 1
        if j >= 0:
            return j
    return start


def recorded_score(selection: dict[str, Any]) -> tuple[int, int, int]:
    selected = selection.get("selected", {})
    score = selected.get("score")
    if isinstance(score, list) and len(score) >= 3:
        return tuple(int(x) for x in score[:3])
    metric = selected.get("metric", {})
    return (1 if metric.get("exit_zero") else 0, int(metric.get("first_error_line", 0)), int(metric.get("first_error_col", 0)))


def metric_score(metric: Any) -> tuple[int, int, int]:
    return (1 if common.passed(metric) else 0, int(metric.first_error_line), int(metric.first_error_col))


def run_generator(name: str, script: str, baseline: Path, refs: Path, limit: int = 18) -> tuple[Path, dict[str, Any]] | None:
    out = GENERATED / name
    out.mkdir(parents=True, exist_ok=True)
    command = ["python3", script, "--baseline", str(baseline), "--output", str(out), "--refs", str(refs), "--limit", str(limit)]
    proc = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, check=False)
    (out / "GENERATOR.log").write_text(proc.stdout, encoding="utf-8")
    manifest = out / "MANIFEST.json"
    if proc.returncode != 0 or not manifest.exists():
        return None
    try:
        return out, json.loads(manifest.read_text(encoding="utf-8"))
    except Exception:
        return None


def scope_closures(prefix: list[str]) -> list[str]:
    stack: list[str] = []
    block_comment = 0
    for raw in prefix:
        line = raw
        # Coarse comment filtering is sufficient for top-level namespace/section commands.
        stripped = line.strip()
        if block_comment:
            block_comment += stripped.count("/-") - stripped.count("-/")
            continue
        if stripped.startswith(("/-", "/--", "/-!")):
            block_comment += stripped.count("/-") - stripped.count("-/")
            if block_comment <= 0:
                block_comment = 0
            continue
        if not line or line[0].isspace() or stripped.startswith("--"):
            continue
        m_namespace = re.match(r"^namespace(?:\s+([^\s]+))?", stripped)
        m_section = re.match(r"^(?:(?:public|noncomputable|private)\s+)?section(?:\s+([^\s]+))?", stripped)
        if m_namespace:
            stack.append(m_namespace.group(1) or "")
        elif m_section:
            stack.append(m_section.group(1) or "")
        elif re.match(r"^end(?:\s|$)", stripped):
            if stack:
                stack.pop()
    return [f"end {name}\n" if name else "end\n" for name in reversed(stack)]


def allowed_prelude(line: str) -> bool:
    stripped = line.strip()
    return stripped.startswith(("local instance", "attribute ", "local attribute "))


def main() -> None:
    LOG_DIR.mkdir(parents=True, exist_ok=True)
    GENERATED.mkdir(parents=True, exist_ok=True)
    FULL_CANDIDATES.mkdir(parents=True, exist_ok=True)
    if not BASELINE.exists() or not SELECTION.exists():
        raise SystemExit("FA428 baseline/selection missing")
    baseline_text = BASELINE.read_text(encoding="utf-8")
    baseline_lines = baseline_text.splitlines(keepends=True)
    if len(baseline_lines) != 60453:
        raise SystemExit("FA428 baseline is not fixed 60453-line source")
    baseline_sha = sha_text(baseline_text)
    selection = json.loads(SELECTION.read_text(encoding="utf-8"))
    shutil.copy2(BASELINE, SOURCE)

    m2 = common.compile_source("Mock2", "Mock2-direct", 500)
    m2a = common.compile_source("Mock2_Advanced", "Mock2_Advanced-direct", 500)
    if not common.passed(m2) or not common.passed(m2a):
        raise SystemExit("Mock2 prerequisites regressed before FA428")
    baseline_metric = common.compile_source("Mock2_FunctionalAnalysis", "FA-baseline-direct", 1)
    if baseline_metric.source_sha256 != baseline_sha or baseline_metric.line_count != 60453:
        raise SystemExit("FA428 baseline direct metric identity mismatch")
    if metric_score(baseline_metric) < recorded_score(selection):
        raise SystemExit("FA428 fresh baseline regressed below selected evidence")
    common.write_context(baseline_metric, SOURCE, LOG_DIR / "BASELINE_FIRST_ERROR_CONTEXT.txt")

    start, by_line, theorem_end = locate(baseline_lines)
    dstart = doc_start(baseline_lines, start)
    baseline_header = tuple(baseline_lines[start : by_line + 1])
    generator_specs = [
        ("generic", "scripts/fa425_strict_theorem_tournament.py"),
        ("preheader", "scripts/fa425b_preheader_candidates.py"),
        ("unfold", "scripts/fa425c_instance_unfold_candidates.py"),
        ("rebundle", "scripts/fa425d_derivative_rebundle_candidates.py"),
        ("isolated-section", "scripts/fa425e_isolated_instance_section_candidates.py"),
        ("transport", "scripts/fa425f_instance_transport_candidates.py"),
        ("sandwich", "scripts/fa425g_instance_sandwich_candidates.py"),
    ]
    candidates: list[dict[str, Any]] = []
    seen = {baseline_sha}
    generator_records = []
    for label, script in generator_specs:
        result = run_generator(label, script, BASELINE, REFS)
        if result is None:
            generator_records.append({"label": label, "success": False})
            continue
        directory, manifest = result
        generator_records.append({"label": label, "success": True, "candidate_count": manifest.get("candidate_count", 0)})
        for item in manifest.get("candidates", []):
            path = directory / item["file"]
            if not path.exists():
                continue
            text = path.read_text(encoding="utf-8")
            digest = sha_text(text)
            lines = text.splitlines(keepends=True)
            if digest in seen or digest != item.get("sha256") or len(lines) != 60453:
                continue
            try:
                cs, cb, ce = locate(lines)
            except Exception:
                continue
            if cs != start or cb != by_line or tuple(lines[cs : cb + 1]) != baseline_header:
                continue
            seen.add(digest)
            target = FULL_CANDIDATES / f"{len(candidates):03d}.lean"
            target.write_text(text, encoding="utf-8")
            candidates.append({
                "index": len(candidates),
                "name": f"{label}:{item.get('name', target.stem)}",
                "provenance": item.get("provenance", label),
                "source_sha256": digest,
                "file": target.name,
                "theorem_end": ce,
            })
            if len(candidates) >= MAX_BATCH_CANDIDATES:
                break
        if len(candidates) >= MAX_BATCH_CANDIDATES:
            break

    if common.passed(baseline_metric):
        candidates = []

    diagnostic_lines = list(baseline_lines[:dstart])
    ranges = []
    for item in candidates:
        text = (FULL_CANDIDATES / item["file"]).read_text(encoding="utf-8")
        lines = text.splitlines(keepends=True)
        cs, cb, ce = locate(lines)
        prelude = []
        for i in range(max(0, dstart - 80), start):
            if lines[i] != baseline_lines[i] and allowed_prelude(lines[i]):
                prelude.append(lines[i])
        body = lines[cb + 1 : ce]
        block_start = len(diagnostic_lines) + 1
        diagnostic_lines.append(f"section FA428CandidateScope{item['index']:03d}\n")
        diagnostic_lines.extend(prelude)
        renamed_header = list(baseline_header)
        renamed_header[0] = renamed_header[0].replace(
            f"theorem {THEOREM}", f"theorem {THEOREM}_candidate_{item['index']:03d}", 1
        )
        diagnostic_lines.extend(renamed_header)
        diagnostic_lines.extend(body)
        diagnostic_lines.append(f"end FA428CandidateScope{item['index']:03d}\n")
        block_end = len(diagnostic_lines)
        ranges.append({**item, "diagnostic_start_line": block_start, "diagnostic_end_line": block_end, "prelude": prelude})

    marker_line = len(diagnostic_lines) + 1
    diagnostic_lines.extend([
        "theorem FA428_batch_end_marker : True := by trivial\n",
        "#check FA428_batch_end_marker\n",
    ])
    diagnostic_lines.extend(scope_closures(baseline_lines[:dstart]))
    diagnostic = LOG_DIR / "FA428BatchDiagnostic.lean"
    diagnostic.write_text("".join(diagnostic_lines), encoding="utf-8")

    diagnostic_log = LOG_DIR / "FA428BatchDiagnostic.log"
    diagnostic_rc = 0
    if candidates:
        with diagnostic_log.open("wb") as out:
            proc = subprocess.run([
                "lake", "env", "lean", "-DmaxErrors=5000", "-DwarningAsError=false",
                "-o", "/tmp/FA428BatchDiagnostic.olean", str(diagnostic),
            ], stdout=out, stderr=subprocess.STDOUT, check=False)
        diagnostic_rc = proc.returncode
    else:
        diagnostic_log.write_text("baseline already exits zero; batch screening skipped\n", encoding="utf-8")
    log_text = diagnostic_log.read_text(encoding="utf-8", errors="replace")
    error_matches = list(ERROR_RE.finditer(log_text))
    error_lines = [int(m.group(1)) for m in error_matches]
    reached_end = not candidates or "FA428_batch_end_marker" in log_text
    batch_rows = []
    successful = []
    for item in ranges:
        errors = [line for line in error_lines if item["diagnostic_start_line"] <= line <= item["diagnostic_end_line"]]
        passed_batch = reached_end and not errors
        row = {**item, "diagnostic_error_lines": errors, "batch_pass": passed_batch}
        batch_rows.append(row)
        if passed_batch:
            successful.append(item)
    outside_errors = [line for line in error_lines if not any(r["diagnostic_start_line"] <= line <= r["diagnostic_end_line"] for r in ranges)]
    batch_status = {
        "authority": "direct Lean CLI diagnostic screening; full source direct compile remains promotion authority",
        "baseline": asdict(baseline_metric),
        "generator_records": generator_records,
        "candidate_count": len(candidates),
        "diagnostic_exit": diagnostic_rc,
        "diagnostic_reached_end_marker": reached_end,
        "diagnostic_error_headers": len(error_matches),
        "outside_candidate_error_lines": outside_errors,
        "marker_line": marker_line,
        "successful_candidate_count": len(successful),
        "rows": batch_rows,
    }
    (LOG_DIR / "BATCH_STATUS.json").write_text(json.dumps(batch_status, indent=2) + "\n", encoding="utf-8")

    best: tuple[Any, Path, dict[str, Any]] | None = None
    full_rows = []
    for item in successful[:MAX_FULL_SUCCESSES]:
        path = FULL_CANDIDATES / item["file"]
        shutil.copy2(path, SOURCE)
        metric = common.compile_source("Mock2_FunctionalAnalysis", f"full-candidate-{item['index']:03d}", 1)
        better = common.strictly_better(metric, baseline_metric)
        row = {"candidate": item, "metric": asdict(metric), "strictly_better": better}
        full_rows.append(row)
        if better and (best is None or metric_score(metric) > metric_score(best[0])):
            best = (metric, path, item)
    (LOG_DIR / "FULL_SCREENING.json").write_text(json.dumps({
        "baseline": asdict(baseline_metric),
        "rows": full_rows,
    }, indent=2) + "\n", encoding="utf-8")

    strict_promotion = False
    selected_metric = baseline_metric
    selected_source = BASELINE
    promotion = None
    if best is not None:
        screen, path, item = best
        shutil.copy2(path, SOURCE)
        verify1 = common.compile_source("Mock2_FunctionalAnalysis", "FA-promotion-reverify-run1", 1)
        verify2 = common.compile_source("Mock2_FunctionalAnalysis", "FA-promotion-reverify-run2", 1)
        consistent = (
            verify1.source_sha256 == verify2.source_sha256 == item["source_sha256"] and
            verify1.line_count == verify2.line_count == 60453 and
            common.strictly_better(verify1, baseline_metric) and common.strictly_better(verify2, baseline_metric) and
            metric_score(verify1) == metric_score(verify2)
        )
        promotion = {
            "candidate": item,
            "screening_metric": asdict(screen),
            "reverify_run1": asdict(verify1),
            "reverify_run2": asdict(verify2),
            "consistent": consistent,
        }
        if consistent:
            strict_promotion = True
            selected_metric = verify2
            selected_source = path
            common.write_context(verify2, SOURCE, LOG_DIR / "PROMOTED_FIRST_ERROR_CONTEXT.txt")
        else:
            shutil.copy2(BASELINE, SOURCE)
    else:
        shutil.copy2(BASELINE, SOURCE)
    (LOG_DIR / "PROMOTION.json").write_text(json.dumps(promotion, indent=2) + "\n" if promotion else "null\n", encoding="utf-8")

    status: dict[str, Any] = {
        "classification": "VERIFIED",
        "stage": "strict blocker promotion" if strict_promotion else "verified baseline retained",
        "Mock2": asdict(m2),
        "Mock2_Advanced": asdict(m2a),
        "baseline": {"verified": True, "source_sha256": baseline_sha, "line_count": 60453, "FA": asdict(baseline_metric)},
        "batch": {k: batch_status[k] for k in ["candidate_count", "diagnostic_exit", "diagnostic_reached_end_marker", "diagnostic_error_headers", "successful_candidate_count"]},
        "promotion": promotion,
        "strict_promotion": strict_promotion,
        "selected_source_sha256": common.sha(SOURCE),
        "selected_line_count": common.line_count(SOURCE),
        "selected_metric": asdict(selected_metric),
        "fa_true_pass": False,
        "all_required_targets_2x_pass": False,
    }
    if common.passed(selected_metric):
        shutil.copy2(selected_source, SOURCE)
        fa1 = common.compile_source("Mock2_FunctionalAnalysis", "FA-final-direct-run1", 2500)
        fa2 = common.compile_source("Mock2_FunctionalAnalysis", "FA-final-direct-run2", 2500)
        audit = common.trust_audit(SOURCE)
        fa_true_pass = common.passed(fa1) and common.passed(fa2) and fa1.source_sha256 == fa2.source_sha256 == common.sha(SOURCE) and audit["clean"]
        status["FA_final_run1"] = asdict(fa1)
        status["FA_final_run2"] = asdict(fa2)
        status["trust_audit"] = audit
        status["fa_true_pass"] = fa_true_pass
        if fa_true_pass:
            status["stage"] = "Mock2_FunctionalAnalysis TRUE PASS x2 and trust audit clean"
            (LOG_DIR / "FA_TRUE_PASS_2X_AUDIT_CLEAN").touch()
            downstream = common.run_ordered_downstream()
            status["downstream"] = downstream
            status["all_required_targets_2x_pass"] = bool(downstream.get("complete"))
            if status["all_required_targets_2x_pass"]:
                status["stage"] = "FA Integrated Mock3 QYM ordered x2 PASS"
                (LOG_DIR / "ALL_REQUIRED_TARGETS_2X_PASS").touch()

    original_branch_sha = Path("/tmp/fa425-original-source.sha").read_text().strip() if Path("/tmp/fa425-original-source.sha").exists() else ""
    materialize_baseline = not strict_promotion and original_branch_sha != baseline_sha
    source_should_commit = bool(strict_promotion or materialize_baseline or status["fa_true_pass"])
    status["materialize_verified_baseline"] = materialize_baseline
    status["source_should_commit"] = source_should_commit
    (LOG_DIR / "CURRENT.json").write_text(json.dumps(status, indent=2) + "\n", encoding="utf-8")
    (LOG_DIR / "CURRENT.txt").write_text(
        f"classification=VERIFIED\n"
        f"stage={status['stage']}\n"
        f"source_sha256={status['selected_source_sha256']}\n"
        f"line_count={status['selected_line_count']}\n"
        f"FA_exit={selected_metric.exit_code}\n"
        f"FA_first_error={selected_metric.first_error_line}:{selected_metric.first_error_col}\n"
        f"FA_declaration={selected_metric.first_error_declaration}\n"
        f"batch_candidates={batch_status['candidate_count']}\n"
        f"batch_successes={batch_status['successful_candidate_count']}\n"
        f"strict_promotion={str(strict_promotion).lower()}\n"
        f"fa_true_pass={str(status['fa_true_pass']).lower()}\n"
        f"all_required_targets_2x_pass={str(status['all_required_targets_2x_pass']).lower()}\n",
        encoding="utf-8",
    )
    output = os.environ.get("GITHUB_OUTPUT")
    if output:
        with open(output, "a", encoding="utf-8") as f:
            f.write(f"source_should_commit={str(source_should_commit).lower()}\n")
            f.write(f"strict_promotion={str(strict_promotion).lower()}\n")
            f.write(f"fa_true_pass={str(status['fa_true_pass']).lower()}\n")
            f.write(f"all_chain_pass={str(status['all_required_targets_2x_pass']).lower()}\n")
            f.write(f"controller_success={str(bool(strict_promotion or materialize_baseline or status['fa_true_pass'])).lower()}\n")
    print(json.dumps(status, indent=2))


if __name__ == "__main__":
    main()
