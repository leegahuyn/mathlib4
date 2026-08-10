#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import importlib.util
import json
import os
import shutil
import subprocess
import sys
from dataclasses import asdict
from pathlib import Path
from typing import Any

ROOT = Path.cwd()
SOURCE = ROOT / "PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean"
BASELINE = Path("/tmp/fa427-baseline.lean")
SELECTION = Path("/tmp/fa427-selection.json")
REFS = Path("/tmp/fa425-donor-refs.txt")
OUT = Path("/tmp/fa427-prepared")
LOGS = OUT / "logs"
CANDIDATES = OUT / "candidates"
PREREQ = OUT / "prerequisites"
MAX_CANDIDATES = 24

spec = importlib.util.spec_from_file_location("fa427_common", ROOT / "scripts/fa425_run_strict_controller.py")
if spec is None or spec.loader is None:
    raise RuntimeError("cannot load direct compiler helper")
common = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = common
spec.loader.exec_module(common)
common.LOG_DIR = LOGS


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def recorded_score(selection: dict[str, Any]) -> tuple[int, int, int]:
    selected = selection.get("selected", {})
    score = selected.get("score")
    if isinstance(score, list) and len(score) >= 3:
        return tuple(int(x) for x in score[:3])
    metric = selected.get("metric", {})
    return (
        1 if metric.get("exit_zero") else 0,
        int(metric.get("first_error_line", 0)),
        int(metric.get("first_error_col", 0)),
    )


def direct_score(metric: Any) -> tuple[int, int, int]:
    return (1 if common.passed(metric) else 0, int(metric.first_error_line), int(metric.first_error_col))


def add_manifest_sources(
    source_dir: Path,
    manifest: dict[str, Any],
    label: str,
    baseline_sha: str,
    baseline_lines: int,
    seen: set[str],
    merged: list[dict[str, Any]],
) -> None:
    for item in manifest.get("candidates", []):
        path = source_dir / item["file"]
        if not path.exists():
            continue
        digest = sha(path)
        if digest != item.get("sha256") or digest == baseline_sha or digest in seen:
            continue
        if common.line_count(path) != baseline_lines:
            continue
        seen.add(digest)
        target = CANDIDATES / f"{len(merged):03d}.lean"
        shutil.copy2(path, target)
        merged.append({
            "index": len(merged),
            "name": f"{label}:{item.get('name', path.stem)}",
            "provenance": item.get("provenance", label),
            "kind": item.get("kind", label),
            "source_sha256": digest,
            "line_count": baseline_lines,
            "file": target.name,
        })
        if len(merged) >= MAX_CANDIDATES:
            return


def run_generator(name: str, command: list[str]) -> tuple[Path, dict[str, Any]] | None:
    directory = OUT / "generated" / name
    directory.mkdir(parents=True, exist_ok=True)
    command = [part.replace("{OUT}", str(directory)) for part in command]
    proc = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, check=False)
    (directory / "GENERATOR.log").write_text(proc.stdout, encoding="utf-8")
    manifest_path = directory / "MANIFEST.json"
    if proc.returncode != 0 or not manifest_path.exists():
        return None
    try:
        return directory, json.loads(manifest_path.read_text(encoding="utf-8"))
    except Exception:
        return None


def copy_prerequisite(stem: str) -> None:
    build = ROOT / ".lake/build/lib/lean/PrimalitySheafVerification"
    for suffix in ("olean", "ilean"):
        src = build / f"{stem}.{suffix}"
        if not src.exists() or src.stat().st_size == 0:
            raise RuntimeError(f"missing prerequisite {src}")
        shutil.copy2(src, PREREQ / src.name)


def emit_outputs(matrix: list[int], baseline_metric: Any, baseline_pass: bool) -> None:
    output = os.environ.get("GITHUB_OUTPUT")
    if not output:
        return
    with open(output, "a", encoding="utf-8") as f:
        f.write("matrix=" + json.dumps(matrix, separators=(",", ":")) + "\n")
        f.write(f"baseline_sha256={baseline_metric.source_sha256}\n")
        f.write(f"baseline_first_error_line={baseline_metric.first_error_line}\n")
        f.write(f"baseline_first_error_col={baseline_metric.first_error_col}\n")
        f.write(f"baseline_declaration={baseline_metric.first_error_declaration}\n")
        f.write(f"baseline_pass={str(baseline_pass).lower()}\n")


def main() -> None:
    OUT.mkdir(parents=True, exist_ok=True)
    LOGS.mkdir(parents=True, exist_ok=True)
    CANDIDATES.mkdir(parents=True, exist_ok=True)
    PREREQ.mkdir(parents=True, exist_ok=True)
    if not BASELINE.exists() or not SELECTION.exists():
        raise SystemExit("selected baseline source/metadata missing")
    shutil.copy2(BASELINE, SOURCE)
    selection = json.loads(SELECTION.read_text(encoding="utf-8"))
    baseline_sha = sha(SOURCE)
    baseline_lines = common.line_count(SOURCE)
    if baseline_lines != 60453:
        raise SystemExit(f"baseline line count {baseline_lines} != 60453")

    m2 = common.compile_source("Mock2", "Mock2-direct", 500)
    m2a = common.compile_source("Mock2_Advanced", "Mock2_Advanced-direct", 500)
    if not common.passed(m2) or not common.passed(m2a):
        raise SystemExit("verified prerequisites regressed before FA427 candidate generation")
    copy_prerequisite("Mock2")
    copy_prerequisite("Mock2_Advanced")

    baseline_metric = common.compile_source("Mock2_FunctionalAnalysis", "FA-baseline-direct", 1)
    score = direct_score(baseline_metric)
    expected = recorded_score(selection)
    if score < expected:
        raise SystemExit(f"fresh baseline metric {score} regressed below selected evidence {expected}")
    if baseline_metric.source_sha256 != baseline_sha or baseline_metric.line_count != baseline_lines:
        raise SystemExit("baseline metric/source identity mismatch")
    common.write_context(baseline_metric, SOURCE, OUT / "BASELINE_FIRST_ERROR_CONTEXT.txt")
    shutil.copy2(BASELINE, OUT / "baseline.lean")

    merged: list[dict[str, Any]] = []
    seen: set[str] = set()
    generators: list[tuple[str, list[str]]] = []
    if not common.passed(baseline_metric):
        generators.append(("dynamic", [
            "python3", "scripts/fa426_dynamic_hunk_candidates.py",
            "--baseline", str(BASELINE), "--output", "{OUT}", "--refs", str(REFS),
            "--first-error-line", str(baseline_metric.first_error_line), "--limit", "18",
        ]))
        if baseline_metric.first_error_declaration == "actualEdgeAmbientParam_hasDerivAt":
            generators.extend([
                ("blocker-generic", ["python3", "scripts/fa425_strict_theorem_tournament.py", "--baseline", str(BASELINE), "--output", "{OUT}", "--refs", str(REFS), "--limit", "18"]),
                ("blocker-preheader", ["python3", "scripts/fa425b_preheader_candidates.py", "--baseline", str(BASELINE), "--output", "{OUT}", "--refs", str(REFS), "--limit", "18"]),
                ("blocker-unfold", ["python3", "scripts/fa425c_instance_unfold_candidates.py", "--baseline", str(BASELINE), "--output", "{OUT}", "--refs", str(REFS), "--limit", "18"]),
            ])
    generator_records = []
    for name, command in generators:
        result = run_generator(name, command)
        if result is None:
            generator_records.append({"name": name, "success": False})
            continue
        directory, manifest = result
        generator_records.append({"name": name, "success": True, "candidate_count": manifest.get("candidate_count", 0)})
        add_manifest_sources(directory, manifest, name, baseline_sha, baseline_lines, seen, merged)
        if len(merged) >= MAX_CANDIDATES:
            break

    if not merged:
        target = CANDIDATES / "000.lean"
        shutil.copy2(BASELINE, target)
        merged.append({
            "index": 0,
            "name": "baseline-control",
            "provenance": "control; not promotion eligible",
            "kind": "control",
            "source_sha256": baseline_sha,
            "line_count": baseline_lines,
            "file": target.name,
        })

    manifest = {
        "authority": "direct Lean CLI",
        "maxErrors_cap": 1,
        "maxErrors_interpretation": "screening stops after first actual error; it is not total error count or completion percentage",
        "selection": selection,
        "baseline": asdict(baseline_metric),
        "Mock2": asdict(m2),
        "Mock2_Advanced": asdict(m2a),
        "generator_records": generator_records,
        "candidate_count": len(merged),
        "candidates": merged,
    }
    (OUT / "MANIFEST.json").write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    matrix = [item["index"] for item in merged]
    emit_outputs(matrix, baseline_metric, common.passed(baseline_metric))
    print(json.dumps({"candidate_count": len(merged), "matrix": matrix, "baseline": asdict(baseline_metric)}, indent=2))


if __name__ == "__main__":
    main()
