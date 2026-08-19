#!/usr/bin/env python3
from __future__ import annotations

from difflib import SequenceMatcher
from pathlib import Path
import hashlib
import importlib.util
import json
import os
import sys

ROOT = Path(os.environ.get("GITHUB_WORKSPACE", Path.cwd())).resolve()
CORE_PATH = ROOT / ".github/qym_repair_c2_c6_serial.py"
RESULT_PATH = ROOT / ".github/qym-frontier/C2_C6_RESULT.json"

if RESULT_PATH.is_file():
    try:
        existing = json.loads(RESULT_PATH.read_text(encoding="utf-8"))
    except Exception:
        existing = {}
    if existing.get("c2_c6_clean") is True and existing.get("strict_improvement") is True:
        print(json.dumps({"already_verified": True, "result": existing}, indent=2, sort_keys=True))
        raise SystemExit(0)

spec = importlib.util.spec_from_file_location("qym_repair_core", CORE_PATH)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot import repair core from {CORE_PATH}")
core = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = core
spec.loader.exec_module(core)

_original_load_artifact = core.load_artifact


def load_artifact_normalized(label: str, artifact_id: int):
    artifact = _original_load_artifact(label, artifact_id)
    artifact.result.setdefault(
        "candidate_qym_sha256",
        hashlib.sha256(artifact.source.encode("utf-8")).hexdigest(),
    )
    return artifact


def diff_hunks_envelope(base: str, candidate: str):
    base_lines = base.splitlines(keepends=True)
    candidate_lines = candidate.splitlines(keepends=True)
    matcher = SequenceMatcher(None, base_lines, candidate_lines, autojunk=False)
    changed = [
        (tag, i1, i2, j1, j2)
        for tag, i1, i2, j1, j2 in matcher.get_opcodes()
        if tag != "equal"
    ]
    if not changed:
        raise RuntimeError("candidate has no source change")
    i1 = min(row[1] for row in changed)
    i2 = max(row[2] for row in changed)
    j1 = min(row[3] for row in changed)
    j2 = max(row[4] for row in changed)
    span = max(i2 - i1, j2 - j1)
    if span > 5000:
        raise RuntimeError(f"candidate repair envelope is unexpectedly large: {span} lines")
    return [
        core.Hunk(
            i1=i1,
            i2=i2,
            j1=j1,
            j2=j2,
            old="".join(base_lines[i1:i2]),
            new="".join(candidate_lines[j1:j2]),
        )
    ]


core.load_artifact = load_artifact_normalized
core.diff_hunks = diff_hunks_envelope

# Additional C2 forms are tested only if the primary explicit constructions fail.
core.C2_VARIANTS.update(
    {
        "ofRealCLM_comp_id": core.c2_theorem(
            "    simpa only [Complex.ofRealCLM_apply] using\n"
            "      (((Complex.ofRealCLM : ℝ →L[ℝ] ℂ).contDiff).comp contDiff_id)"
        ),
        "ofRealCLM_convert": core.c2_theorem(
            "    convert ((Complex.ofRealCLM : ℝ →L[ℝ] ℂ).contDiff) using 1 <;> rfl"
        ),
    }
)

core.main()
