from __future__ import annotations

import argparse
import importlib.util
import json
import os
import re
import shutil
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MODULE_PATH = Path(__file__).with_name("pass376_multitarget_agent.py")
spec = importlib.util.spec_from_file_location("pass376_core", MODULE_PATH)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load {MODULE_PATH}")
core = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = core
spec.loader.exec_module(core)

LOG_ROOT = ROOT / "build-logs" / "pass376-aider"
STATE_PATH = ROOT / "build-logs" / "pass376-v2-state.json"
BASELINE_PATH = ROOT / "build-logs" / "pass376-v2-baseline.json"


def reduction_key(result: core.CompileResult, width: int = 12) -> tuple[int, ...]:
    if result.passed:
        return (1,) + (10**9,) * (width * 2 + 1)
    flattened = [0]
    for line, col in result.positions[:width]:
        flattened.extend([line, col])
    while len(flattened) < 1 + width * 2:
        flattened.extend([10**9, 10**9])
    try:
        size = result.log_path.stat().st_size
    except OSError:
        size = 10**9
    flattened.append(-size)
    return tuple(flattened[: 2 + width * 2])


def load_state() -> dict:
    if STATE_PATH.exists():
        return json.loads(STATE_PATH.read_text(encoding="utf-8"))
    return {"version": 2, "verified": {}, "history": [], "success": False}


def active_target(state: dict, paths: list[Path]) -> Path:
    active = state.get("active_target")
    if isinstance(active, str):
        candidate = ROOT / active
        if candidate in paths and candidate.exists():
            return candidate
    verified = state.get("verified", {})
    for path in paths:
        key = str(path.relative_to(ROOT))
        entry = verified.get(key)
        if not entry or entry.get("sha256") != core.sha256_file(path):
            return path
    return paths[-1]


def build_prompt(path: Path, baseline: core.CompileResult) -> str:
    context = core.error_context(path, baseline)
    relative = path.relative_to(ROOT)
    return f"""
Work only on `{relative}` and repair its current Lean 4.33.0-rc1/mathlib compile errors.
Run the configured Lean test after editing and use the test output to refine the proof.

Non-negotiable rules:
- Do not change any existing public theorem/lemma/corollary statement, binder, assumption, conclusion, or name.
- You may rewrite proof bodies and add only private helper lemmas/theorems.
- Never use or add sorry, admit, a global axiom, unsafe, native_decide, or Lean.ofReduceBool.
- Do not delete existing imports.
- Do not edit any other file.
- Prefer current Mathlib lemmas, explicit `change`/`calc`/`ext`, and small typed transports.
- Fix the earliest independent errors first rather than masking them with heartbeat increases.

Current compiler frontier: exit={baseline.returncode}, first={baseline.first_line}:{baseline.first_col}, visible_errors={baseline.error_count}.

{context}
""".strip()


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--cycle", type=int, required=True)
    parser.add_argument("--timeout-seconds", type=int, default=3300)
    args = parser.parse_args()

    LOG_ROOT.mkdir(parents=True, exist_ok=True)
    paths = core.target_paths()
    baseline_manifest = core.ensure_baseline(paths)
    state = load_state()
    target = active_target(state, paths)
    relative = str(target.relative_to(ROOT))
    snapshot = baseline_manifest[relative]
    valid, reason = core.validate_against_snapshot(target, snapshot)
    if not valid:
        raise RuntimeError(f"pre-Aider trust gate failed: {reason}")

    baseline = core.compile_target(
        target,
        f"aider-{target.stem}-cycle-{args.cycle:02d}-baseline",
        max_errors=16,
        timeout=1800,
    )
    if baseline.passed:
        print(f"[pass376-aider] {relative} already compiles; handing back to ordered verifier")
        return 0

    before = target.read_bytes()
    before_tracked = set(
        line.strip()
        for line in subprocess.run(
            ["git", "diff", "--name-only"],
            cwd=ROOT,
            text=True,
            stdout=subprocess.PIPE,
            check=True,
        ).stdout.splitlines()
        if line.strip()
    )
    test_command = f"lake env lean -DmaxErrors=16 {relative}"
    prompt_path = LOG_ROOT / f"cycle-{args.cycle:02d}-{target.stem}-prompt.txt"
    prompt = build_prompt(target, baseline)
    prompt_path.write_text(prompt, encoding="utf-8")
    console_path = LOG_ROOT / f"cycle-{args.cycle:02d}-{target.stem}-console.log"

    model_candidates = [
        os.environ.get("PASS376_AIDER_MODEL", "openai/openai/gpt-4.1"),
        "openai/openai/gpt-5-mini",
        "openai/openai/gpt-4o",
    ]
    aider_ok = False
    for model in model_candidates:
        command = [
            "aider",
            "--model",
            model,
            "--yes-always",
            "--no-auto-commits",
            "--no-gitignore",
            "--no-check-update",
            "--no-show-model-warnings",
            "--edit-format",
            "diff",
            "--test-cmd",
            test_command,
            "--auto-test",
            "--message",
            prompt,
            relative,
        ]
        environment = os.environ.copy()
        environment.setdefault("OPENAI_API_KEY", environment.get("GITHUB_TOKEN", ""))
        environment.setdefault("OPENAI_API_BASE", "https://models.github.ai/inference")
        started = time.monotonic()
        try:
            process = subprocess.run(
                command,
                cwd=ROOT,
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                timeout=args.timeout_seconds,
                env=environment,
            )
            output = process.stdout
            returncode = process.returncode
        except subprocess.TimeoutExpired as exc:
            output = (exc.stdout or "") + "\n[pass376-aider] timeout\n"
            returncode = 124
        with console_path.open("a", encoding="utf-8") as handle:
            handle.write(
                f"\n===== model={model} rc={returncode} elapsed={time.monotonic()-started:.2f}s =====\n"
            )
            handle.write(output)
        if target.read_bytes() != before:
            aider_ok = True
            break

    for generated in (ROOT / ".aider.chat.history.md", ROOT / ".aider.input.history"):
        generated.unlink(missing_ok=True)

    if not aider_ok:
        target.write_bytes(before)
        print("[pass376-aider] no model produced a source edit")
        return 2

    changed_tracked = set(
        line.strip()
        for line in subprocess.run(
            ["git", "diff", "--name-only"],
            cwd=ROOT,
            text=True,
            stdout=subprocess.PIPE,
            check=True,
        ).stdout.splitlines()
        if line.strip()
    )
    newly_changed = changed_tracked - before_tracked
    if newly_changed - {relative}:
        target.write_bytes(before)
        for changed in sorted(newly_changed - {relative}):
            subprocess.run(["git", "checkout", "--", changed], cwd=ROOT, check=False)
        print(f"[pass376-aider] rejected edits outside target: {sorted(newly_changed)}")
        return 2

    valid, reason = core.validate_against_snapshot(target, snapshot)
    if not valid:
        target.write_bytes(before)
        print(f"[pass376-aider] rejected by trust gate: {reason}")
        return 2

    candidate = core.compile_target(
        target,
        f"aider-{target.stem}-cycle-{args.cycle:02d}-candidate",
        max_errors=16,
        timeout=1800,
    )
    if not candidate.passed and reduction_key(candidate) <= reduction_key(baseline):
        target.write_bytes(before)
        print(
            "[pass376-aider] rejected non-advancing candidate: "
            f"baseline={reduction_key(baseline)} candidate={reduction_key(candidate)}"
        )
        return 2

    state.setdefault("history", []).append(
        {
            "cycle": args.cycle,
            "target": relative,
            "event": "aider-repair",
            "accepted": True,
            "before_sha256": core.sha256_bytes(before),
            "after_sha256": core.sha256_file(target),
            "baseline": core.result_payload(baseline),
            "candidate": core.result_payload(candidate),
        }
    )
    state["active_target"] = relative
    state["success"] = False
    core.invalidate_from(state, paths, paths.index(target))
    core.write_json(STATE_PATH, state)
    print(
        f"[pass376-aider] accepted {relative}: "
        f"first={candidate.first_line}:{candidate.first_col} errors={candidate.error_count}"
    )
    return 0 if candidate.passed else 2


if __name__ == "__main__":
    raise SystemExit(main())
