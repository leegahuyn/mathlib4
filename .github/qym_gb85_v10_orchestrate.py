#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import time

ERROR_RE = re.compile(r"(?m)^(?P<file>[^\n]*\.lean):(?P<line>\d+):(?P<col>\d+): error: ?(?P<msg>.*)$")
PANIC_RE = re.compile(r"(?im)^.*(?:panic|internal compiler error|internal error).*$")
FORBIDDEN = {
    "sorry": re.compile(r"\bsorry\b"),
    "admit": re.compile(r"\badmit\b"),
    "native_decide": re.compile(r"\bnative_decide\b"),
    "Lean.ofReduceBool": re.compile(r"Lean\.ofReduceBool"),
    "global_axiom": re.compile(r"(?m)^\s*axiom\s+"),
    "unsafe": re.compile(r"(?m)^\s*unsafe\s+"),
    "maxHeartbeats_zero": re.compile(r"set_option\s+maxHeartbeats\s+0\b"),
}
STAGES = [
    ("C3", ["using_bang_explicit_constants"]),
    ("C5", ["derive_and_normsq", "derive_and_star", "coordinate_star"]),
    ("C6", ["helper_letI", "inline_letI"]),
]


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git_blob(path: Path) -> str:
    raw = path.read_bytes()
    return hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest()


def forbidden(path: Path) -> dict[str, int]:
    text = path.read_text(encoding="utf-8")
    return {name: len(regex.findall(text)) for name, regex in FORBIDDEN.items()}


def metrics(log: Path, exit_code: int, source: Path) -> dict:
    text = log.read_text(encoding="utf-8", errors="replace")
    errors = [m.groupdict() for m in ERROR_RE.finditer(text)]
    first = None
    if errors:
        first = {
            "file": errors[0]["file"],
            "line": int(errors[0]["line"]),
            "col": int(errors[0]["col"]),
            "message": errors[0]["msg"].strip(),
        }
    return {
        "lean_exit": exit_code,
        "error_headers": len(errors),
        "panic_lines": len(PANIC_RE.findall(text)),
        "first_error": first,
        "normalized_signatures": sorted({e["msg"].strip() for e in errors}),
        "candidate_qym_sha256": sha256(source),
        "candidate_qym_blob": git_blob(source),
        "forbidden": forbidden(source),
        "log_sha256": hashlib.sha256(log.read_bytes()).hexdigest(),
    }


def rank(value: dict) -> tuple:
    first = value.get("first_error")
    first_line = int(first["line"]) if first else 10**12
    return (
        int(value.get("panic_lines", 10**9)),
        int(value.get("error_headers", 10**9)),
        -first_line,
        len(value.get("normalized_signatures", [])),
    )


def strictly_better(candidate: dict, current: dict) -> bool:
    if int(candidate.get("panic_lines", 1)) != 0:
        return False
    if any(int(v) != 0 for v in candidate.get("forbidden", {}).values()):
        return False
    return rank(candidate) < rank(current)


def patch_constraints(script_text: str, source: Path) -> str:
    source_sha = sha256(source)
    source_blob = git_blob(source)
    patterns = [
        (re.compile(r"(?im)([A-Z0-9_]*(?:BASE|SOURCE|INPUT)[A-Z0-9_]*SHA256[A-Z0-9_]*\s*(?::[^=\n]+)?=\s*[\"'])([0-9a-f]{64})([\"'])"), source_sha),
        (re.compile(r"(?im)([A-Z0-9_]*(?:BASE|SOURCE|INPUT)[A-Z0-9_]*(?:BLOB|GIT_BLOB)[A-Z0-9_]*\s*(?::[^=\n]+)?=\s*[\"'])([0-9a-f]{40})([\"'])"), source_blob),
    ]
    result = script_text
    for regex, replacement in patterns:
        result = regex.sub(lambda m: m.group(1) + replacement + m.group(3), result)
    known_sha = {
        "830563b33d873354809594d9e9dce962c1253052f8e70bd4d1513226f7598217",
        "f4c9b27a297be772cde7183526378ad42ae826053f69cf3ce521670da4f06210",
    }
    known_blob = {
        "e796aa6ae9f01965116902a9345ed69f81bcfc42",
        "bd28d0436230a8f0bcb01806dac01787542256b8",
    }
    for old in known_sha:
        result = result.replace(old, source_sha)
    for old in known_blob:
        result = result.replace(old, source_blob)
    return result


def discover(repo: Path, variant: str) -> list[Path]:
    result: list[Path] = []
    for path in (repo / ".github").rglob("*.py"):
        if path.name == Path(__file__).name:
            continue
        try:
            text = path.read_text(encoding="utf-8")
        except Exception:
            continue
        if variant in text:
            result.append(path)
    return sorted(result, key=lambda p: ("patch" not in p.name.lower(), len(str(p)), str(p)))


def try_patcher(repo: Path, script: Path, variant: str, source: Path, out_dir: Path) -> tuple[Path | None, dict]:
    attempts: list[dict] = []
    script_text = patch_constraints(script.read_text(encoding="utf-8"), source)
    patched_script = out_dir / "patched_patcher.py"
    patched_script.write_text(script_text, encoding="utf-8")
    arg_patterns = [
        [variant, "{input}", "{output}"],
        ["{input}", "{output}", variant],
        ["--variant", variant, "--input", "{input}", "--output", "{output}"],
        ["--input", "{input}", "--output", "{output}", "--variant", variant],
        [variant, "--input", "{input}", "--output", "{output}"],
        ["--variant", variant, "{input}", "{output}"],
    ]
    for index, pattern in enumerate(arg_patterns):
        attempt_dir = out_dir / f"invoke-{index}"
        attempt_dir.mkdir(parents=True, exist_ok=True)
        attempt_input = attempt_dir / "QYM.input.lean"
        attempt_output = attempt_dir / "QYM.output.lean"
        shutil.copy2(source, attempt_input)
        args = [str(patched_script)] + [
            str(attempt_input) if x == "{input}" else str(attempt_output) if x == "{output}" else x
            for x in pattern
        ]
        proc = subprocess.run(
            [sys.executable, *args],
            cwd=repo,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=180,
        )
        (attempt_dir / "patcher.log").write_text(proc.stdout, encoding="utf-8")
        candidate: Path | None = None
        if attempt_output.exists() and attempt_output.stat().st_size > 0:
            candidate = attempt_output
        elif attempt_input.exists() and sha256(attempt_input) != sha256(source):
            candidate = attempt_input
        valid = False
        reason = "no candidate"
        if candidate is not None:
            if sha256(candidate) == sha256(source):
                reason = "unchanged"
            elif forbidden(candidate) != forbidden(source):
                reason = "forbidden delta"
            elif candidate.read_text(encoding="utf-8").count("\n") < 1000:
                reason = "implausibly short"
            else:
                valid = True
                reason = "candidate generated"
        attempts.append({
            "args": args,
            "exit": proc.returncode,
            "candidate": str(candidate) if candidate else None,
            "valid": valid,
            "reason": reason,
        })
        if valid and candidate is not None:
            final = out_dir / "QYM.lean"
            shutil.copy2(candidate, final)
            return final, {"script": str(script), "attempts": attempts}
    return None, {"script": str(script), "attempts": attempts}


def compile_candidate(repo: Path, candidate: Path, log: Path) -> dict:
    env = os.environ.copy()
    env["LEAN_ABORT_ON_PANIC"] = "1"
    started = time.time()
    with log.open("wb") as handle:
        proc = subprocess.run(
            ["timeout", "10800", "lake", "env", "lean", "-DmaxErrors=2000", str(candidate)],
            cwd=repo,
            env=env,
            stdout=handle,
            stderr=subprocess.STDOUT,
        )
    value = metrics(log, proc.returncode, candidate)
    value["wall_seconds"] = round(time.time() - started, 3)
    return value


def main() -> None:
    if len(sys.argv) != 6:
        raise SystemExit("usage: orchestrate.py REPO SOURCE CURRENT_FRONTIER OUT FINAL_SOURCE")
    repo = Path(sys.argv[1]).resolve()
    original = Path(sys.argv[2]).resolve()
    frontier_path = Path(sys.argv[3]).resolve()
    out = Path(sys.argv[4]).resolve()
    final_source = Path(sys.argv[5]).resolve()
    out.mkdir(parents=True, exist_ok=True)

    current_source = out / "current" / "QYM.lean"
    current_source.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(original, current_source)
    current = json.loads(frontier_path.read_text(encoding="utf-8"))
    current.update({
        "candidate_qym_sha256": sha256(current_source),
        "candidate_qym_blob": git_blob(current_source),
        "forbidden": forbidden(current_source),
    })
    starting = dict(current)
    report: dict = {
        "schema": "qym-gb85-v10-cumulative-existing-patch-tournament",
        "starting_frontier": starting,
        "stages": [],
    }

    for stage, variants in STAGES:
        stage_record: dict = {"stage": stage, "starting": current, "attempts": []}
        valid_rows: list[tuple[dict, Path]] = []
        for variant in variants:
            scripts = discover(repo, variant)
            variant_record: dict = {"variant": variant, "discovered_scripts": [str(p) for p in scripts], "patch_attempts": []}
            for script_index, script in enumerate(scripts):
                candidate_dir = out / stage / variant / f"script-{script_index}"
                candidate_dir.mkdir(parents=True, exist_ok=True)
                candidate, patch_meta = try_patcher(repo, script, variant, current_source, candidate_dir)
                variant_record["patch_attempts"].append(patch_meta)
                if candidate is None:
                    continue
                lean_metrics = compile_candidate(repo, candidate, candidate_dir / "full.log")
                lean_metrics.update({
                    "stage": stage,
                    "variant": variant,
                    "script": str(script),
                    "candidate": str(candidate),
                    "strict_improvement": strictly_better(lean_metrics, current),
                })
                (candidate_dir / "full.json").write_text(json.dumps(lean_metrics, indent=2, sort_keys=True) + "\n", encoding="utf-8")
                variant_record.setdefault("compiled", []).append(lean_metrics)
                if lean_metrics["strict_improvement"]:
                    valid_rows.append((lean_metrics, candidate))
            stage_record["attempts"].append(variant_record)
        if valid_rows:
            valid_rows.sort(key=lambda row: rank(row[0]))
            best_metrics, best_source = valid_rows[0]
            shutil.copy2(best_source, current_source)
            current = best_metrics
            stage_record["winner"] = best_metrics
        else:
            stage_record["winner"] = None
        stage_record["ending"] = current
        report["stages"].append(stage_record)

    overall = strictly_better(current, starting)
    report.update({
        "ending_frontier": current,
        "strict_improvement": overall,
        "starting_sha256": sha256(original),
        "ending_sha256": sha256(current_source),
    })
    Path(out / "RESULT.json").write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    final_source.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(current_source, final_source)
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
