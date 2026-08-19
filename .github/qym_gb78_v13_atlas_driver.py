#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import collections, hashlib, json, os, re, shutil, subprocess, sys

QYM = Path(os.environ.get("QYM", "PrimalitySheafVerification/QYM.lean"))
NORMAL_OUT = Path(os.environ.get("NORMAL_OUT", "/tmp/qym-gb78-v13/normal"))
OUT = Path(os.environ.get("ATLAS_OUT", "/tmp/qym-gb78-v13/atlas"))
PATCHER = Path(".github/qym_gb78_v13_atlas_patch.py")
VARIANTS = ("private_helpers", "direct_letI")

DIAG = re.compile(r"^(?P<file>.*?\.lean):(?P<line>\d+):(?P<column>\d+): (?P<severity>error|warning)(?:\((?P<code>[^)]*)\))?:\s*(?P<message>.*)$", re.M)
PANIC = re.compile(r"(?im)^.*(?:internal error|uncaught exception|panic(?:!|:|\s)).*$")

def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()

def blob(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()

def dump(path: Path, value) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")

def compile_candidate(candidate: Path, variant: str, phase: str, max_errors: int):
    shutil.copy2(candidate, QYM)
    log = OUT / f"{variant}.{phase}.log"
    olean = OUT / f"{variant}.{phase}.olean"
    ilean = OUT / f"{variant}.{phase}.ilean"
    cmd = ["lake", "env", "lean", f"-DmaxErrors={max_errors}", "-DwarningAsError=false",
           "-o", str(olean), "-i", str(ilean), str(QYM)]
    with log.open("wb") as handle:
        proc = subprocess.run(cmd, stdout=handle, stderr=subprocess.STDOUT)
    text = log.read_text(errors="replace")
    rows = []
    for m in DIAG.finditer(text):
        row = m.groupdict()
        row["line"] = int(row["line"])
        row["column"] = int(row["column"])
        rows.append(row)
    errors = [r for r in rows if r["severity"] == "error"]
    warnings = [r for r in rows if r["severity"] == "warning"]
    result = {
        "variant": variant,
        "phase": phase,
        "exit": proc.returncode,
        "error_headers": len(errors),
        "warning_headers": len(warnings),
        "panic_lines": len(PANIC.findall(text)),
        "first_error": errors[0] if errors else None,
        "last_error": errors[-1] if errors else None,
        "error_codes": dict(sorted(collections.Counter((r.get("code") or "uncoded") for r in errors).items())),
        "log_sha256": sha(log.read_bytes()),
        "candidate_qym_sha256": sha(candidate.read_bytes()),
        "candidate_qym_blob": blob(candidate.read_bytes()),
        "olean_exists": olean.is_file() and olean.stat().st_size > 0,
        "ilean_exists": ilean.is_file() and ilean.stat().st_size > 0,
    }
    dump(OUT / f"{variant}.{phase}.json", result)
    return result

def main() -> int:
    OUT.mkdir(parents=True, exist_ok=True)
    normal_source = NORMAL_OUT / "QYM.best.lean"
    normal_result_path = NORMAL_OUT / "BEST_RESULT.json"
    if not normal_source.is_file() or not normal_result_path.is_file():
        raise SystemExit("normal-stage best source/result missing")
    normal_result = json.loads(normal_result_path.read_text())
    normal_errors = int(normal_result["error_headers"])
    if int(normal_result["panic_lines"]) != 0 or normal_errors >= 78:
        raise SystemExit(f"normal stage is not a strict GB78 improvement: {normal_result}")
    if sha(normal_source.read_bytes()) != normal_result["candidate_qym_sha256"]:
        raise SystemExit("normal source SHA mismatch")
    if blob(normal_source.read_bytes()) != normal_result["candidate_qym_blob"]:
        raise SystemExit("normal source blob mismatch")

    original = OUT / "QYM.checked-in.lean"
    shutil.copy2(QYM, original)
    rows = []
    try:
        for variant in VARIANTS:
            candidate = OUT / f"QYM.candidate-{variant}.lean"
            shutil.copy2(normal_source, candidate)
            patch_path = OUT / f"{variant}.PATCH_RESULT.json"
            with patch_path.open("wb") as handle:
                subprocess.run([sys.executable, "-B", str(PATCHER), variant, str(candidate)], check=True, stdout=handle)
            patch = json.loads(patch_path.read_text())
            if patch["candidate_sha256"] != sha(candidate.read_bytes()) or patch["candidate_blob"] != blob(candidate.read_bytes()):
                raise RuntimeError(f"{variant}: patch digest mismatch")
            local = compile_candidate(candidate, variant, "local", 1)
            first = local.get("first_error") or {}
            first_line = int(first.get("line") or 10**9)
            gate_line = int(patch["gate_line"])
            local_pass = int(local["panic_lines"]) == 0 and first_line >= gate_line
            row = {
                "variant": variant,
                "candidate": str(candidate),
                "patch": patch,
                "local": local,
                "local_gate_pass": local_pass,
            }
            rows.append(row)
            if not local_pass:
                continue
            full = compile_candidate(candidate, variant, "full", 10000)
            semantic = (int(full["exit"]) == 0 and int(full["error_headers"]) == 0 and
                        int(full["panic_lines"]) == 0 and bool(full["olean_exists"]) and bool(full["ilean_exists"]))
            strict = semantic or (int(full["panic_lines"]) == 0 and int(full["error_headers"]) < normal_errors)
            full.update({
                "semantic_pass": semantic,
                "strict_improvement": strict,
                "baseline_error_headers": normal_errors,
                "baseline_qym_sha256": normal_result["candidate_qym_sha256"],
                "baseline_qym_blob": normal_result["candidate_qym_blob"],
                "run_id": os.environ.get("GITHUB_RUN_ID"),
                "trigger_sha": os.environ.get("GITHUB_SHA"),
            })
            dump(OUT / f"{variant}.FULL_RESULT.json", full)
            row["full"] = full

        improved = [r for r in rows if (r.get("full") or {}).get("strict_improvement")]
        selection = {
            "schema": "qym-gb78-v13-normal-atlas-selection-v1",
            "normal_baseline": normal_result,
            "candidates": rows,
            "atlas_strict_improvement_found": bool(improved),
        }
        if improved:
            improved.sort(key=lambda r: (
                int(r["full"]["error_headers"]),
                int(r["full"]["panic_lines"]),
                -int(((r["full"].get("first_error") or {}).get("line") or 0)),
                r["variant"],
            ))
            best = improved[0]
            selection["best_variant"] = best["variant"]
            selection["best"] = best["full"]
            shutil.copy2(Path(best["candidate"]), OUT / "FINAL_QYM.lean")
            final = dict(best["full"])
            final["atlas_improved"] = True
        else:
            shutil.copy2(normal_source, OUT / "FINAL_QYM.lean")
            final = dict(normal_result)
            final["atlas_improved"] = False
            final["origin"] = "normal_only"
        final["candidate_qym_sha256"] = sha((OUT / "FINAL_QYM.lean").read_bytes())
        final["candidate_qym_blob"] = blob((OUT / "FINAL_QYM.lean").read_bytes())
        dump(OUT / "FINAL_RESULT.json", final)
        dump(OUT / "ATLAS_SELECTION.json", selection)
        return 0
    finally:
        shutil.copy2(original, QYM)

if __name__ == "__main__":
    raise SystemExit(main())
