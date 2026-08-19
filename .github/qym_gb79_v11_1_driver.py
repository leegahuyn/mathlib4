#!/usr/bin/env python3
from pathlib import Path
import collections, hashlib, json, os, re, shutil, subprocess, sys

QYM = Path("PrimalitySheafVerification/QYM.lean")
PATCHER = Path(".github/qym_patch_gb79_v11_1.py")
OUT = Path("/tmp/qym-gb79-v11-1")
BASE_SHA256 = "790b40c05a8f3735dd171a135eda65de92ab68b247d13e7e2ffe2968e3798421"
BASE_BLOB = "33e4fab1130e4c17ea5d212fe2691c3e0c0eb8d3"
BASE_ERRORS = 79
VARIANTS = ("edge_only", "edge_re", "edge_both")
DIAG = re.compile(r"^(?P<file>.*?\.lean):(?P<line>\d+):(?P<column>\d+): (?P<severity>error|warning)(?:\((?P<code>[^)]*)\))?:\s*(?P<message>.*)$", re.M)
PANIC = re.compile(r"(?im)^.*(?:internal error|uncaught exception|panic(?:!|:|\s)).*$")

def sha256(b): return hashlib.sha256(b).hexdigest()
def blob(b): return hashlib.sha1(b"blob " + str(len(b)).encode() + b"\0" + b).hexdigest()
def dump(path, value): Path(path).write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")

def compile_candidate(src, variant, phase, max_errors):
    shutil.copy2(src, QYM)
    log = OUT / f"{variant}.{phase}.log"
    olean = OUT / f"{variant}.{phase}.olean"
    ilean = OUT / f"{variant}.{phase}.ilean"
    cmd = ["lake", "env", "lean", f"-DmaxErrors={max_errors}", "-DwarningAsError=false",
           "-o", str(olean), "-i", str(ilean), str(QYM)]
    with log.open("wb") as h:
        proc = subprocess.run(cmd, stdout=h, stderr=subprocess.STDOUT)
    text = log.read_text(errors="replace")
    rows = []
    for m in DIAG.finditer(text):
        d = m.groupdict(); d["line"] = int(d["line"]); d["column"] = int(d["column"]); rows.append(d)
    errors = [x for x in rows if x["severity"] == "error"]
    warnings = [x for x in rows if x["severity"] == "warning"]
    result = {
        "variant": variant, "phase": phase, "exit": proc.returncode,
        "error_headers": len(errors), "warning_headers": len(warnings),
        "panic_lines": len(PANIC.findall(text)),
        "first_error": errors[0] if errors else None,
        "last_error": errors[-1] if errors else None,
        "error_codes": dict(sorted(collections.Counter((x.get("code") or "uncoded") for x in errors).items())),
        "log_sha256": sha256(log.read_bytes()),
        "candidate_qym_sha256": sha256(Path(src).read_bytes()),
        "candidate_qym_blob": blob(Path(src).read_bytes()),
        "olean_exists": olean.is_file() and olean.stat().st_size > 0,
        "ilean_exists": ilean.is_file() and ilean.stat().st_size > 0,
    }
    dump(OUT / f"{variant}.{phase}.json", result)
    return result

def main():
    OUT.mkdir(parents=True, exist_ok=True)
    original = OUT / "QYM.GB79.lean"
    shutil.copy2(QYM, original)
    raw = original.read_bytes()
    check = {"sha_ok": sha256(raw) == BASE_SHA256, "blob_ok": blob(raw) == BASE_BLOB,
             "sha256": sha256(raw), "blob": blob(raw), "error_headers": BASE_ERRORS}
    dump(OUT / "BASELINE_CHECK.json", check)
    if not check["sha_ok"] or not check["blob_ok"]:
        raise SystemExit(f"GB79 authority mismatch: {check}")
    rows = []
    try:
        for variant in VARIANTS:
            cand = OUT / f"QYM.candidate-{variant}.lean"
            shutil.copy2(original, cand)
            patch_path = OUT / f"{variant}.PATCH_RESULT.json"
            with patch_path.open("wb") as h:
                subprocess.run([sys.executable, "-B", str(PATCHER), variant, str(cand)], check=True, stdout=h)
            patch = json.loads(patch_path.read_text())
            local = compile_candidate(cand, variant, "local", 1)
            first = local.get("first_error") or {}
            first_line = int(first.get("line") or 10**9)
            gate = int(patch["gate_line"])
            gate_pass = int(local["panic_lines"]) == 0 and first_line >= gate
            local["gate_line"] = gate
            local["gate_pass"] = gate_pass
            dump(OUT / f"{variant}.LOCAL_RESULT.json", local)
            row = {"variant": variant, "candidate": str(cand), "patch": patch,
                   "local": local, "local_gate_pass": gate_pass}
            rows.append(row)
            if not gate_pass:
                continue
            full = compile_candidate(cand, variant, "full", 10000)
            semantic = (int(full["exit"]) == 0 and int(full["error_headers"]) == 0 and
                        int(full["panic_lines"]) == 0 and full["olean_exists"] and full["ilean_exists"])
            strict = semantic or (int(full["panic_lines"]) == 0 and int(full["error_headers"]) < BASE_ERRORS)
            full.update({
                "semantic_pass": semantic, "strict_improvement": strict,
                "baseline_error_headers": BASE_ERRORS,
                "baseline_qym_sha256": BASE_SHA256, "baseline_qym_blob": BASE_BLOB,
                "run_id": os.environ.get("GITHUB_RUN_ID"), "trigger_sha": os.environ.get("GITHUB_SHA"),
            })
            dump(OUT / f"{variant}.FULL_RESULT.json", full)
            row["full"] = full
        improved = [r for r in rows if r.get("full", {}).get("strict_improvement")]
        selection = {"schema": "qym-gb79-v11-1-selection-v1", "baseline": check,
                     "candidates": rows, "strict_improvement_found": bool(improved)}
        if improved:
            improved.sort(key=lambda r: (int(r["full"]["error_headers"]), int(r["full"]["panic_lines"]),
                                         -int((r["full"].get("first_error") or {}).get("line") or 10**9), r["variant"]))
            best = improved[0]
            selection["best_variant"] = best["variant"]
            selection["best"] = best["full"]
            shutil.copy2(best["candidate"], OUT / "QYM.best.lean")
            dump(OUT / "BEST_RESULT.json", best["full"])
            dump(OUT / "SELECTION.json", selection)
            return 0
        dump(OUT / "SELECTION.json", selection)
        return 2
    finally:
        shutil.copy2(original, QYM)

if __name__ == "__main__":
    raise SystemExit(main())
