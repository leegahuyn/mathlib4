from __future__ import annotations

import json
import os
import shutil
import subprocess
import sys
from pathlib import Path
from typing import Any

from fa442_pipeline_common import (
    FA_PATH,
    MOCK2_ADV_PATH,
    MOCK2_PATH,
    REPO,
    append_github_output,
    audit_clean,
    error_header_count,
    exact_command,
    parse_first_error,
    read_json,
    source_metadata,
    write_json,
)

VARIANT = os.environ["VARIANT"]
SLUG = os.environ["VARIANT_SLUG"]
EXPECTED_SHA = os.environ["EXPECTED_SHA256"]
IS_BASELINE = os.environ.get("IS_BASELINE", "false").lower() == "true"
CURRENT_BASELINE_SHA = os.environ["CURRENT_BASELINE_SHA"]
MAX_ERRORS = int(os.environ.get("FA_MAX_ERRORS", "2000"))
BUNDLE_ROOT = Path(os.environ["CANDIDATE_BUNDLE_ROOT"])
BASELINE_META_PATH = Path(os.environ["BASELINE_META_PATH"])
RESULT_ROOT = Path(os.environ.get(
    "FA443_RESULT_ROOT",
    REPO / "build-logs/fa443-blocker-tournament/direct-metrics",
))
RESULT = RESULT_ROOT / SLUG
LEAN_INSTALL_MARKER = Path(os.environ.get("LEAN_INSTALL_MARKER", "/tmp/fa443-lean-install-ok"))


def compile_one(stem: str, source: Path, max_errors: int) -> dict[str, Any]:
    output_dir = REPO / ".lake/build/lib/lean/PrimalitySheafVerification"
    output_dir.mkdir(parents=True, exist_ok=True)
    olean = output_dir / f"{stem}.olean"
    ilean = output_dir / f"{stem}.ilean"
    olean.unlink(missing_ok=True)
    ilean.unlink(missing_ok=True)
    command = [
        "lake", "env", "lean", "-DwarningAsError=false", f"-DmaxErrors={max_errors}",
        "-o", str(olean), "-i", str(ilean), str(source.relative_to(REPO)),
    ]
    log_path = RESULT / f"{stem}.log"
    with log_path.open("wb") as log:
        cp = subprocess.run(command, cwd=REPO, stdout=log, stderr=subprocess.STDOUT, check=False)
    return {
        "command": exact_command(command),
        "max_errors": max_errors,
        "exit_code": cp.returncode,
        "olean_exists": olean.exists() and olean.stat().st_size > 0,
        "ilean_exists": ilean.exists() and ilean.stat().st_size > 0,
        "log": str(log_path.relative_to(RESULT)),
    }


def main() -> int:
    if RESULT.exists():
        shutil.rmtree(RESULT)
    RESULT.mkdir(parents=True)
    metric: dict[str, Any]
    source_meta: dict[str, Any] = {}
    try:
        if not LEAN_INSTALL_MARKER.exists():
            raise RuntimeError("Lean setup marker missing")
        source_path = BUNDLE_ROOT / SLUG / "source.lean"
        metadata_path = BUNDLE_ROOT / SLUG / "metadata.json"
        if not source_path.exists() or not metadata_path.exists():
            raise RuntimeError("candidate bundle missing source/metadata")
        bundle_meta = read_json(metadata_path)
        if bundle_meta.get("sha256") != EXPECTED_SHA:
            raise RuntimeError("bundle metadata SHA mismatch")
        baseline_meta = read_json(BASELINE_META_PATH)
        if baseline_meta.get("sha256") != CURRENT_BASELINE_SHA:
            raise RuntimeError("current baseline metadata SHA mismatch")
        shutil.copy2(source_path, FA_PATH)
        source_meta = source_metadata(FA_PATH.read_bytes())
        source_meta.update({
            "expected_sha256": EXPECTED_SHA,
            "sha_identity_ok": source_meta["sha256"] == EXPECTED_SHA,
            "same_height": source_meta["line_count"] == baseline_meta["line_count"],
            "header_unchanged": (
                source_meta["blocker_header_sha256"] == baseline_meta["blocker_header_sha256"] and
                source_meta["blocker_header"] == baseline_meta["blocker_header"]
            ),
            "declaration_sequence_unchanged": (
                source_meta["declaration_sequence_sha256"] == baseline_meta["declaration_sequence_sha256"]
            ),
            "trust_audit_clean": audit_clean(source_meta["trust_audit"]),
        })
        if not all(source_meta[k] for k in (
            "sha_identity_ok", "same_height", "header_unchanged",
            "declaration_sequence_unchanged", "trust_audit_clean",
        )):
            raise RuntimeError(f"candidate integrity/trust failure: {source_meta}")
        if IS_BASELINE and source_meta["sha256"] != CURRENT_BASELINE_SHA:
            raise RuntimeError("FA443 baseline matrix entry does not equal current baseline")
        shutil.copy2(FA_PATH, RESULT / "source.lean")
        write_json(RESULT / "source-metadata.json", source_meta)

        m2 = compile_one("Mock2", MOCK2_PATH, 400)
        m2a = compile_one("Mock2_Advanced", MOCK2_ADV_PATH, 400)
        prereq_ok = all(
            x["exit_code"] == 0 and x["olean_exists"] and x["ilean_exists"]
            for x in (m2, m2a)
        )
        if not prereq_ok:
            raise RuntimeError("Mock2 or Mock2_Advanced direct regression compile failed")
        fa = compile_one("Mock2_FunctionalAnalysis", FA_PATH, MAX_ERRORS)
        log = (RESULT / "Mock2_FunctionalAnalysis.log").read_text(
            encoding="utf-8", errors="replace"
        )
        first = parse_first_error(log, FA_PATH.read_text(encoding="utf-8"))
        fa.update({
            "first_error": first,
            "error_header_count": error_header_count(log),
            "error_header_count_interpretation": (
                "captured diagnostics before maxErrors termination; not total errors/progress"
            ),
        })
        metric = {
            "variant": VARIANT,
            "slug": SLUG,
            "is_baseline": IS_BASELINE,
            "classification": "FA_PASS_CANDIDATE" if fa["exit_code"] == 0 else "LEAN_FAILURE",
            "direct_lean_executed": True,
            "current_baseline_sha256": CURRENT_BASELINE_SHA,
            "source": source_meta,
            "prerequisites": {"Mock2": m2, "Mock2_Advanced": m2a},
            "fa": fa,
            "lean_version": Path("/tmp/fa443-lean-version.txt").read_text(
                errors="replace").strip() if Path("/tmp/fa443-lean-version.txt").exists() else "",
            "lake_version": Path("/tmp/fa443-lake-version.txt").read_text(
                errors="replace").strip() if Path("/tmp/fa443-lake-version.txt").exists() else "",
            "repository_head": subprocess.run(
                ["git", "rev-parse", "HEAD"], cwd=REPO,
                stdout=subprocess.PIPE, text=True, check=True,
            ).stdout.strip(),
            "authority": "direct lake env lean CLI in FA443 sequential tournament",
        }
    except Exception as exc:
        metric = {
            "variant": VARIANT,
            "slug": SLUG,
            "is_baseline": IS_BASELINE,
            "classification": "INFRA_FAILURE",
            "direct_lean_executed": False,
            "current_baseline_sha256": CURRENT_BASELINE_SHA,
            "source": source_meta,
            "prerequisites": {},
            "fa": {},
            "error": repr(exc),
        }
    write_json(RESULT / "metric.json", metric)
    append_github_output(
        classification=metric["classification"],
        lean_executed=metric.get("direct_lean_executed", False),
        source_sha=metric.get("source", {}).get("sha256", ""),
        fa_exit=metric.get("fa", {}).get("exit_code", 999),
        first_line=metric.get("fa", {}).get("first_error", {}).get("line", 0),
        first_col=metric.get("fa", {}).get("first_error", {}).get("column", 0),
    )
    print(json.dumps(metric, indent=2, ensure_ascii=False))
    return 1 if metric["classification"] == "INFRA_FAILURE" else 0


if __name__ == "__main__":
    sys.exit(main())
