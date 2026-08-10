from __future__ import annotations

import json
import os
import shutil
import subprocess
import sys
from pathlib import Path
from typing import Any

from fa442_pipeline_common import (
    BASELINE_LINE_COUNT,
    BASELINE_SHA256,
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
    sha256_file,
    source_metadata,
    trust_audit,
    write_json,
)

VARIANT = os.environ["VARIANT"]
SLUG = os.environ["VARIANT_SLUG"]
EXPECTED_SHA = os.environ["EXPECTED_SHA256"]
IS_BASELINE = os.environ.get("IS_BASELINE", "false").lower() == "true"
MAX_ERRORS = int(os.environ.get("FA_MAX_ERRORS", "2000"))
BUNDLE_ROOT = Path(os.environ.get(
    "CANDIDATE_BUNDLE_ROOT",
    REPO / "build-logs/fa442-pipeline-repair/prep-download/candidate-bundle",
))
BASELINE_META_PATH = Path(os.environ.get(
    "BASELINE_META_PATH",
    REPO / "build-logs/fa442-pipeline-repair/prep-download/baseline-meta.json",
))
RESULT = REPO / "build-logs/fa442-pipeline-repair/matrix-results" / SLUG
LEAN_INSTALL_MARKER = Path(os.environ.get("LEAN_INSTALL_MARKER", "/tmp/fa442-lean-install-ok"))


def compile_one(stem: str, source: Path, max_errors: int) -> dict[str, Any]:
    output_dir = REPO / ".lake/build/lib/lean/PrimalitySheafVerification"
    output_dir.mkdir(parents=True, exist_ok=True)
    olean = output_dir / f"{stem}.olean"
    ilean = output_dir / f"{stem}.ilean"
    olean.unlink(missing_ok=True)
    ilean.unlink(missing_ok=True)
    command = [
        "lake", "env", "lean",
        "-DwarningAsError=false",
        f"-DmaxErrors={max_errors}",
        "-o", str(olean),
        "-i", str(ilean),
        str(source.relative_to(REPO)),
    ]
    log_path = RESULT / f"{stem}.log"
    with log_path.open("wb") as log:
        cp = subprocess.run(
            command,
            cwd=REPO,
            stdout=log,
            stderr=subprocess.STDOUT,
            check=False,
        )
    return {
        "stem": stem,
        "command": exact_command(command),
        "max_errors": max_errors,
        "exit_code": cp.returncode,
        "olean_exists": olean.exists() and olean.stat().st_size > 0,
        "ilean_exists": ilean.exists() and ilean.stat().st_size > 0,
        "log": str(log_path.relative_to(RESULT)),
    }


def infra_metric(error: str, source_meta: dict[str, Any] | None = None) -> dict[str, Any]:
    return {
        "variant": VARIANT,
        "slug": SLUG,
        "is_baseline": IS_BASELINE,
        "classification": "INFRA_FAILURE",
        "direct_lean_executed": False,
        "error": error,
        "expected_source_sha256": EXPECTED_SHA,
        "source": source_meta or {},
        "prerequisites": {},
        "fa": {},
        "lean_version": Path("/tmp/fa442-lean-version.txt").read_text(errors="replace").strip()
            if Path("/tmp/fa442-lean-version.txt").exists() else "",
        "lake_version": Path("/tmp/fa442-lake-version.txt").read_text(errors="replace").strip()
            if Path("/tmp/fa442-lake-version.txt").exists() else "",
        "repository_head": subprocess.run(
            ["git", "rev-parse", "HEAD"], cwd=REPO,
            stdout=subprocess.PIPE, text=True, check=False,
        ).stdout.strip(),
    }


def main() -> int:
    if RESULT.exists():
        shutil.rmtree(RESULT)
    RESULT.mkdir(parents=True)
    metric: dict[str, Any]
    source_meta: dict[str, Any] | None = None
    try:
        if not LEAN_INSTALL_MARKER.exists():
            raise RuntimeError("Lean install/cache step did not complete; direct compile cannot be claimed")
        source_from_bundle = BUNDLE_ROOT / SLUG / "source.lean"
        metadata_from_bundle = BUNDLE_ROOT / SLUG / "metadata.json"
        if not source_from_bundle.exists() or not metadata_from_bundle.exists():
            raise RuntimeError(f"candidate bundle is incomplete for {SLUG}")
        bundle_meta = read_json(metadata_from_bundle)
        if bundle_meta.get("variant") != VARIANT:
            raise RuntimeError("matrix variant metadata mismatch")
        if bundle_meta.get("sha256") != EXPECTED_SHA:
            raise RuntimeError("matrix expected SHA does not match candidate bundle metadata")

        baseline_meta = read_json(BASELINE_META_PATH)
        shutil.copy2(source_from_bundle, FA_PATH)
        source_meta = source_metadata(FA_PATH.read_bytes())
        source_meta["expected_sha256"] = EXPECTED_SHA
        source_meta["sha_identity_ok"] = source_meta["sha256"] == EXPECTED_SHA
        source_meta["line_count_ok"] = source_meta["line_count"] == BASELINE_LINE_COUNT
        source_meta["blocker_header_unchanged"] = (
            source_meta["blocker_header_sha256"] == baseline_meta["blocker_header_sha256"] and
            source_meta["blocker_header"] == baseline_meta["blocker_header"]
        )
        source_meta["declaration_sequence_unchanged"] = (
            source_meta["declaration_sequence_sha256"] ==
            baseline_meta["declaration_sequence_sha256"]
        )
        source_meta["trust_audit_clean"] = audit_clean(source_meta["trust_audit"])
        if not source_meta["sha_identity_ok"]:
            raise RuntimeError("materialized candidate SHA does not match matrix SHA")
        if not source_meta["line_count_ok"]:
            raise RuntimeError("candidate line count differs from authoritative same-height baseline")
        if not source_meta["blocker_header_unchanged"]:
            raise RuntimeError("actualEdgeAmbientParam_hasDerivAt header/statement changed")
        if not source_meta["declaration_sequence_unchanged"]:
            raise RuntimeError("declaration sequence changed; line-only frontier comparison is invalid")
        if not source_meta["trust_audit_clean"]:
            raise RuntimeError(f"forbidden-token audit failed: {source_meta['trust_audit']}")
        if IS_BASELINE and source_meta["sha256"] != BASELINE_SHA256:
            raise RuntimeError("baseline matrix entry does not have authoritative baseline SHA")

        shutil.copy2(FA_PATH, RESULT / "source.lean")
        write_json(RESULT / "source-metadata.json", source_meta)

        mock2 = compile_one("Mock2", MOCK2_PATH, 400)
        mock2_adv = compile_one("Mock2_Advanced", MOCK2_ADV_PATH, 400)
        prereq_ok = (
            mock2["exit_code"] == 0 and mock2["olean_exists"] and mock2["ilean_exists"] and
            mock2_adv["exit_code"] == 0 and mock2_adv["olean_exists"] and mock2_adv["ilean_exists"]
        )
        if not prereq_ok:
            metric = infra_metric(
                "completed prerequisites did not directly compile cleanly; FA direct metric withheld",
                source_meta,
            )
            metric["prerequisites"] = {"Mock2": mock2, "Mock2_Advanced": mock2_adv}
        else:
            fa_result = compile_one("Mock2_FunctionalAnalysis", FA_PATH, MAX_ERRORS)
            fa_log = (RESULT / "Mock2_FunctionalAnalysis.log").read_text(
                encoding="utf-8", errors="replace"
            )
            source_text = FA_PATH.read_text(encoding="utf-8")
            first = parse_first_error(fa_log, source_text)
            fa_result.update({
                "first_error": first,
                "error_header_count": error_header_count(fa_log),
                "error_header_count_interpretation": (
                    "diagnostic headers captured before Lean stopped; not total errors or progress"
                ),
                "direct_lean_executed": True,
            })
            classification = "FA_PASS_CANDIDATE" if fa_result["exit_code"] == 0 else "LEAN_FAILURE"
            metric = {
                "variant": VARIANT,
                "slug": SLUG,
                "is_baseline": IS_BASELINE,
                "classification": classification,
                "direct_lean_executed": True,
                "expected_source_sha256": EXPECTED_SHA,
                "source": source_meta,
                "prerequisites": {"Mock2": mock2, "Mock2_Advanced": mock2_adv},
                "fa": fa_result,
                "lean_version": Path("/tmp/fa442-lean-version.txt").read_text(
                    errors="replace").strip(),
                "lake_version": Path("/tmp/fa442-lake-version.txt").read_text(
                    errors="replace").strip(),
                "lean_toolchain": (REPO / "lean-toolchain").read_text().strip(),
                "repository_head": subprocess.run(
                    ["git", "rev-parse", "HEAD"], cwd=REPO,
                    stdout=subprocess.PIPE, text=True, check=True,
                ).stdout.strip(),
                "mathlib_identity": subprocess.run(
                    ["git", "rev-parse", "HEAD^{tree}"], cwd=REPO,
                    stdout=subprocess.PIPE, text=True, check=True,
                ).stdout.strip(),
                "authority": "direct lake env lean CLI in this matrix job",
            }
    except Exception as exc:
        metric = infra_metric(repr(exc), source_meta)
        if FA_PATH.exists() and not (RESULT / "source.lean").exists():
            try:
                shutil.copy2(FA_PATH, RESULT / "source.lean")
            except Exception:
                pass

    write_json(RESULT / "metric.json", metric)
    append_github_output(
        classification=metric["classification"],
        infra_failure=metric["classification"] == "INFRA_FAILURE",
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
