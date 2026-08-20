#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import json
import os
import pathlib
import sys
from typing import Any

EXPECTED_ROOTS = [
    "PrimalitySheafVerification/Spt1.lean",
    "PrimalitySheafVerification/Spt2.lean",
    "PrimalitySheafVerification/Spt3.lean",
    "PrimalitySheafVerification/Spt4.lean",
    "PrimalitySheafVerification/Spt5.lean",
    "PrimalitySheafVerification/Spt6.lean",
    "PrimalitySheafVerification/Spt7.lean",
    "PrimalitySheafVerification/Mock1.lean",
    "PrimalitySheafVerification/Mock1_Advanced.lean",
    "PrimalitySheafVerification/Mock2.lean",
    "PrimalitySheafVerification/Mock2_Advanced.lean",
    "PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean",
    "PrimalitySheafVerification/QYM.lean",
]
BRIDGE = "PrimalitySheafVerification/Mock2_FunctionalAnalysis_Integrated.lean"
EXPECTED_FA_BLOB = "28f614d48e02a0f28d3f5a758e813350b3ea89cf"
EXPECTED_INTEGRATED_BLOB = "464f5dd095876b20165d12690c8127ef9d909e6a"
EXPECTED_TOOLCHAIN = "leanprover/lean4:v4.33.0-rc1"
PHASES = ("baseline", "clean1", "clean2")


def load(path: pathlib.Path) -> dict[str, Any]:
    return json.loads(path.read_text())


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def locate_phase(root: pathlib.Path, phase: str) -> pathlib.Path:
    matches = sorted(
        path.parent
        for path in root.rglob("PHASE_RESULT.json")
        if load(path).get("mode") == phase
    )
    if len(matches) != 1:
        raise SystemExit(f"expected one {phase} phase artifact, found {len(matches)}")
    return matches[0]


def canonical_manifest(manifest: dict[str, Any]) -> dict[str, Any]:
    files = []
    for row in manifest.get("files", []):
        files.append(
            {
                key: row.get(key)
                for key in (
                    "file",
                    "exists",
                    "sha256",
                    "git_blob",
                    "bytes",
                    "lines",
                    "declaration_count",
                    "declaration_sequence_sha256",
                    "trust_counts",
                    "trust_six_zero",
                )
            }
        )
    return {
        "expected_roots": manifest.get("expected_roots"),
        "expected_root_count": manifest.get("expected_root_count"),
        "existing_root_count": manifest.get("existing_root_count"),
        "all_present": manifest.get("all_present"),
        "all_nonempty": manifest.get("all_nonempty"),
        "all_trust_six_zero": manifest.get("all_trust_six_zero"),
        "bridge": manifest.get("bridge"),
        "files": files,
    }


def file_map(manifest: dict[str, Any]) -> dict[str, dict[str, Any]]:
    return {str(row["file"]): row for row in manifest.get("files", [])}


def checklist_row(number: int, key: str, title: str, passed: bool, evidence: Any) -> dict[str, Any]:
    return {
        "number": number,
        "key": key,
        "title": title,
        "pass": bool(passed),
        "evidence": evidence,
    }


def main() -> None:
    if len(sys.argv) != 3:
        raise SystemExit("usage: final13_aggregate_v2.py DOWNLOAD_ROOT OUT")
    download = pathlib.Path(sys.argv[1]).resolve()
    out = pathlib.Path(sys.argv[2]).resolve()
    out.mkdir(parents=True, exist_ok=True)

    phase_dirs = {phase: locate_phase(download, phase) for phase in PHASES}
    results = {phase: load(path / "PHASE_RESULT.json") for phase, path in phase_dirs.items()}
    before = {phase: load(path / "SOURCE_MANIFEST.before.json") for phase, path in phase_dirs.items()}
    after = {phase: load(path / "SOURCE_MANIFEST.after.json") for phase, path in phase_dirs.items()}
    audits = {phase: load(path / "COMPILER_LOG_AUDIT.json") for phase, path in phase_dirs.items()}
    envs = {phase: load(path / "ENVIRONMENT.json") for phase, path in phase_dirs.items()}

    baseline_map = file_map(before["baseline"])
    phase_sha_set = {str(result.get("github_sha")) for result in results.values()}
    env_sha_set = {str(env.get("github_sha")) for env in envs.values()}
    initial_statuses = {phase: envs[phase].get("git_status_before", []) for phase in PHASES}
    final_statuses = {phase: envs[phase].get("git_status_after", []) for phase in PHASES}

    provenance_pass = (
        len(phase_sha_set) == 1
        and phase_sha_set == env_sha_set
        and None not in phase_sha_set
        and all(not initial_statuses[phase] for phase in PHASES)
        and all(not final_statuses[phase] for phase in PHASES)
    )
    toolchain_pass = (
        all(env.get("toolchain") == EXPECTED_TOOLCHAIN for env in envs.values())
        and len({env.get("lean_version") for env in envs.values()}) == 1
        and all("4.33.0-rc1" in str(env.get("lean_version")) for env in envs.values())
        and len({env.get("lake_manifest_sha256") for env in envs.values()}) == 1
        and len({env.get("lakefile_sha256") for env in envs.values()}) == 1
    )
    canonical_roots_pass = (
        before["baseline"].get("expected_roots") == EXPECTED_ROOTS
        and before["baseline"].get("expected_root_count") == 13
        and before["baseline"].get("existing_root_count") == 13
        and set(baseline_map) == set(EXPECTED_ROOTS)
        and before["baseline"].get("bridge", {}).get("file") == BRIDGE
        and before["baseline"].get("bridge", {}).get("exists") is True
    )
    nonempty_pass = all(
        manifest.get("all_present") is True and manifest.get("all_nonempty") is True
        for manifest in before.values()
    )
    authority_pass = (
        baseline_map.get("PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean", {}).get("git_blob")
        == EXPECTED_FA_BLOB
        and before["baseline"].get("bridge", {}).get("git_blob") == EXPECTED_INTEGRATED_BLOB
    )

    canonical_before = {phase: canonical_manifest(before[phase]) for phase in PHASES}
    canonical_after = {phase: canonical_manifest(after[phase]) for phase in PHASES}
    source_stability_pass = (
        all(canonical_before[phase] == canonical_after[phase] for phase in PHASES)
        and len({json.dumps(canonical_before[phase], sort_keys=True) for phase in PHASES}) == 1
        and all(results[phase].get("source_identical") is True for phase in PHASES)
    )

    trust_totals: dict[str, int] = {
        "sorry": 0,
        "admit": 0,
        "axiom": 0,
        "unsafe": 0,
        "native_decide": 0,
        "Lean.ofReduceBool": 0,
    }
    for row in baseline_map.values():
        for key in trust_totals:
            trust_totals[key] += int(row.get("trust_counts", {}).get(key, 0))
    sorry_admit_pass = trust_totals["sorry"] == 0 and trust_totals["admit"] == 0
    axiom_unsafe_pass = trust_totals["axiom"] == 0 and trust_totals["unsafe"] == 0
    native_pass = (
        trust_totals["native_decide"] == 0
        and trust_totals["Lean.ofReduceBool"] == 0
    )

    baseline_result = results["baseline"]
    baseline_roots_pass = (
        baseline_result.get("root_count") == 13
        and baseline_result.get("root_pass") is True
        and baseline_result.get("bridge_pass") is True
    )
    strict_core_pass = (
        baseline_result.get("core_pass") is True
        and len(baseline_result.get("core", [])) == 5
        and all(
            row.get("exit") == 0
            and row.get("olean_exists") is True
            and row.get("ilean_exists") is True
            for row in baseline_result.get("core", [])
        )
    )
    buildall_baseline_pass = baseline_result.get("build_all_pass") is True
    clean1_pass = (
        results["clean1"].get("mode") == "clean1"
        and results["clean1"].get("environment_pass") is True
        and results["clean1"].get("root_pass") is True
        and results["clean1"].get("bridge_pass") is True
        and results["clean1"].get("build_all_pass") is True
        and results["clean1"].get("pass") is True
    )
    clean2_pass = (
        results["clean2"].get("mode") == "clean2"
        and results["clean2"].get("environment_pass") is True
        and results["clean2"].get("root_pass") is True
        and results["clean2"].get("bridge_pass") is True
        and results["clean2"].get("build_all_pass") is True
        and results["clean2"].get("pass") is True
    )
    log_clean = all(
        audit.get("error_header_count") == 0
        and audit.get("panic_line_count") == 0
        and audit.get("synthetic_sorry_warning_count") == 0
        and audit.get("max_error_cap_sentinel_count") == 0
        for audit in audits.values()
    )
    all_phase_pass = all(results[phase].get("pass") is True for phase in PHASES)
    qym_rows = [
        file_map(before[phase]).get("PrimalitySheafVerification/QYM.lean", {})
        for phase in PHASES
    ]
    qym_stable = len({row.get("sha256") for row in qym_rows}) == 1 and len({row.get("git_blob") for row in qym_rows}) == 1
    evidence_pass = all_phase_pass and log_clean and qym_stable

    checks = [
        checklist_row(1, "PROVENANCE_PRISTINE", "동일 커밋·초기/최종 작업트리 pristine", provenance_pass, {
            "phase_shas": sorted(phase_sha_set),
            "initial_statuses": initial_statuses,
            "final_statuses": final_statuses,
        }),
        checklist_row(2, "PINNED_TOOLCHAIN", "Lean/Lake 및 의존성 핀 일치", toolchain_pass, {
            phase: {
                "toolchain": envs[phase].get("toolchain"),
                "lean_version": envs[phase].get("lean_version"),
                "lake_version": envs[phase].get("lake_version"),
                "lake_manifest_sha256": envs[phase].get("lake_manifest_sha256"),
                "lakefile_sha256": envs[phase].get("lakefile_sha256"),
            }
            for phase in PHASES
        }),
        checklist_row(3, "CANONICAL_13_ROOTS", "정확한 13개 canonical root와 Integrated bridge 존재", canonical_roots_pass, {
            "roots": EXPECTED_ROOTS,
            "bridge": before["baseline"].get("bridge"),
        }),
        checklist_row(4, "SOURCE_NONEMPTY", "13개 소스가 비어 있지 않고 선언을 포함", nonempty_pass, {
            "existing_root_count": before["baseline"].get("existing_root_count"),
            "all_nonempty": before["baseline"].get("all_nonempty"),
        }),
        checklist_row(5, "FA_INTEGRATED_AUTHORITY", "FA TRUE PASS와 Integrated 권위 blob 보존", authority_pass, {
            "fa_blob": baseline_map.get("PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean", {}).get("git_blob"),
            "expected_fa_blob": EXPECTED_FA_BLOB,
            "integrated_blob": before["baseline"].get("bridge", {}).get("git_blob"),
            "expected_integrated_blob": EXPECTED_INTEGRATED_BLOB,
        }),
        checklist_row(6, "SOURCE_IDENTITY", "세 phase 전후·상호 간 소스 및 선언열 동일", source_stability_pass, {
            "phase_source_identical": {phase: results[phase].get("source_identical") for phase in PHASES},
        }),
        checklist_row(7, "SORRY_ADMIT_ZERO", "실행 코드의 sorry/admit 0", sorry_admit_pass, trust_totals),
        checklist_row(8, "AXIOM_UNSAFE_ZERO", "실행 코드의 axiom/unsafe 0", axiom_unsafe_pass, trust_totals),
        checklist_row(9, "NATIVE_TRUST_ZERO", "native_decide/Lean.ofReduceBool 0", native_pass, trust_totals),
        checklist_row(10, "BASELINE_13_DIRECT", "baseline 13-root와 bridge actual direct Lean PASS", baseline_roots_pass, {
            "root_count": baseline_result.get("root_count"),
            "root_pass": baseline_result.get("root_pass"),
            "bridge_pass": baseline_result.get("bridge_pass"),
        }),
        checklist_row(11, "STRICT_CORE_CHAIN", "Mock2→Advanced→FA→Integrated→QYM strict chain PASS", strict_core_pass, {
            "core": [
                {key: row.get(key) for key in ("source", "exit", "olean_exists", "ilean_exists")}
                for row in baseline_result.get("core", [])
            ],
        }),
        checklist_row(12, "BUILDALL_BASELINE", "generated BuildAll actual Lean PASS", buildall_baseline_pass, baseline_result.get("build_all")),
        checklist_row(13, "CLEAN_BUILD_ONE", "완전 삭제·cache 복구·lake build·13-root·BuildAll clean #1 PASS", clean1_pass, {
            "environment": results["clean1"].get("environment"),
            "root_pass": results["clean1"].get("root_pass"),
            "build_all_pass": results["clean1"].get("build_all_pass"),
        }),
        checklist_row(14, "CLEAN_BUILD_TWO", "독립 완전 삭제·cache 복구·lake build·13-root·BuildAll clean #2 PASS", clean2_pass, {
            "environment": results["clean2"].get("environment"),
            "root_pass": results["clean2"].get("root_pass"),
            "build_all_pass": results["clean2"].get("build_all_pass"),
        }),
        checklist_row(15, "EVIDENCE_REPRODUCIBLE", "세 phase PASS·compiler error/panic/sorry/cap 0·QYM 해시 일치", evidence_pass, {
            "phase_pass": {phase: results[phase].get("pass") for phase in PHASES},
            "compiler_audits": {
                phase: {
                    key: audits[phase].get(key)
                    for key in (
                        "logs_examined",
                        "error_header_count",
                        "panic_line_count",
                        "synthetic_sorry_warning_count",
                        "max_error_cap_sentinel_count",
                    )
                }
                for phase in PHASES
            },
            "qym": qym_rows,
        }),
    ]

    all_pass = all(row["pass"] for row in checks)
    github_sha = next(iter(phase_sha_set)) if len(phase_sha_set) == 1 else None
    tag_name = f"lean13-true-pass-{str(github_sha)[:12]}" if all_pass and github_sha else None
    report = {
        "schema": "final13-15checklist-aggregate-v2",
        "run_id": int(os.environ.get("GITHUB_RUN_ID", "0")),
        "github_sha": github_sha,
        "all_pass": all_pass,
        "passed_count": sum(row["pass"] for row in checks),
        "total_count": 15,
        "tag_name": tag_name,
        "qym_sha256": qym_rows[0].get("sha256") if qym_rows else None,
        "qym_git_blob": qym_rows[0].get("git_blob") if qym_rows else None,
        "checks": checks,
        "phase_results": results,
    }
    (out / "checklist_15_final.json").write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    (out / "execution_report.json").write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")

    status = "TRUE PASS" if all_pass else "FAIL"
    rows_md = [
        "# Lean 13-file final verification",
        "",
        f"- Status: **{status}**",
        f"- Commit: `{github_sha}`",
        f"- QYM SHA256: `{report['qym_sha256']}`",
        f"- QYM Git blob: `{report['qym_git_blob']}`",
        f"- Checklist: **{report['passed_count']}/15**",
        f"- Tag: `{tag_name}`" if tag_name else "- Tag: not created",
        "",
        "## Checklist",
        "",
    ]
    for row in checks:
        rows_md.append(f"{row['number']}. {'PASS' if row['pass'] else 'FAIL'} — {row['title']}")
    rows_md.append("")
    (out / "execution_report.md").write_text("\n".join(rows_md))
    (out / "final_status_card.md").write_text(
        "\n".join([
            f"# FINAL {status}",
            "",
            f"Commit: `{github_sha}`",
            f"13-root / BuildAll / clean×2: `{'PASS' if all_pass else 'FAIL'}`",
            f"15-checklist: `{report['passed_count']}/15`",
            f"QYM: `{'TRUE PASS' if all_pass else 'NOT CERTIFIED'}`",
            f"Tag: `{tag_name or 'NONE'}`",
            "",
        ])
    )
    (out / "gmail_final_body.md").write_text("\n".join(rows_md))
    if tag_name:
        (out / "TAG_NAME.txt").write_text(tag_name + "\n")
    if all_pass:
        (out / "TRUE_PASS").write_text(f"{github_sha}\n")

    evidence_files = sorted(path for path in out.iterdir() if path.is_file() and path.name != "evidence_sha256.txt")
    (out / "evidence_sha256.txt").write_text(
        "".join(f"{sha256(path)}  {path.name}\n" for path in evidence_files)
    )
    print(json.dumps({
        "all_pass": all_pass,
        "passed_count": report["passed_count"],
        "github_sha": github_sha,
        "qym_sha256": report["qym_sha256"],
        "qym_git_blob": report["qym_git_blob"],
        "tag_name": tag_name,
        "failed_checks": [row["number"] for row in checks if not row["pass"]],
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
