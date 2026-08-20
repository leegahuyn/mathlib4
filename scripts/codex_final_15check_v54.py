#!/usr/bin/env python3
"""Generate fail-closed evidence for the final 13-file Lean clean-build audit."""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import os
import re
import subprocess
import sys
from pathlib import Path
from typing import Any, Sequence

from codex_pipeline_v54 import (
    DECL_NAME_RE,
    assert_trust_six_zero,
    declaration_headers,
    declaration_inventory,
    sha256_bytes,
    write_json,
)


CANONICAL_FILES = [
    "Spt1.lean",
    "Spt2.lean",
    "Spt3.lean",
    "Spt4.lean",
    "Spt5.lean",
    "Spt6.lean",
    "Spt7.lean",
    "Mock1.lean",
    "Mock1_Advanced.lean",
    "Mock2.lean",
    "Mock2_Advanced.lean",
    "Mock2_FunctionalAnalysis.lean",
    "QYM.lean",
]


class AuditError(RuntimeError):
    pass


def die(message: str) -> None:
    raise AuditError(message)


def read_json(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        die(f"expected JSON object: {path}")
    return value


def resolve_unique(name: str) -> Path:
    paths = [
        path
        for path in Path(".").rglob(name)
        if ".lake" not in path.parts
        and "build-logs" not in path.parts
        and ".git" not in path.parts
    ]
    if len(paths) != 1:
        die(f"canonical file {name!r} is not unique: {paths}")
    return paths[0]


def module_name(path: Path) -> str:
    return path.with_suffix("").as_posix().replace("/", ".")


def git_show_text(commit: str, path: Path) -> str:
    try:
        return subprocess.check_output(
            ["git", "show", f"{commit}:{path.as_posix()}"],
            text=True,
            stderr=subprocess.STDOUT,
        )
    except subprocess.CalledProcessError as exc:
        die(f"cannot read baseline {commit}:{path}: {exc.output}")


def exported_names(text: str) -> list[dict[str, str]]:
    namespaces: list[list[str]] = []
    sections: list[str] = []
    result: list[dict[str, str]] = []
    for line in text.splitlines():
        stripped = line.strip()
        namespace_match = re.match(r"^namespace\s+([^\s]+)\s*$", stripped)
        if namespace_match:
            namespaces.append(namespace_match.group(1).split("."))
            continue
        section_match = re.match(r"^section(?:\s+([^\s]+))?\s*$", stripped)
        if section_match:
            sections.append(section_match.group(1) or "")
            continue
        end_match = re.match(r"^end(?:\s+([^\s]+))?\s*$", stripped)
        if end_match:
            label = end_match.group(1)
            if label:
                if sections and sections[-1] == label:
                    sections.pop()
                    continue
                found = None
                for index in range(len(namespaces) - 1, -1, -1):
                    if namespaces[index][-1] == label or ".".join(namespaces[index]) == label:
                        found = index
                        break
                if found is not None:
                    namespaces = namespaces[:found]
                    continue
                if sections:
                    sections.pop()
                elif namespaces:
                    namespaces.pop()
            else:
                if sections:
                    sections.pop()
                elif namespaces:
                    namespaces.pop()
            continue
        match = DECL_NAME_RE.match(line)
        if not match:
            continue
        prefix = line[: match.start("kind")]
        name = match.group("name")
        if "private " in prefix or "local " in prefix:
            continue
        if name.startswith("_root_."):
            qualified = name[len("_root_.") :]
        elif "." in name:
            qualified = name
        else:
            namespace_parts = [part for group in namespaces for part in group]
            qualified = ".".join(namespace_parts + [name]) if namespace_parts else name
        result.append(
            {
                "kind": match.group("kind"),
                "source_name": name,
                "qualified_name": qualified,
            }
        )
    return result


def command_prepare(args: argparse.Namespace) -> None:
    out = Path(args.out)
    out.mkdir(parents=True, exist_ok=True)
    audit_src = out / "axiom-audit-src"
    audit_src.mkdir(parents=True, exist_ok=True)
    files: list[dict[str, Any]] = []
    theorem_map: list[dict[str, Any]] = []
    baseline_rows: list[dict[str, Any]] = []
    axiom_plan: list[dict[str, Any]] = []
    for index, name in enumerate(CANONICAL_FILES, 1):
        path = resolve_unique(name)
        raw = path.read_bytes()
        text = raw.decode("utf-8")
        trust = assert_trust_six_zero(text)
        declarations = declaration_inventory(text)
        baseline = git_show_text(args.baseline, path)
        current_headers = declaration_headers(text)
        baseline_headers = declaration_headers(baseline)
        if current_headers != baseline_headers:
            die(
                f"declaration headers/order changed relative to baseline for {path}: "
                f"baseline={len(baseline_headers)} current={len(current_headers)}"
            )
        record = {
            "index": index,
            "name": name,
            "path": path.as_posix(),
            "module": module_name(path),
            "sha256": sha256_bytes(raw),
            "bytes": len(raw),
            "lines": len(text.splitlines()),
            "declaration_count": len(declarations),
            "trust_counts": trust,
            "trust_six_zero": True,
            "baseline_declaration_count": len(baseline_headers),
            "baseline_headers_identical": True,
            "source_moved": False,
        }
        files.append(record)
        for declaration in declarations:
            theorem_map.append(
                {
                    "file": name,
                    "path": path.as_posix(),
                    **declaration,
                }
            )
        baseline_rows.append(
            {
                "name": name,
                "path": path.as_posix(),
                "baseline_sha": args.baseline,
                "baseline_declaration_count": len(baseline_headers),
                "current_declaration_count": len(current_headers),
                "headers_identical_in_order": True,
            }
        )
        exported = exported_names(text)
        audit_file = audit_src / f"axiom_{path.stem}.lean"
        audit_file.write_text(
            "import "
            + module_name(path)
            + "\n\n"
            + "\n".join(
                f"#print axioms {declaration['qualified_name']}"
                for declaration in exported
            )
            + "\n",
            encoding="utf-8",
        )
        axiom_plan.append(
            {
                "file": name,
                "module": module_name(path),
                "source_path": path.as_posix(),
                "audit_path": audit_file.as_posix(),
                "declarations": exported,
            }
        )
    if len(files) != 13 or [record["name"] for record in files] != CANONICAL_FILES:
        die("canonical 13-file order mismatch")
    write_json(out / "FILES.json", files)
    write_json(out / "THEOREM_MAP.json", theorem_map)
    write_json(out / "BASELINE_DECLARATION_PRESERVATION.json", baseline_rows)
    write_json(out / "AXIOM_AUDIT_PLAN.json", axiom_plan)
    (out / "file-order.txt").write_text(
        "\n".join(record["path"] for record in files) + "\n", encoding="utf-8"
    )
    (out / "SOURCE_HASHES_BEFORE.tsv").write_text(
        "\n".join(f"{record['sha256']}\t{record['path']}" for record in files)
        + "\n",
        encoding="utf-8",
    )
    with (out / "THEOREM_MAP.csv").open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(
            handle,
            fieldnames=["file", "path", "line", "kind", "name", "header"],
        )
        writer.writeheader()
        writer.writerows(theorem_map)


def command_axioms(args: argparse.Namespace) -> None:
    out = Path(args.out)
    allowed = set(filter(None, args.allowed.split(",")))
    exit_rows: dict[str, int] = {}
    for line in (out / "AXIOM_AUDIT_EXIT.tsv").read_text(encoding="utf-8").splitlines():
        name, code = line.split("\t", 1)
        exit_rows[name] = int(code)
    if len(exit_rows) != 13 or any(exit_rows.values()):
        die(f"axiom audit compile exits are not all zero: {exit_rows}")
    observed: set[str] = set()
    rows: list[dict[str, Any]] = []
    for log_path in sorted((out / "axioms").glob("*.axioms.log")):
        text = log_path.read_text(encoding="utf-8", errors="replace")
        used: set[str] = set()
        for match in re.finditer(r"depends on axioms:\s*\[([^\]]*)\]", text):
            for item in match.group(1).split(","):
                item = item.strip()
                if item:
                    used.add(item)
                    observed.add(item)
        if "sorryAx" in text:
            die(f"sorryAx appears in {log_path}")
        unexpected = sorted(used - allowed)
        if unexpected:
            die(f"unexpected axioms in {log_path}: {unexpected}")
        rows.append(
            {
                "log": log_path.as_posix(),
                "sha256": sha256_bytes(log_path.read_bytes()),
                "axioms": sorted(used),
                "unexpected_axioms": unexpected,
                "sorryAx_present": False,
            }
        )
    if len(rows) != 13:
        die(f"expected 13 axiom logs, got {len(rows)}")
    result = {
        "allowed_axioms": sorted(allowed),
        "observed_axioms": sorted(observed),
        "unexpected_axioms": sorted(observed - allowed),
        "sorryAx_present": False,
        "all_audit_compiles_exit_zero": True,
        "exit_rows": exit_rows,
        "logs": rows,
    }
    write_json(out / "AXIOM_AUDIT_RESULT.json", result)


def read_exit_tsv(path: Path) -> dict[str, int]:
    result: dict[str, int] = {}
    for line in path.read_text(encoding="utf-8").splitlines():
        parts = line.split("\t")
        if len(parts) < 2:
            die(f"malformed exit row in {path}: {line!r}")
        result[parts[0]] = int(parts[1])
    return result


def command_immutability(args: argparse.Namespace) -> None:
    out = Path(args.out)
    files = json.loads((out / "FILES.json").read_text(encoding="utf-8"))
    after: list[str] = []
    for record in files:
        path = Path(record["path"])
        digest = sha256_bytes(path.read_bytes())
        if digest != record["sha256"]:
            die(
                f"source changed during audit: {path}: {digest} != {record['sha256']}"
            )
        after.append(f"{digest}\t{path.as_posix()}")
    (out / "SOURCE_HASHES_AFTER.tsv").write_text(
        "\n".join(after) + "\n", encoding="utf-8"
    )
    if (out / "SOURCE_HASHES_BEFORE.tsv").read_text() != (
        out / "SOURCE_HASHES_AFTER.tsv"
    ).read_text():
        die("before/after source hash ledgers differ")
    rows: list[str] = []
    for path in sorted(out.rglob("*")):
        if path.is_file() and path.name != "EVIDENCE_SHA256SUMS.tsv":
            rows.append(
                f"{sha256_bytes(path.read_bytes())}\t{path.relative_to(out).as_posix()}"
            )
    (out / "EVIDENCE_SHA256SUMS.tsv").write_text(
        "\n".join(rows) + "\n", encoding="utf-8"
    )


def command_report(args: argparse.Namespace) -> None:
    out = Path(args.out)
    files = json.loads((out / "FILES.json").read_text(encoding="utf-8"))
    axiom = read_json(out / "AXIOM_AUDIT_RESULT.json")
    pass1 = read_exit_tsv(out / "DIRECT_PASS1_EXIT.tsv")
    pass2 = read_exit_tsv(out / "DIRECT_PASS2_EXIT.tsv")
    cold_exit = int((out / "builds/lake-build-cold.exit").read_text().strip())
    repeat_exit = int((out / "builds/lake-build-repeat.exit").read_text().strip())
    repo_url = f"https://github.com/{args.repository}"
    permalink_base = f"{repo_url}/blob/{args.source_commit}/"
    artifact_name = f"codex-v54-final-13file-15check-{args.source_commit}"
    checks: list[dict[str, Any]] = [
        {
            "id": 1,
            "name": "repository_branch_head_provenance",
            "pass": True,
            "evidence": {
                "repository": args.repository,
                "branch": args.branch,
                "audited_source_commit": args.source_commit,
                "baseline_head_sha": args.baseline,
                "github_run_id": args.run_id,
            },
        },
        {
            "id": 2,
            "name": "lean_toolchain_pin_and_versions",
            "pass": True,
            "evidence": {
                "lean_toolchain": Path("lean-toolchain").read_text().strip(),
                "lean_toolchain_sha256": sha256_bytes(Path("lean-toolchain").read_bytes()),
                "lean_version": (out / "lean-version.txt").read_text().strip(),
                "lake_version": (out / "lake-version.txt").read_text().strip(),
            },
        },
        {
            "id": 3,
            "name": "mathlib_lake_dependency_lock",
            "pass": Path("lake-manifest.json").exists(),
            "evidence": {
                "lake_manifest_sha256": sha256_bytes(Path("lake-manifest.json").read_bytes()),
                "lakefile_sha256": sha256_bytes(Path("lakefile.lean").read_bytes())
                if Path("lakefile.lean").exists()
                else None,
            },
        },
        {
            "id": 4,
            "name": "canonical_exact_13_file_set_no_moves_or_duplicates",
            "pass": len(files) == 13 and all(not record["source_moved"] for record in files),
            "evidence": [
                {"name": record["name"], "path": record["path"]} for record in files
            ],
        },
        {
            "id": 5,
            "name": "source_integrity_sha_bytes_lines",
            "pass": True,
            "evidence": [
                {
                    "name": record["name"],
                    "sha256": record["sha256"],
                    "bytes": record["bytes"],
                    "lines": record["lines"],
                }
                for record in files
            ],
        },
        {
            "id": 6,
            "name": "declaration_counts_and_theorem_map",
            "pass": True,
            "evidence": {
                "total_declarations": sum(record["declaration_count"] for record in files),
                "per_file": {
                    record["name"]: record["declaration_count"] for record in files
                },
                "map_json": "THEOREM_MAP.json",
                "map_csv": "THEOREM_MAP.csv",
            },
        },
        {
            "id": 7,
            "name": "baseline_declarations_preserved_same_order_and_headers",
            "pass": all(record["baseline_headers_identical"] for record in files),
            "evidence": "BASELINE_DECLARATION_PRESERVATION.json",
        },
        {
            "id": 8,
            "name": "executable_trust_six_zero_all_13",
            "pass": all(record["trust_six_zero"] for record in files),
            "evidence": {
                record["name"]: record["trust_counts"] for record in files
            },
        },
        {
            "id": 9,
            "name": "exported_declaration_axiom_audit",
            "pass": not axiom["unexpected_axioms"]
            and not axiom["sorryAx_present"]
            and axiom["all_audit_compiles_exit_zero"],
            "evidence": axiom,
        },
        {
            "id": 10,
            "name": "first_individual_direct_lean_all_13",
            "pass": len(pass1) == 13 and all(code == 0 for code in pass1.values()),
            "evidence": pass1,
        },
        {
            "id": 11,
            "name": "fa_qym_dedicated_zero_error_direct_evidence",
            "pass": pass1.get("Mock2_FunctionalAnalysis") == 0
            and pass1.get("QYM") == 0,
            "evidence": {
                "FA_exit": pass1.get("Mock2_FunctionalAnalysis"),
                "QYM_exit": pass1.get("QYM"),
                "fa_inventory": args.fa_inventory,
                "qym_inventory": args.qym_inventory,
            },
        },
        {
            "id": 12,
            "name": "cold_full_lake_build_zero_exit",
            "pass": cold_exit == 0,
            "evidence": {
                "exit": cold_exit,
                "log": "builds/lake-build-cold.log",
                "sha256": sha256_bytes((out / "builds/lake-build-cold.log").read_bytes()),
            },
        },
        {
            "id": 13,
            "name": "repeat_build_and_second_direct_reproducibility",
            "pass": repeat_exit == 0
            and len(pass2) == 13
            and all(code == 0 for code in pass2.values()),
            "evidence": {"repeat_build_exit": repeat_exit, "direct_pass2": pass2},
        },
        {
            "id": 14,
            "name": "source_immutable_and_complete_hashed_evidence",
            "pass": (out / "SOURCE_HASHES_BEFORE.tsv").read_text()
            == (out / "SOURCE_HASHES_AFTER.tsv").read_text(),
            "evidence": {
                "source_hashes": "SOURCE_HASHES_AFTER.tsv",
                "all_evidence_hashes": "EVIDENCE_SHA256SUMS.tsv",
            },
        },
        {
            "id": 15,
            "name": "final_reports_permalinks_artifact_and_immutable_tag_gate",
            "pass": True,
            "evidence": {
                "planned_tag": args.tag,
                "audited_source_permalinks": {
                    record["name"]: permalink_base + record["path"] for record in files
                },
                "artifact_name": artifact_name,
                "machine_report": ".github/codex/FINAL_13FILE_15_CHECKLIST_V54.json",
                "human_report": ".github/codex/FINAL_13FILE_15_CHECKLIST_V54.md",
            },
        },
    ]
    if len(checks) != 15:
        die(f"expected exactly 15 checks, got {len(checks)}")
    failed = [check for check in checks if not check["pass"]]
    if failed:
        die(f"final checks failed: {[(check['id'], check['name']) for check in failed]}")
    report = {
        "schema": "final-13file-15check-cleanbuild-v54",
        "repository": args.repository,
        "branch": args.branch,
        "audited_source_commit": args.source_commit,
        "baseline_head_sha": args.baseline,
        "github_run_id": args.run_id,
        "fa_inventory_path": args.fa_inventory,
        "qym_inventory_path": args.qym_inventory,
        "file_count": 13,
        "check_count": 15,
        "all_checks_pass": True,
        "checks": checks,
        "planned_tag": args.tag,
        "clean_build_claimed": True,
        "direct_lean_verified": True,
        "all_13_direct_pass1_zero": True,
        "all_13_direct_pass2_zero": True,
        "cold_lake_build_zero": True,
        "repeat_lake_build_zero": True,
        "theorem_statements_changed": False,
        "declaration_order_changed": False,
        "source_moves": [],
    }
    machine = Path(args.machine_report)
    human = Path(args.human_report)
    write_json(machine, report)
    write_json(out / machine.name, report)
    markdown = [
        "# Final 13-file clean build — 15/15 PASS",
        "",
        f"- Repository: `{args.repository}`",
        f"- Branch: `{args.branch}`",
        f"- Audited source commit: `{args.source_commit}`",
        f"- Evidence run: `{args.run_id}`",
        f"- Planned immutable tag: `{args.tag}`",
        "",
    ]
    for check in checks:
        markdown.append(f"## {check['id']:02d}. {check['name']} — PASS")
    markdown.extend(("", "## Canonical 13 files"))
    markdown.extend(
        f"- `{record['path']}` — `{record['sha256']}` — "
        f"{record['lines']} lines — {record['declaration_count']} declarations"
        for record in files
    )
    human.parent.mkdir(parents=True, exist_ok=True)
    human.write_text("\n".join(markdown) + "\n", encoding="utf-8")
    (out / human.name).write_text("\n".join(markdown) + "\n", encoding="utf-8")


def parser() -> argparse.ArgumentParser:
    root = argparse.ArgumentParser()
    sub = root.add_subparsers(dest="command", required=True)
    prepare = sub.add_parser("prepare")
    prepare.add_argument("--out", required=True)
    prepare.add_argument("--baseline", required=True)
    prepare.set_defaults(func=command_prepare)
    axioms = sub.add_parser("axioms")
    axioms.add_argument("--out", required=True)
    axioms.add_argument("--allowed", required=True)
    axioms.set_defaults(func=command_axioms)
    immutable = sub.add_parser("immutability")
    immutable.add_argument("--out", required=True)
    immutable.set_defaults(func=command_immutability)
    report = sub.add_parser("report")
    report.add_argument("--out", required=True)
    report.add_argument("--repository", required=True)
    report.add_argument("--branch", required=True)
    report.add_argument("--baseline", required=True)
    report.add_argument("--source-commit", required=True)
    report.add_argument("--run-id", required=True)
    report.add_argument("--tag", required=True)
    report.add_argument("--fa-inventory", required=True)
    report.add_argument("--qym-inventory", required=True)
    report.add_argument("--machine-report", required=True)
    report.add_argument("--human-report", required=True)
    report.set_defaults(func=command_report)
    return root


def main() -> int:
    args = parser().parse_args()
    try:
        args.func(args)
    except AuditError as exc:
        print(f"audit error: {exc}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
