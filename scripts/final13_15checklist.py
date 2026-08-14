#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path

FILES = [
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
TRUST = ("sorry", "admit", "axiom", "unsafe", "native_decide", "Lean.ofReduceBool")
DECL_RE = re.compile(
    r"(?m)^(?:protected\s+|private\s+|noncomputable\s+|local\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance|structure|class)\s+([^\s(:]+)"
)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def strip_noncode(text: str) -> str:
    out = list(text)
    i = 0
    depth = 0
    string = False
    esc = False
    while i < len(out):
        if depth:
            if text.startswith("/-", i):
                out[i] = out[i + 1] = " "
                depth += 1
                i += 2
                continue
            if text.startswith("-/", i):
                out[i] = out[i + 1] = " "
                depth -= 1
                i += 2
                continue
            if out[i] != "\n":
                out[i] = " "
            i += 1
            continue
        if string:
            ch = out[i]
            if ch != "\n":
                out[i] = " "
            if esc:
                esc = False
            elif ch == "\\":
                esc = True
            elif ch == '"':
                string = False
            i += 1
            continue
        if text.startswith("/-", i):
            out[i] = out[i + 1] = " "
            depth = 1
            i += 2
            continue
        if text.startswith("--", i):
            while i < len(out) and out[i] != "\n":
                out[i] = " "
                i += 1
            continue
        if out[i] == '"':
            out[i] = " "
            string = True
        i += 1
    return "".join(out)


def trust_counts(text: str) -> dict[str, int]:
    code = strip_noncode(text)
    return {
        token: len(
            re.findall(
                r"(?<![A-Za-z0-9_])" + re.escape(token) + r"(?![A-Za-z0-9_])",
                code,
            )
        )
        for token in TRUST
    }


def inventory(repo: Path, out: Path, phase: str) -> dict[str, object]:
    rows: list[dict[str, object]] = []
    for relative in FILES:
        path = repo / relative
        if not path.exists():
            rows.append({"file": relative, "exists": False})
            continue
        raw = path.read_bytes()
        text = raw.decode()
        trust = trust_counts(text)
        declarations = DECL_RE.findall(text)
        rows.append(
            {
                "file": relative,
                "exists": True,
                "sha256": hashlib.sha256(raw).hexdigest(),
                "bytes": len(raw),
                "lines": len(text.splitlines()),
                "declaration_count": len(declarations),
                "declaration_sequence_sha256": hashlib.sha256(
                    "\n".join(declarations).encode()
                ).hexdigest(),
                "trust_counts": trust,
                "trust_six_zero": all(value == 0 for value in trust.values()),
            }
        )
    report = {
        "schema": "final13-source-inventory-v1",
        "phase": phase,
        "expected_files": FILES,
        "expected_file_count": len(FILES),
        "existing_file_count": sum(1 for row in rows if row.get("exists")),
        "all_present": all(row.get("exists") is True for row in rows),
        "all_nonempty": all(
            row.get("exists") is True
            and int(row.get("bytes", 0)) > 0
            and int(row.get("lines", 0)) > 0
            and int(row.get("declaration_count", 0)) > 0
            for row in rows
        ),
        "all_trust_six_zero": all(row.get("trust_six_zero") is True for row in rows),
        "files": rows,
    }
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(report, ensure_ascii=False, indent=2, sort_keys=True) + "\n")
    return report


def read_json(path: Path) -> dict[str, object]:
    if not path.exists():
        return {}
    return json.loads(path.read_text())


def read_text(path: Path) -> str:
    return path.read_text(errors="replace").strip() if path.exists() else ""


def numeric_exit(path: Path) -> int | None:
    value = read_text(path)
    return int(value) if value.isdigit() else None


def parse_tsv(path: Path) -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    if not path.exists():
        return rows
    for raw in path.read_text(errors="replace").splitlines():
        if not raw.strip():
            continue
        parts = raw.split("\t")
        if len(parts) < 2:
            rows.append({"raw": raw, "valid": False})
            continue
        code = int(parts[-1]) if parts[-1].isdigit() else None
        rows.append(
            {
                "file": parts[0],
                "state": parts[1] if len(parts) >= 3 else "EXECUTED",
                "exit": code,
                "valid": code is not None,
            }
        )
    return rows


def tsv_all_clean(path: Path, expected: int) -> tuple[bool, list[dict[str, object]]]:
    rows = parse_tsv(path)
    clean = (
        len(rows) == expected
        and all(row.get("valid") is True and row.get("exit") == 0 for row in rows)
    )
    return clean, rows


def inventories_identical(before: dict[str, object], after: dict[str, object]) -> bool:
    before_rows = {row["file"]: row for row in before.get("files", []) if row.get("exists")}
    after_rows = {row["file"]: row for row in after.get("files", []) if row.get("exists")}
    if set(before_rows) != set(after_rows):
        return False
    keys = ("sha256", "bytes", "lines", "declaration_count", "declaration_sequence_sha256")
    return all(
        all(before_rows[name].get(key) == after_rows[name].get(key) for key in keys)
        for name in before_rows
    )


def make_item(number: int, key: str, title: str, passed: bool, evidence: object) -> dict[str, object]:
    return {
        "number": number,
        "key": key,
        "title": title,
        "status": "PASS" if passed else "FAIL",
        "passed": passed,
        "evidence": evidence,
    }


def first14(evidence: Path, github_sha: str) -> dict[str, object]:
    before = read_json(evidence / "SOURCE_MANIFEST.before.json")
    after = read_json(evidence / "SOURCE_MANIFEST.after.json")
    pass1_clean, pass1_rows = tsv_all_clean(evidence / "direct-pass1.tsv", 13)
    pass2_clean, pass2_rows = tsv_all_clean(evidence / "direct-pass2.tsv", 13)
    core_clean, core_rows = tsv_all_clean(evidence / "core-chain.tsv", 4)
    checkout_head = read_text(evidence / "checkout-head.txt")
    checkout_status = read_text(evidence / "checkout-status-before.txt")
    lean_toolchain = read_text(evidence / "lean-toolchain.txt")
    lean_version = read_text(evidence / "lean-version.txt")
    lake_version = read_text(evidence / "lake-version.txt")
    environment_hashes = read_text(evidence / "environment.sha256")
    lake_clean_exit = numeric_exit(evidence / "lake-clean.exit")
    cache_restore_exit = numeric_exit(evidence / "cache-restore-after-clean.exit")
    lake_build_exit = numeric_exit(evidence / "lake-build.exit")
    aggregate_exit = numeric_exit(evidence / "aggregate-import.exit")
    warnings = read_json(evidence / "COMPILER_WARNING_AUDIT.json")

    trust_sums = {token: 0 for token in TRUST}
    for row in before.get("files", []):
        counts = row.get("trust_counts", {})
        for token in TRUST:
            trust_sums[token] += int(counts.get(token, 0))

    items = [
        make_item(
            1,
            "repository_identity",
            "Exact branch commit and initially clean checkout are locked",
            checkout_head == github_sha and checkout_status == "",
            {"expected_sha": github_sha, "observed_sha": checkout_head, "porcelain": checkout_status},
        ),
        make_item(
            2,
            "lean_toolchain_pin",
            "lean-toolchain pin is installed and the exact Lean/Lake versions are recorded",
            bool(lean_toolchain) and lean_toolchain in lean_version and bool(lake_version),
            {"lean_toolchain": lean_toolchain, "lean_version": lean_version, "lake_version": lake_version},
        ),
        make_item(
            3,
            "mathlib_manifest_lock",
            "lakefile, lake-manifest, and lean-toolchain identities are cryptographically recorded",
            len(environment_hashes.splitlines()) >= 3
            and all(len(line.split()) >= 2 for line in environment_hashes.splitlines()),
            {"environment_sha256": environment_hashes},
        ),
        make_item(
            4,
            "all_13_sources_present",
            "All exact 13 required Lean source files exist at canonical paths",
            before.get("all_present") is True and before.get("existing_file_count") == 13,
            {"expected": 13, "existing": before.get("existing_file_count")},
        ),
        make_item(
            5,
            "source_identity_inventory",
            "SHA256, bytes, lines, and declaration counts are complete for every source",
            before.get("all_nonempty") is True
            and all(
                all(key in row for key in ("sha256", "bytes", "lines", "declaration_count"))
                for row in before.get("files", [])
            ),
            {"manifest": "SOURCE_MANIFEST.before.json"},
        ),
        make_item(
            6,
            "declaration_and_source_integrity",
            "Source hashes and declaration sequences are unchanged by all verification passes",
            inventories_identical(before, after),
            {"before": "SOURCE_MANIFEST.before.json", "after": "SOURCE_MANIFEST.after.json"},
        ),
        make_item(
            7,
            "sorry_admit_zero",
            "Executable-code sorry and admit counts are both zero in all 13 files",
            trust_sums["sorry"] == 0 and trust_sums["admit"] == 0,
            {"sorry": trust_sums["sorry"], "admit": trust_sums["admit"]},
        ),
        make_item(
            8,
            "axiom_unsafe_zero",
            "Executable-code axiom and unsafe counts are both zero in all 13 files",
            trust_sums["axiom"] == 0 and trust_sums["unsafe"] == 0,
            {"axiom": trust_sums["axiom"], "unsafe": trust_sums["unsafe"]},
        ),
        make_item(
            9,
            "native_escape_zero",
            "native_decide and Lean.ofReduceBool escape counts are both zero in all 13 files",
            trust_sums["native_decide"] == 0 and trust_sums["Lean.ofReduceBool"] == 0,
            {
                "native_decide": trust_sums["native_decide"],
                "Lean.ofReduceBool": trust_sums["Lean.ofReduceBool"],
            },
        ),
        make_item(
            10,
            "individual_direct_lean_pass1",
            "Every one of the 13 files executes a first direct Lean compile with exit zero",
            pass1_clean,
            pass1_rows,
        ),
        make_item(
            11,
            "core_dependency_chain",
            "Mock2, Mock2_Advanced, Mock2_FunctionalAnalysis, and QYM pass in strict order",
            core_clean,
            core_rows,
        ),
        make_item(
            12,
            "fresh_lake_clean_build",
            "lake clean, cache restoration, and the pinned project build all exit zero",
            lake_clean_exit == 0 and cache_restore_exit == 0 and lake_build_exit == 0,
            {
                "lake_clean_exit": lake_clean_exit,
                "cache_restore_after_clean_exit": cache_restore_exit,
                "lake_build_exit": lake_build_exit,
            },
        ),
        make_item(
            13,
            "aggregate_13_import_smoke",
            "One generated module importing all 13 required modules compiles with direct Lean",
            aggregate_exit == 0,
            {"aggregate_import_exit": aggregate_exit},
        ),
        make_item(
            14,
            "second_direct_reproducibility_and_warning_audit",
            "A second full direct pass is clean, source-identical, uncapped, and has no synthetic sorry warning",
            pass2_clean
            and inventories_identical(before, after)
            and warnings.get("synthetic_sorry_warning_count") == 0
            and warnings.get("error_header_count") == 0
            and warnings.get("max_error_cap_sentinel_count") == 0,
            {
                "direct_pass2": pass2_rows,
                "warning_audit": warnings,
                "source_identical": inventories_identical(before, after),
            },
        ),
    ]
    report = {
        "schema": "final13-first14-checklist-v1",
        "github_sha": github_sha,
        "items": items,
        "passed_count": sum(1 for item in items if item["passed"]),
        "failed_count": sum(1 for item in items if not item["passed"]),
        "all_first14_pass": all(item["passed"] for item in items),
    }
    (evidence / "FIRST14_GATE.json").write_text(
        json.dumps(report, ensure_ascii=False, indent=2, sort_keys=True) + "\n"
    )
    return report


def finalize(evidence: Path, github_sha: str) -> dict[str, object]:
    first = read_json(evidence / "FIRST14_GATE.json")
    tag = read_json(evidence / "TAG_STATUS.json")
    bundle = read_json(evidence / "EVIDENCE_BUNDLE_MANIFEST.json")
    item15_pass = (
        first.get("all_first14_pass") is True
        and tag.get("status") == "PASS"
        and tag.get("target_sha") == github_sha
        and bundle.get("status") == "PASS"
        and int(bundle.get("file_count", 0)) > 0
    )
    item15 = make_item(
        15,
        "immutable_evidence_bundle_and_tag",
        "The complete evidence bundle is hashed and an immutable source-commit tag is verified",
        item15_pass,
        {"tag": tag, "bundle": bundle},
    )
    items = list(first.get("items", [])) + [item15]
    final = {
        "schema": "final13-15-checklist-gate-v1",
        "github_sha": github_sha,
        "status": "PASS" if all(item.get("passed") is True for item in items) else "FAIL",
        "passed_count": sum(1 for item in items if item.get("passed") is True),
        "failed_count": sum(1 for item in items if item.get("passed") is not True),
        "items": items,
        "source_manifest_sha256": sha256(evidence / "SOURCE_MANIFEST.before.json")
        if (evidence / "SOURCE_MANIFEST.before.json").exists()
        else None,
    }
    (evidence / "FINAL_15_CHECKLIST.json").write_text(
        json.dumps(final, ensure_ascii=False, indent=2, sort_keys=True) + "\n"
    )
    lines = [
        "# Lean 13-File Clean-Build and 15-Checklist Final Gate",
        "",
        f"- GitHub source SHA: `{github_sha}`",
        f"- Final status: **{final['status']}**",
        f"- Passed: {final['passed_count']}/15",
        "",
    ]
    for item in items:
        marker = "x" if item.get("passed") is True else " "
        lines.append(f"- [{marker}] {item['number']}. {item['title']} — **{item['status']}**")
    lines.extend(
        [
            "",
            "The JSON gate and all raw logs in this evidence directory are authoritative.",
            "A green workflow without `FINAL_15_CHECKLIST.json` status `PASS` is not a final pass.",
        ]
    )
    (evidence / "FINAL_15_CHECKLIST.md").write_text("\n".join(lines) + "\n")
    print(json.dumps(final, ensure_ascii=False, indent=2, sort_keys=True))
    return final


def main() -> None:
    parser = argparse.ArgumentParser()
    sub = parser.add_subparsers(dest="command", required=True)

    inv = sub.add_parser("inventory")
    inv.add_argument("--repo", type=Path, default=Path("."))
    inv.add_argument("--out", type=Path, required=True)
    inv.add_argument("--phase", required=True)

    pre = sub.add_parser("first14")
    pre.add_argument("--evidence", type=Path, required=True)
    pre.add_argument("--github-sha", required=True)

    fin = sub.add_parser("finalize")
    fin.add_argument("--evidence", type=Path, required=True)
    fin.add_argument("--github-sha", required=True)

    args = parser.parse_args()
    if args.command == "inventory":
        report = inventory(args.repo, args.out, args.phase)
        print(json.dumps(report, ensure_ascii=False, indent=2, sort_keys=True))
    elif args.command == "first14":
        first14(args.evidence, args.github_sha)
    else:
        finalize(args.evidence, args.github_sha)


if __name__ == "__main__":
    main()
