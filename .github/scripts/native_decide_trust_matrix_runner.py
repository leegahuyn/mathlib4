#!/usr/bin/env python3
"""Isolated direct-Lean runner for the native_decide trust-repair matrix.

Intended repository path when promoted for CI:
  .github/scripts/native_decide_trust_matrix_runner.py

The runner deliberately does not compile the forbidden baseline.  It verifies
the exact checked-in source blobs, asks the guarded preparer to materialize one
candidate outside the checkout, proves source/candidate declaration sequence
and header identity statically, and then directly compiles the two repaired
roots.  Only after *both* roots and their post-elaboration trust audits pass are
downstream modules compiled.

Use --prepare-only for a source-only dry run.  That mode never invokes Lean,
Lake, Git, or GitHub and never writes inside the source directory.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
import time
from dataclasses import asdict, dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Iterable


SOURCE_SHA256 = {
    "Spt1": "0ef9289806dcb5b57d1d801526e45fe71bd2c85768b5b6f375fa9de005037e74",
    "Mock1_Advanced": "69f0703cc03fd0efde38b9d7018424cc62b724e0afaab7b66e3ccafb4d9f0311",
}

CANDIDATE_SHA256 = {
    "kernel": {
        "Spt1": "1294f6bbf361798a0706ab960b427b1f0165cd0a3670b0e130cb723a8de63b51",
        "Mock1_Advanced": "25eb501aea633b950fc5b7296b5b752aa4ac9c0812ee96fde120f3076e0ca34f",
    },
    "elab": {
        "Spt1": "124075df7f3c23a9d3f00c4b4aa996e8dee2b87d9174f2babae9197d02ae86fa",
        "Mock1_Advanced": "0d504d07e50d7d9b2f128a0e6288244f03a339b23f85da7204a3157a45425b4f",
    },
}

ROOT_MODULES = ("Spt1", "Mock1_Advanced")

# These are deliberately direct, sequential checks.  BuildAll is last so that
# it verifies importability of both freshly generated root oleans as a unit.
DOWNSTREAM_MODULES = (
    "Spt2",
    "Spt3",
    "Spt4",
    "Spt5",
    "Spt6",
    "Spt7",
    "Mock1",
    "Mock2",
    "Mock2_Advanced",
    "Mock2_FunctionalAnalysis",
    "QYM",
    "BuildAll",
)

# The 60 native_decide tactic uses in Mock1_Advanced occur in exactly these 58
# enclosing declarations.  Two certificate-valued declarations each contain
# two affected field proofs.  Every target is post-checked with both #check and
# #print axioms.
AFFECTED_TARGETS = (
    "MockCert.Mock1Advanced.advanced_claims_ii_paper_i2_extrapolated_value_table",
    "MockCert.Mock1Advanced.advanced_claims_ii_paper_i2_extrapolated_residue_table",
    "MockCert.Mock1Advanced.advanced_claims_ii_paper_i2_forward_difference_table",
    "MockCert.Mock1Advanced.advanced_claims_ii_paper_i2_forward_difference_residue_table",
    "MockCert.Mock1Advanced.advanced_claims_ii_paper_t1t2_full_depth",
    "MockCert.Mock1Advanced.advanced_claims_ii_paper_t1t2_full_column_count",
    "MockCert.Mock1Advanced.advanced_claims_ii_paper_t1t2_full_matrix_formula",
    "MockCert.Mock1Advanced.advanced_claims_ii_paper_t1t2_full_matrix_rows",
    "MockCert.Mock1Advanced.advanced_claims_ii_paper_t1t2_full_matrix_row_lengths",
    "MockCert.Mock1Advanced.advanced_claims_ii_paper_t1t2_full_rhs_table",
    "MockCert.Mock1Advanced.advanced_claims_ii_paper_t1t2_full_solution_table",
    "MockCert.Mock1Advanced.advanced_claims_ii_paper_t1t2_full_matvec",
    "MockCert.Mock1Advanced.advanced_claims_ii_paper_t1t2_full_solution_squared_norm",
    "MockCert.Mock1Advanced.advanced_claims_ii_paper_t1t2_full_rhs_squared_norm",
    "MockCert.Mock1Advanced.advanced_claims_ii_paper_t1t2_full_pair_targets",
    "MockCert.Mock1Advanced.advanced_claims_ii_paper_t1t2_full_pair_flatten",
    "MockCert.Mock1Advanced.advanced_claims_ii_paper_t1t2_full_pair_squared_norm",
    "MockCert.Mock1Advanced.referenceAdvancedClaimsIIPaperT1T2FullMatrixCertificate",
    "MockCert.Mock1Advanced.advanced_claims_ii_appell_lerch_ridge_index_table",
    "MockCert.Mock1Advanced.advanced_claims_ii_appell_lerch_leading_exponent_table",
    "MockCert.Mock1Advanced.advanced_claims_ii_unary_theta_window_closed",
    "MockCert.Mock1Advanced.advanced_claims_ii_unary_theta_raw_term_table",
    "MockCert.Mock1Advanced.advanced_claims_ii_unary_theta_coefficient_one_eighth",
    "MockCert.Mock1Advanced.advanced_claims_ii_unary_theta_coefficient_nine_eighths",
    "MockCert.Mock1Advanced.advanced_claims_ii_unary_theta_coefficient_twenty_five_eighths",
    "MockCert.Mock1Advanced.advanced_claims_ii_paper_t3_block_sum",
    "MockCert.Mock1Advanced.advanced_claims_ii_paper_t3_completion_correction_scale",
    "MockCert.Mock1Advanced.reference_advanced_claims_ii_paper_t3_block_portfolio",
    "MockCert.Mock1Advanced.advanced_claims_ii_paper_item1_character_table",
    "MockCert.Mock1Advanced.advanced_claims_ii_paper_item1_character_minus_one",
    "MockCert.Mock1Advanced.advanced_claims_ii_paper_item1_expected_nu_parity",
    "MockCert.Mock1Advanced.advanced_claims_ii_paper_item1_character_parity_mismatch",
    "MockCert.Mock1Advanced.advanced_claims_ii_paper_item1_first_symmetric_pair_cancels",
    "MockCert.Mock1Advanced.advanced_claims_ii_paper_k_theta_term_table",
    "MockCert.Mock1Advanced.advanced_claims_ii_paper_k_theta_pair_one_cancels",
    "MockCert.Mock1Advanced.advanced_claims_ii_paper_k_theta_pair_three_cancels",
    "MockCert.Mock1Advanced.advanced_claims_ii_paper_k_theta_window_character_sum",
    "MockCert.Mock1Advanced.advanced_claims_ii_ramanujan_f_prefix_table",
    "MockCert.Mock1Advanced.advanced_claims_ii_negative_twelve_kronecker_table",
    "MockCert.Mock1Advanced.advanced_claims_ii_ramanujan_f_outside_prefix_table",
    "MockCert.Mock1Advanced.advanced_claims_ii_ramanujan_psi_prefix_table",
    "MockCert.Mock1Advanced.advanced_claims_ii_ramanujan_explicit_correction_prefix_table",
    "MockCert.Mock1Advanced.advanced_claims_ii_ramanujan_dictionary_correction_prefix_table",
    "MockCert.Mock1Advanced.advanced_claims_ii_ramanujan_explicit_matches_dictionary",
    "MockCert.Mock1Advanced.advanced_claims_ii_ramanujan_finite_inside_outside_identity",
    "MockCert.Mock1Advanced.advanced_claims_ii_rlf_ramanujan_f_finite_manifest_fields",
    "MockCert.Mock1Advanced.advanced_claims_ii_ramanujan_f_padic_modulus_value",
    "MockCert.Mock1Advanced.advanced_claims_ii_ramanujan_f_padic_denominator_positive",
    "MockCert.Mock1Advanced.advanced_claims_ii_ramanujan_f_padic_raw_prefix",
    "MockCert.Mock1Advanced.advanced_claims_ii_ramanujan_f_padic_residue_table",
    "MockCert.Mock1Advanced.advanced_claims_ii_ramanujan_f_padic_forward_difference_table",
    "MockCert.Mock1Advanced.advanced_claims_ii_ramanujan_f_padic_mahler_coefficient_table",
    "MockCert.Mock1Advanced.advanced_claims_ii_ramanujan_f_padic_interpolation_at",
    "MockCert.Mock1Advanced.advanced_claims_ii_ramanujan_f_padic_interpolation_table",
    "MockCert.Mock1Advanced.advanced_claims_ii_ramanujan_f_padic_worked_table_witness",
    "MockCert.Mock1Advanced.advanced_claims_ii_ramanujan_f_padic_worked_table_mismatch",
    "MockCert.Mock1Advanced.advanced_claims_ii_entropy_crt_free_gate_arithmetic",
    "MockCert.Mock1Advanced.advanced_claims_ii_ramanujan_f_coefficient_two",
)

ALLOWED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})

SOURCE_FORBIDDEN_PATTERNS = {
    "native_decide": re.compile(r"\bnative_decide\b"),
    "decide_plus_native": re.compile(r"\bdecide\s+\+native\b"),
    "Lean.ofReduceBool": re.compile(r"\bLean\.ofReduceBool\b"),
    "sorry": re.compile(r"\bsorry\b"),
    "admit": re.compile(r"\badmit\b"),
    "unsafe": re.compile(r"\bunsafe\b"),
    "global_axiom": re.compile(r"(?m)^\s*axiom\b"),
}

RAW_TRUST_PATTERNS = {
    "native_decide": re.compile(r"\bnative_decide\b"),
    "decide_plus_native": re.compile(r"\bdecide\s+\+native\b"),
    "Lean.ofReduceBool": re.compile(r"\bLean\.ofReduceBool\b"),
}

ARTIFACT_FORBIDDEN = (
    b"Lean.ofReduceBool",
    b"Lean.trustCompiler",
    b"sorryAx",
    b"native_decide",
    b"._native.",
)

PANIC_PATTERNS = (
    "panic!",
    "PANIC",
    "internal compiler error",
    "segmentation fault",
    "core dumped",
    "fatal error",
)

WARNING_HEADER_RE = re.compile(r"(?m)^.*?:\d+:\d+: warning(?:\([^)]*\))?:")
ERROR_HEADER_RE = re.compile(r"(?m)^.*?:\d+:\d+: error(?:\([^)]*\))?:")
MAX_ERRORS_RE = re.compile(r"maximum number of errors", re.IGNORECASE)
SUPPRESSION_RE = re.compile(
    r"(?m)^\s*set_option\s+(?:linter\.|warn\.)[^\s]*\s+false\b.*$"
)

DECL_RE = re.compile(
    r"^\s*(?:(?:private|protected|noncomputable|unsafe|local|scoped)\s+)*"
    r"(?P<kind>theorem|lemma|def|abbrev|opaque|axiom|example|instance|structure|class|inductive)\b"
    r"(?:\s+(?P<name>[^\s(:{\[]+))?"
)
NAMESPACE_RE = re.compile(r"^\s*namespace\s+([^\s]+)")
SECTION_RE = re.compile(r"^\s*section(?:\s+([^\s]+))?")
END_RE = re.compile(r"^\s*end(?:\s+([^\s]+))?\s*(?:--.*)?$")


@dataclass(frozen=True)
class Declaration:
    kind: str
    name: str
    full_name: str
    start_line: int
    header_end_line: int
    header_end_column: int


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_text(text: str) -> str:
    return sha256_bytes(text.encode("utf-8"))


def json_digest(value: object) -> str:
    data = json.dumps(value, ensure_ascii=False, separators=(",", ":")).encode("utf-8")
    return sha256_bytes(data)


def json_write(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(value, ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
        newline="",
    )


def read_utf8(path: Path) -> str:
    with path.open("r", encoding="utf-8", newline="") as handle:
        return handle.read()


def strip_comments_and_strings(source: str) -> str:
    """Blank nested Lean comments and strings while preserving newlines."""

    out: list[str] = []
    index = 0
    depth = 0
    in_string = False
    escaped = False
    while index < len(source):
        if depth:
            if source.startswith("/-", index):
                depth += 1
                out.extend((" ", " "))
                index += 2
            elif source.startswith("-/", index):
                depth -= 1
                out.extend((" ", " "))
                index += 2
            else:
                out.append("\n" if source[index] == "\n" else " ")
                index += 1
        elif in_string:
            char = source[index]
            out.append("\n" if char == "\n" else " ")
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
            index += 1
        elif source.startswith("/-", index):
            depth = 1
            out.extend((" ", " "))
            index += 2
        elif source.startswith("--", index):
            while index < len(source) and source[index] != "\n":
                out.append(" ")
                index += 1
        elif source[index] == '"':
            in_string = True
            out.append(" ")
            index += 1
        else:
            out.append(source[index])
            index += 1
    if depth or in_string:
        raise RuntimeError("unterminated Lean block comment or string")
    return "".join(out)


def source_forbidden_audit(source: str) -> dict[str, object]:
    code = strip_comments_and_strings(source)
    code_counts = {
        name: len(pattern.findall(code))
        for name, pattern in SOURCE_FORBIDDEN_PATTERNS.items()
    }
    raw_trust_counts = {
        name: len(pattern.findall(source))
        for name, pattern in RAW_TRUST_PATTERNS.items()
    }
    suppressions = SUPPRESSION_RE.findall(code)
    return {
        "code_counts": code_counts,
        "raw_trust_counts": raw_trust_counts,
        "warning_suppressions": suppressions,
        "forbidden_code_absolute_zero": not any(code_counts.values()),
        "raw_trust_absolute_zero": not any(raw_trust_counts.values()),
    }


def qualify(namespace: list[str], name: str) -> str:
    if "." in name or not namespace:
        return name
    return ".".join((*namespace, name))


def find_header_end(lines: list[str], start: int, stop: int) -> tuple[int, int]:
    block_depth = 0
    in_string = False
    escaped = False
    for index in range(start - 1, stop):
        text = lines[index]
        masked: list[str] = []
        cursor = 0
        while cursor < len(text):
            ch = text[cursor]
            pair = text[cursor : cursor + 2]
            if block_depth:
                if pair == "/-":
                    block_depth += 1
                    masked.extend("  ")
                    cursor += 2
                elif pair == "-/":
                    block_depth -= 1
                    masked.extend("  ")
                    cursor += 2
                else:
                    masked.append(" ")
                    cursor += 1
            elif in_string:
                masked.append(" ")
                if escaped:
                    escaped = False
                elif ch == "\\":
                    escaped = True
                elif ch == '"':
                    in_string = False
                cursor += 1
            elif pair == "/-":
                block_depth = 1
                masked.extend("  ")
                cursor += 2
            elif pair == "--":
                masked.extend(" " * (len(text) - cursor))
                break
            elif ch == '"':
                in_string = True
                masked.append(" ")
                cursor += 1
            else:
                masked.append(ch)
                cursor += 1
        code = "".join(masked)
        positions = [
            position
            for position in (code.find(":="), code.find(" where"))
            if position >= 0
        ]
        stripped = code.lstrip()
        if stripped.startswith("|"):
            positions.append(len(code) - len(stripped))
        if positions:
            return index + 1, min(positions)
    return start, len(lines[start - 1])


def parse_declarations(source: str) -> list[Declaration]:
    lines = source.splitlines()
    provisional: list[tuple[str, str, str, int]] = []
    frames: list[tuple[str, str | None]] = []
    namespace: list[str] = []
    for line_no, text in enumerate(lines, 1):
        if match := NAMESPACE_RE.match(text):
            name = match.group(1)
            frames.append(("namespace", name))
            namespace.append(name)
            continue
        if match := SECTION_RE.match(text):
            frames.append(("section", match.group(1)))
            continue
        if match := END_RE.match(text):
            requested = match.group(1)
            if requested:
                while frames:
                    kind, name = frames.pop()
                    if kind == "namespace" and namespace:
                        namespace.pop()
                    if name == requested:
                        break
            elif frames:
                kind, _ = frames.pop()
                if kind == "namespace" and namespace:
                    namespace.pop()
            continue
        match = DECL_RE.match(text)
        if not match:
            continue
        kind = match.group("kind")
        name = match.group("name") or f"<anonymous-{kind}@{line_no}>"
        provisional.append((kind, name, qualify(namespace, name), line_no))

    declarations: list[Declaration] = []
    for index, (kind, name, full_name, start) in enumerate(provisional):
        stop = provisional[index + 1][3] - 1 if index + 1 < len(provisional) else len(lines)
        end_line, end_column = find_header_end(lines, start, stop)
        declarations.append(
            Declaration(kind, name, full_name, start, end_line, end_column)
        )
    return declarations


def header_text_from_lines(lines: list[str], declaration: Declaration) -> str:
    start = declaration.start_line - 1
    end = declaration.header_end_line - 1
    if start == end:
        return lines[start][: declaration.header_end_column]
    return "\n".join((*lines[start:end], lines[end][: declaration.header_end_column]))


def header_text(source: str, declaration: Declaration) -> str:
    return header_text_from_lines(source.splitlines(), declaration)


def declaration_snapshot(source: str) -> dict[str, object]:
    lines = source.splitlines()
    declarations = parse_declarations(source)
    sequence = [
        {"kind": declaration.kind, "name": declaration.full_name}
        for declaration in declarations
    ]
    headers = [
        {
            "kind": declaration.kind,
            "name": declaration.full_name,
            "header": header_text_from_lines(lines, declaration),
        }
        for declaration in declarations
    ]
    return {
        "declaration_count": len(declarations),
        "sequence": sequence,
        "sequence_sha256": json_digest(sequence),
        "all_headers_sha256": json_digest(headers),
        "declarations": declarations,
        "headers": headers,
    }


def target_header_snapshot(source: str) -> dict[str, dict[str, object]]:
    lines = source.splitlines()
    declarations = parse_declarations(source)
    by_name: dict[str, list[Declaration]] = {}
    for declaration in declarations:
        by_name.setdefault(declaration.full_name, []).append(declaration)
    result: dict[str, dict[str, object]] = {}
    for target in AFFECTED_TARGETS:
        matches = by_name.get(target, [])
        if len(matches) != 1:
            raise RuntimeError(
                f"affected declaration must occur exactly once: {target}: {len(matches)}"
            )
        declaration = matches[0]
        header = header_text_from_lines(lines, declaration)
        result[target] = {
            "kind": declaration.kind,
            "start_line": declaration.start_line,
            "header_end_line": declaration.header_end_line,
            "header_sha256": sha256_text(header),
            "header": header,
            "explicit_type_syntax_present": ":" in strip_comments_and_strings(header),
        }
    return result


def changed_lines(before: str, after: str) -> list[dict[str, object]]:
    old_lines = before.splitlines()
    new_lines = after.splitlines()
    if len(old_lines) != len(new_lines):
        raise RuntimeError("candidate line count changed")
    return [
        {"line": index, "before": old, "after": new}
        for index, (old, new) in enumerate(zip(old_lines, new_lines), 1)
        if old != new
    ]


def resolve_source_dir(repo_root: Path) -> Path:
    nested = repo_root / "PrimalitySheafVerification"
    if all((nested / f"{module}.lean").is_file() for module in ROOT_MODULES):
        return nested
    if all((repo_root / f"{module}.lean").is_file() for module in ROOT_MODULES):
        return repo_root
    raise FileNotFoundError("could not locate exact Spt1 and Mock1_Advanced sources")


def resolve_module_source(repo_root: Path, module: str) -> Path:
    candidates = (
        repo_root / "PrimalitySheafVerification" / f"{module}.lean",
        repo_root / f"{module}.lean",
    )
    for candidate in candidates:
        if candidate.is_file():
            return candidate
    raise FileNotFoundError(f"source for module {module} not found")


def exact_artifact_paths(repo_root: Path, module: str) -> tuple[Path, Path, Path]:
    resolved_repo = repo_root.resolve()
    unresolved_base = (
        resolved_repo
        / ".lake"
        / "build"
        / "lib"
        / "lean"
        / "PrimalitySheafVerification"
    )
    # Refuse to traverse a symlinked build-path component.  GitHub's normal
    # .lake/build tree is made of directories; a link here would make an exact
    # artifact deletion resolve outside the intended checkout.
    current = resolved_repo
    for component in (".lake", "build", "lib", "lean", "PrimalitySheafVerification"):
        current = current / component
        if current.is_symlink():
            raise RuntimeError(f"refusing symlinked build-path component: {current}")
    base = unresolved_base.resolve()
    if base != unresolved_base or resolved_repo not in base.parents:
        raise RuntimeError(f"resolved artifact base escaped the checkout: {base}")
    return (
        base / f"{module}.olean",
        base / f"{module}.ilean",
        base / f"{module}.olean.private",
    )


def delete_exact_artifacts(repo_root: Path, module: str) -> dict[str, object]:
    targets = exact_artifact_paths(repo_root, module)
    expected_base = targets[0].parent
    deleted: list[dict[str, object]] = []
    for target in targets:
        resolved_parent = target.parent.resolve()
        if resolved_parent != expected_base:
            raise RuntimeError(f"refusing artifact deletion outside exact build dir: {target}")
        if target.is_symlink():
            raise RuntimeError(f"refusing to delete symlink artifact: {target}")
        if target.exists():
            if not target.is_file():
                raise RuntimeError(f"expected artifact is not a regular file: {target}")
            data = target.read_bytes()
            deleted.append(
                {"path": str(target), "bytes": len(data), "sha256": sha256_bytes(data)}
            )
            target.unlink()
        if target.exists():
            raise RuntimeError(f"artifact deletion did not complete: {target}")
    expected_base.mkdir(parents=True, exist_ok=True)
    return {
        "targets": [str(path) for path in targets],
        "deleted": deleted,
        "all_absent_after_delete": all(not path.exists() for path in targets),
    }


def artifact_metric(path: Path) -> dict[str, object]:
    if not path.is_file():
        return {
            "path": str(path),
            "exists": False,
            "bytes": 0,
            "sha256": None,
            "forbidden_ascii_counts": {
                token.decode("ascii"): 0 for token in ARTIFACT_FORBIDDEN
            },
            "forbidden_absolute_zero": False,
        }
    data = path.read_bytes()
    forbidden = {
        token.decode("ascii"): data.count(token) for token in ARTIFACT_FORBIDDEN
    }
    return {
        "path": str(path),
        "exists": True,
        "bytes": len(data),
        "sha256": sha256_bytes(data),
        "forbidden_ascii_counts": forbidden,
        "forbidden_absolute_zero": not any(forbidden.values()),
    }


def log_metrics(log: str) -> dict[str, object]:
    warning_headers = WARNING_HEADER_RE.findall(log)
    error_headers = ERROR_HEADER_RE.findall(log)
    panic_counts = {
        pattern: log.lower().count(pattern.lower()) for pattern in PANIC_PATTERNS
    }
    return {
        "warning_header_count": len(warning_headers),
        "error_header_count": len(error_headers),
        "panic_counts": panic_counts,
        "panic_count": sum(panic_counts.values()),
        "max_errors_cap_reached_count": len(MAX_ERRORS_RE.findall(log)),
        "sorry_warning_count": sum(
            log.count(token) for token in ("declaration uses 'sorry'", "sorryAx")
        ),
    }


def lean_root_for(source_path: Path, repo_root: Path) -> Path:
    """Return a module root that actually contains the direct Lean input."""
    resolved_source = source_path.resolve()
    try:
        resolved_source.relative_to(repo_root.resolve())
        return repo_root.resolve()
    except ValueError:
        if resolved_source.parent.name == "PrimalitySheafVerification":
            return resolved_source.parent.parent
        return resolved_source.parent


def direct_compile(
    *,
    label: str,
    module: str,
    source_path: Path,
    repo_root: Path,
    evidence_root: Path,
    max_errors: int,
) -> dict[str, object]:
    compile_root = evidence_root / "compile" / label
    compile_root.mkdir(parents=True, exist_ok=True)
    log_path = compile_root / f"{module}.log"
    source_before = source_path.read_bytes()
    deletion = delete_exact_artifacts(repo_root, module)
    olean, ilean, private = exact_artifact_paths(repo_root, module)
    lean_root = lean_root_for(source_path, repo_root)
    command = [
        "lake",
        "env",
        "lean",
        f"--root={lean_root}",
        f"-DmaxErrors={max_errors}",
        "-o",
        str(olean),
        "-i",
        str(ilean),
        str(source_path),
    ]
    environment = os.environ.copy()
    environment["LEAN_ABORT_ON_PANIC"] = "1"
    started = utc_now()
    start_clock = time.monotonic()
    completed = subprocess.run(
        command,
        cwd=repo_root,
        env=environment,
        text=True,
        encoding="utf-8",
        errors="replace",
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    elapsed = time.monotonic() - start_clock
    log_path.write_text(completed.stdout, encoding="utf-8", newline="")
    logs = log_metrics(completed.stdout)
    artifacts = {
        "olean": artifact_metric(olean),
        "ilean": artifact_metric(ilean),
        "olean_private": artifact_metric(private) if private.exists() else {
            "path": str(private),
            "exists": False,
            "bytes": 0,
            "sha256": None,
            "forbidden_ascii_counts": {
                token.decode("ascii"): 0 for token in ARTIFACT_FORBIDDEN
            },
            "forbidden_absolute_zero": True,
        },
    }
    required_artifacts = (artifacts["olean"], artifacts["ilean"])
    artifact_gate = all(
        artifact["exists"]
        and int(artifact["bytes"]) > 0
        and artifact["forbidden_absolute_zero"]
        for artifact in required_artifacts
    )
    source_after = source_path.read_bytes()
    clean = (
        completed.returncode == 0
        and logs["error_header_count"] == 0
        and logs["panic_count"] == 0
        and logs["max_errors_cap_reached_count"] == 0
        and logs["sorry_warning_count"] == 0
        and artifact_gate
        and source_before == source_after
        and deletion["all_absent_after_delete"]
    )
    return {
        "label": label,
        "module": module,
        "command": command,
        "source_path": str(source_path),
        "lean_root": str(lean_root),
        "source_sha256_before": sha256_bytes(source_before),
        "source_sha256_after": sha256_bytes(source_after),
        "source_unchanged": source_before == source_after,
        "started_utc": started,
        "elapsed_seconds": round(elapsed, 3),
        "exit": completed.returncode,
        **logs,
        "log_path": str(log_path),
        "log_bytes": len(completed.stdout.encode("utf-8")),
        "log_sha256": sha256_text(completed.stdout),
        "deleted_before_compile": deletion,
        "artifacts": artifacts,
        "required_artifact_gate": artifact_gate,
        "clean": clean,
    }


def run_audit_file(
    *,
    label: str,
    source_path: Path,
    repo_root: Path,
    evidence_root: Path,
    max_errors: int,
) -> dict[str, object]:
    audit_root = evidence_root / "audit"
    audit_root.mkdir(parents=True, exist_ok=True)
    olean = audit_root / f"{label}.olean"
    ilean = audit_root / f"{label}.ilean"
    for target in (olean, ilean):
        if target.is_symlink():
            raise RuntimeError(f"refusing to delete symlink audit artifact: {target}")
        if target.exists():
            if not target.is_file():
                raise RuntimeError(f"audit artifact is not a regular file: {target}")
            target.unlink()
    lean_root = lean_root_for(source_path, repo_root)
    command = [
        "lake",
        "env",
        "lean",
        f"--root={lean_root}",
        f"-DmaxErrors={max_errors}",
        "-o",
        str(olean),
        "-i",
        str(ilean),
        str(source_path),
    ]
    environment = os.environ.copy()
    environment["LEAN_ABORT_ON_PANIC"] = "1"
    started = utc_now()
    start_clock = time.monotonic()
    completed = subprocess.run(
        command,
        cwd=repo_root,
        env=environment,
        text=True,
        encoding="utf-8",
        errors="replace",
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    elapsed = time.monotonic() - start_clock
    log_path = audit_root / f"{label}.log"
    log_path.write_text(completed.stdout, encoding="utf-8", newline="")
    logs = log_metrics(completed.stdout)
    artifacts = {"olean": artifact_metric(olean), "ilean": artifact_metric(ilean)}
    clean = (
        completed.returncode == 0
        and logs["error_header_count"] == 0
        and logs["panic_count"] == 0
        and logs["max_errors_cap_reached_count"] == 0
        and logs["sorry_warning_count"] == 0
        and all(
            metric["exists"]
            and int(metric["bytes"]) > 0
            and metric["forbidden_absolute_zero"]
            for metric in artifacts.values()
        )
    )
    return {
        "label": label,
        "command": command,
        "source_path": str(source_path),
        "lean_root": str(lean_root),
        "source_sha256": sha256_bytes(source_path.read_bytes()),
        "started_utc": started,
        "elapsed_seconds": round(elapsed, 3),
        "exit": completed.returncode,
        **logs,
        "log_path": str(log_path),
        "log_bytes": len(completed.stdout.encode("utf-8")),
        "log_sha256": sha256_text(completed.stdout),
        "artifacts": artifacts,
        "clean": clean,
        "log": completed.stdout,
    }


def write_type_audit(path: Path) -> None:
    lines = [
        "import PrimalitySheafVerification.Mock1_Advanced",
        "set_option pp.universes true",
        "set_option pp.explicit true",
        "set_option pp.fullNames true",
        "",
    ]
    lines.extend(f"#check @{target}" for target in AFFECTED_TARGETS)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8", newline="")


def write_axiom_audit(path: Path) -> None:
    lines = ["import PrimalitySheafVerification.Mock1_Advanced", ""]
    lines.extend(f"#print axioms {target}" for target in AFFECTED_TARGETS)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8", newline="")


def type_coverage(log: str) -> dict[str, object]:
    present = [
        target
        for target in AFFECTED_TARGETS
        if re.search(rf"(?m)^@?{re.escape(target)}\s*:", log)
    ]
    missing = sorted(set(AFFECTED_TARGETS) - set(present))
    return {
        "expected_count": len(AFFECTED_TARGETS),
        "present_count": len(present),
        "present": present,
        "missing": missing,
        "exact_coverage": len(present) == len(AFFECTED_TARGETS) and not missing,
    }


def parse_axiom_records(log: str) -> dict[str, list[str]]:
    records: dict[str, list[str]] = {}
    lines = log.splitlines()
    index = 0
    start_re = re.compile(
        r"^'(?P<name>[^']+)' (?P<kind>depends on axioms: \[|does not depend on any axioms)"
    )
    while index < len(lines):
        match = start_re.match(lines[index])
        if not match:
            index += 1
            continue
        name = match.group("name")
        if name in records:
            raise RuntimeError(f"duplicate #print axioms output for {name}")
        if match.group("kind") == "does not depend on any axioms":
            records[name] = []
            index += 1
            continue
        chunk = lines[index].split("[", 1)[1]
        while "]" not in chunk:
            index += 1
            if index >= len(lines):
                raise RuntimeError(f"unterminated #print axioms output for {name}")
            chunk += " " + lines[index].strip()
        payload = chunk.split("]", 1)[0].strip()
        records[name] = [item.strip() for item in payload.split(",") if item.strip()]
        index += 1
    return records


def axiom_coverage(log: str) -> dict[str, object]:
    records = parse_axiom_records(log)
    expected = set(AFFECTED_TARGETS)
    observed = set(records)
    selected = {target: records.get(target, []) for target in AFFECTED_TARGETS}
    union = sorted({axiom for axioms in selected.values() for axiom in axioms})
    disallowed = sorted(set(union) - ALLOWED_AXIOMS)
    missing = sorted(expected - observed)
    unexpected = sorted(observed - expected)
    forbidden_log_counts = {
        token.decode("ascii"): log.count(token.decode("ascii"))
        for token in ARTIFACT_FORBIDDEN
    }
    return {
        "expected_count": len(expected),
        "record_count": len(records),
        "missing": missing,
        "unexpected": unexpected,
        "records": selected,
        "axiom_union": union,
        "allowed_axioms": sorted(ALLOWED_AXIOMS),
        "disallowed_axioms": disallowed,
        "forbidden_log_counts": forbidden_log_counts,
        "exact_coverage": not missing and not unexpected and len(records) == len(expected),
        "allowed_only": not disallowed and not any(forbidden_log_counts.values()),
    }


def version_record(command: list[str], repo_root: Path) -> dict[str, object]:
    completed = subprocess.run(
        command,
        cwd=repo_root,
        text=True,
        encoding="utf-8",
        errors="replace",
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    return {
        "command": command,
        "exit": completed.returncode,
        "output": completed.stdout.strip(),
    }


def compiled_artifacts_forbidden_zero(result: dict[str, object]) -> bool:
    artifacts = result.get("artifacts", {})
    return bool(artifacts) and all(
        bool(metric.get("forbidden_absolute_zero"))
        for metric in artifacts.values()
        if isinstance(metric, dict)
    )


def static_prepare(
    *,
    repo_root: Path,
    evidence_root: Path,
    preparer: Path,
    variant: str,
) -> dict[str, object]:
    source_dir = resolve_source_dir(repo_root)
    candidate_dir = evidence_root / "candidate"
    if candidate_dir.exists():
        raise RuntimeError(f"candidate output already exists; refusing overwrite: {candidate_dir}")
    preparer_log = evidence_root / "preparer.log"
    command = [
        sys.executable,
        str(preparer),
        "--source-dir",
        str(source_dir),
        "--output-dir",
        str(candidate_dir),
        "--variant",
        variant,
    ]
    completed = subprocess.run(
        command,
        cwd=repo_root,
        text=True,
        encoding="utf-8",
        errors="replace",
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    preparer_log.write_text(completed.stdout, encoding="utf-8", newline="")
    if completed.returncode != 0:
        raise RuntimeError(
            f"guarded preparer failed with exit {completed.returncode}; see {preparer_log}"
        )
    manifest_path = candidate_dir / "MANIFEST.json"
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    if manifest.get("variant") != variant:
        raise RuntimeError("preparer manifest variant mismatch")
    if manifest.get("total_replacements") != 61:
        raise RuntimeError("preparer did not report exactly 61 code replacements")
    if manifest.get("total_documentation_edits") != 1:
        raise RuntimeError("preparer did not report exactly one documentation normalization")

    file_policies: dict[str, object] = {}
    all_static = True
    for module in ROOT_MODULES:
        source_path = source_dir / f"{module}.lean"
        candidate_path = candidate_dir / f"{module}.lean"
        source = read_utf8(source_path)
        candidate = read_utf8(candidate_path)
        source_sha = sha256_text(source)
        candidate_sha = sha256_text(candidate)
        source_snapshot = declaration_snapshot(source)
        candidate_snapshot = declaration_snapshot(candidate)
        source_targets = (
            target_header_snapshot(source) if module == "Mock1_Advanced" else {}
        )
        candidate_targets = (
            target_header_snapshot(candidate) if module == "Mock1_Advanced" else {}
        )
        edits = changed_lines(source, candidate)
        source_audit = source_forbidden_audit(source)
        candidate_audit = source_forbidden_audit(candidate)
        identity_gate = source_sha == SOURCE_SHA256[module]
        candidate_sha_gate = candidate_sha == CANDIDATE_SHA256[variant][module]
        sequence_gate = source_snapshot["sequence"] == candidate_snapshot["sequence"]
        header_gate = source_snapshot["headers"] == candidate_snapshot["headers"]
        target_header_gate = source_targets == candidate_targets
        explicit_type_gate = all(
            bool(row["explicit_type_syntax_present"])
            for row in candidate_targets.values()
        )
        expected_edit_count = 2 if module == "Spt1" else 60
        edit_count_gate = len(edits) == expected_edit_count
        forbidden_gate = (
            candidate_audit["forbidden_code_absolute_zero"]
            and candidate_audit["raw_trust_absolute_zero"]
        )
        suppression_unchanged_gate = (
            source_audit["warning_suppressions"]
            == candidate_audit["warning_suppressions"]
        )
        gates = {
            "source_identity": identity_gate,
            "candidate_sha256": candidate_sha_gate,
            "line_count_preserved": len(source.splitlines()) == len(candidate.splitlines()),
            "exact_changed_line_count": edit_count_gate,
            "declaration_sequence_identical": sequence_gate,
            "all_declaration_headers_identical": header_gate,
            "affected_target_headers_identical": target_header_gate,
            "affected_targets_have_explicit_type_syntax": explicit_type_gate,
            "candidate_forbidden_absolute_zero": forbidden_gate,
            "warning_suppression_multiset_unchanged": suppression_unchanged_gate,
        }
        all_static = all_static and all(gates.values())
        file_policies[module] = {
            "source_path": str(source_path),
            "candidate_path": str(candidate_path),
            "source_sha256": source_sha,
            "expected_source_sha256": SOURCE_SHA256[module],
            "candidate_sha256": candidate_sha,
            "expected_candidate_sha256": CANDIDATE_SHA256[variant][module],
            "source_line_count": len(source.splitlines()),
            "candidate_line_count": len(candidate.splitlines()),
            "changed_lines": edits,
            "source_forbidden": source_audit,
            "candidate_forbidden": candidate_audit,
            "pre_declaration_sequence": source_snapshot["sequence"],
            "post_declaration_sequence": candidate_snapshot["sequence"],
            "pre_sequence_sha256": source_snapshot["sequence_sha256"],
            "post_sequence_sha256": candidate_snapshot["sequence_sha256"],
            "pre_all_headers_sha256": source_snapshot["all_headers_sha256"],
            "post_all_headers_sha256": candidate_snapshot["all_headers_sha256"],
            "pre_affected_headers": source_targets,
            "post_affected_headers": candidate_targets,
            "gates": gates,
            "all_static_gates_pass": all(gates.values()),
        }
    policy = {
        "variant": variant,
        "preparer_command": command,
        "preparer_exit": completed.returncode,
        "preparer_sha256": sha256_bytes(preparer.read_bytes()),
        "preparer_manifest": manifest,
        "source_dir": str(source_dir),
        "candidate_dir": str(candidate_dir),
        "affected_target_count": len(AFFECTED_TARGETS),
        "header_type_policy": {
            "source_vs_candidate_declaration_sequence": "must be byte-for-byte identical as parsed kind/name rows",
            "source_vs_candidate_headers": "every parsed declaration header must be byte-for-byte identical",
            "affected_declarations": "all 58 must occur once and retain an identical explicit type-bearing header",
            "post_elaboration": "after both roots compile, #check @target must cover all 58 declarations",
            "baseline_execution": "forbidden baseline is not compiled; exact source headers are the pre-state",
        },
        "files": file_policies,
        "all_static_gates_pass": all_static,
    }
    json_write(evidence_root / "declaration-header-type-policy.json", policy)
    return policy


def main() -> int:
    if len(AFFECTED_TARGETS) != 58 or len(set(AFFECTED_TARGETS)) != 58:
        raise RuntimeError("affected target policy must contain exactly 58 unique declarations")

    parser = argparse.ArgumentParser()
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--preparer", type=Path, required=True)
    parser.add_argument("--variant", choices=("kernel", "elab"), required=True)
    parser.add_argument("--max-errors", type=int, default=160)
    parser.add_argument(
        "--prepare-only",
        action="store_true",
        help="run only guarded materialization and static policy checks; never invoke Lean/Lake",
    )
    args = parser.parse_args()
    if args.max_errors != 160:
        raise RuntimeError(f"strict matrix requires maxErrors=160, got {args.max_errors}")

    repo_root = args.repo_root.resolve()
    evidence_root = args.out.resolve()
    preparer = args.preparer.resolve()
    if not preparer.is_file():
        raise FileNotFoundError(f"preparer not found: {preparer}")
    source_dir = resolve_source_dir(repo_root).resolve()
    if evidence_root == source_dir or source_dir in evidence_root.parents:
        raise RuntimeError("evidence root must not equal or be nested beneath the source directory")
    if evidence_root.exists():
        if not evidence_root.is_dir():
            raise RuntimeError("evidence path exists and is not a directory")
        if any(evidence_root.iterdir()):
            raise RuntimeError("evidence directory must be empty")
    else:
        evidence_root.mkdir(parents=True)

    static_policy = static_prepare(
        repo_root=repo_root,
        evidence_root=evidence_root,
        preparer=preparer,
        variant=args.variant,
    )
    common = {
        "schema": "codex-native-decide-trust-matrix-v1",
        "matrix_variant": args.variant,
        "replacement": "decide +kernel" if args.variant == "kernel" else "decide",
        "max_errors": args.max_errors,
        "root_modules": list(ROOT_MODULES),
        "downstream_modules": list(DOWNSTREAM_MODULES),
        "affected_target_count": len(AFFECTED_TARGETS),
        "static_policy_path": str(evidence_root / "declaration-header-type-policy.json"),
        "static_policy_gate": static_policy["all_static_gates_pass"],
        "candidate_forbidden_absolute_zero": all(
            row["candidate_forbidden"]["forbidden_code_absolute_zero"]
            and row["candidate_forbidden"]["raw_trust_absolute_zero"]
            for row in static_policy["files"].values()
        ),
    }

    if args.prepare_only:
        passed = bool(common["static_policy_gate"] and common["candidate_forbidden_absolute_zero"])
        metric = {
            **common,
            "classification": "PREPARED_STATIC_PASS" if passed else "STATIC_TRUST_BLOCKED",
            "prepare_only": True,
            "lean_lake_git_github_invoked": False,
            "root_direct": [],
            "post_type_audit": None,
            "post_axiom_audit": None,
            "downstream_started": False,
            "downstream_direct": [],
            "all_gates_pass": passed,
            "candidate_is_compile_evidence": False,
        }
        json_write(evidence_root / "METRIC.json", metric)
        print(json.dumps(metric, ensure_ascii=False, indent=2))
        return 0 if passed else 1

    lean_version = version_record(["lake", "env", "lean", "--version"], repo_root)
    lake_version = version_record(["lake", "--version"], repo_root)
    candidate_dir = Path(static_policy["candidate_dir"])
    candidate_module_root = evidence_root / "candidate-module-root"
    candidate_source_dir = candidate_module_root / "PrimalitySheafVerification"
    if candidate_module_root.exists():
        raise RuntimeError(
            f"candidate module root already exists; refusing overwrite: {candidate_module_root}"
        )
    candidate_source_dir.mkdir(parents=True)
    for module in ROOT_MODULES:
        source = candidate_dir / f"{module}.lean"
        staged = candidate_source_dir / f"{module}.lean"
        staged.write_bytes(source.read_bytes())
        if staged.read_bytes() != source.read_bytes():
            raise RuntimeError(f"candidate staging changed source bytes: {module}")
    root_results = [
        direct_compile(
            label=f"root-{module}",
            module=module,
            source_path=candidate_source_dir / f"{module}.lean",
            repo_root=repo_root,
            evidence_root=evidence_root,
            max_errors=args.max_errors,
        )
        for module in ROOT_MODULES
    ]
    roots_both_pass = (
        bool(common["static_policy_gate"])
        and bool(common["candidate_forbidden_absolute_zero"])
        and all(result["clean"] for result in root_results)
    )

    type_result: dict[str, object] | None = None
    axiom_result: dict[str, object] | None = None
    type_gate = False
    axiom_gate = False
    if roots_both_pass:
        type_source = evidence_root / "audit" / "AffectedNativeDecideTypes.lean"
        axiom_source = evidence_root / "audit" / "AffectedNativeDecideAxioms.lean"
        type_source.parent.mkdir(parents=True, exist_ok=True)
        write_type_audit(type_source)
        write_axiom_audit(axiom_source)
        type_result = run_audit_file(
            label="affected-types",
            source_path=type_source,
            repo_root=repo_root,
            evidence_root=evidence_root,
            max_errors=args.max_errors,
        )
        type_log = str(type_result.pop("log"))
        type_result["coverage"] = type_coverage(type_log)
        type_gate = bool(type_result["clean"] and type_result["coverage"]["exact_coverage"])
        axiom_result = run_audit_file(
            label="affected-axioms",
            source_path=axiom_source,
            repo_root=repo_root,
            evidence_root=evidence_root,
            max_errors=args.max_errors,
        )
        axiom_log = str(axiom_result.pop("log"))
        axiom_result["coverage"] = axiom_coverage(axiom_log)
        axiom_gate = bool(
            axiom_result["clean"]
            and axiom_result["coverage"]["exact_coverage"]
            and axiom_result["coverage"]["allowed_only"]
        )
        json_write(evidence_root / "audit" / "affected-type-coverage.json", type_result["coverage"])
        json_write(evidence_root / "audit" / "affected-axiom-coverage.json", axiom_result["coverage"])

    downstream_results: list[dict[str, object]] = []
    downstream_gate_open = roots_both_pass and type_gate and axiom_gate
    if downstream_gate_open:
        for module in DOWNSTREAM_MODULES:
            downstream_results.append(
                direct_compile(
                    label=f"downstream-{module}",
                    module=module,
                    source_path=resolve_module_source(repo_root, module),
                    repo_root=repo_root,
                    evidence_root=evidence_root,
                    max_errors=args.max_errors,
                )
            )
    downstream_all_pass = bool(downstream_gate_open and downstream_results) and all(
        result["clean"] for result in downstream_results
    )

    root_artifact_trust_gate = all(
        compiled_artifacts_forbidden_zero(result) for result in root_results
    )
    post_audit_artifact_trust_gate = bool(type_result and axiom_result) and all(
        compiled_artifacts_forbidden_zero(result)
        for result in (type_result, axiom_result)
    )
    downstream_artifact_trust_gate = bool(downstream_results) and all(
        compiled_artifacts_forbidden_zero(result) for result in downstream_results
    )

    source_dir = resolve_source_dir(repo_root)
    source_unchanged = {
        module: sha256_bytes((source_dir / f"{module}.lean").read_bytes())
        == SOURCE_SHA256[module]
        for module in ROOT_MODULES
    }
    gates = {
        "static_policy": bool(common["static_policy_gate"]),
        "candidate_forbidden_absolute_zero": bool(common["candidate_forbidden_absolute_zero"]),
        "root_Spt1_direct_clean": root_results[0]["clean"],
        "root_Mock1_Advanced_direct_clean": root_results[1]["clean"],
        "root_artifacts_forbidden_absolute_zero": root_artifact_trust_gate,
        "both_roots_pass_before_post_audits": roots_both_pass,
        "affected_58_type_check_exact": type_gate,
        "affected_58_axiom_records_exact_and_allowed_only": axiom_gate,
        "post_audit_artifacts_forbidden_absolute_zero": post_audit_artifact_trust_gate,
        "downstream_started_only_after_both_roots_and_audits": (
            bool(downstream_results) == downstream_gate_open
        ),
        "all_downstream_direct_clean": downstream_all_pass,
        "downstream_artifacts_forbidden_absolute_zero": downstream_artifact_trust_gate,
        "checked_in_root_sources_unchanged": all(source_unchanged.values()),
    }
    all_gates_pass = all(gates.values())
    if all_gates_pass:
        classification = "TRUST_REPAIR_PASS"
    elif not common["static_policy_gate"] or not common["candidate_forbidden_absolute_zero"]:
        classification = "STATIC_TRUST_BLOCKED"
    elif not roots_both_pass:
        classification = "ROOT_DIRECT_COMPILE_FAILURE"
    elif not type_gate or not axiom_gate:
        classification = "POST_ELAB_TRUST_FAILURE"
    else:
        classification = "DOWNSTREAM_DIRECT_COMPILE_FAILURE"

    metric = {
        **common,
        "classification": classification,
        "prepare_only": False,
        "lean_version": lean_version,
        "lake_version": lake_version,
        "root_direct": root_results,
        "both_roots_pass": roots_both_pass,
        "post_type_audit": type_result,
        "post_axiom_audit": axiom_result,
        "downstream_gate_open": downstream_gate_open,
        "downstream_started": bool(downstream_results),
        "downstream_direct": downstream_results,
        "downstream_all_pass": downstream_all_pass,
        "checked_in_source_unchanged": source_unchanged,
        "gates": gates,
        "all_gates_pass": all_gates_pass,
        "candidate_is_compile_evidence": all_gates_pass,
    }
    json_write(evidence_root / "METRIC.json", metric)
    print(json.dumps(metric, ensure_ascii=False, indent=2))
    return 0 if all_gates_pass else 1


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as error:  # ensure a concise error is visible in CI logs
        print(f"native_decide trust runner failed: {type(error).__name__}: {error}", file=sys.stderr)
        raise
