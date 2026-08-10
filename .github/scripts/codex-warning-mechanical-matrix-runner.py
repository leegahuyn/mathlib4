#!/usr/bin/env python3
"""Isolated direct-Lean runner for the mechanical warning candidate matrix.

Intended repository path when promoted for CI:
  .github/scripts/codex-warning-mechanical-matrix-runner.py

This runner never edits checked-in sources.  It validates the checked-in blob,
materializes one candidate beneath an evidence directory, directly compiles the
baseline and candidate, and compares their warning multisets.  Warning-zero is
*not* the gate here: the exact expected reductions and zero new signatures are.
The absolute trust/forbidden gate remains zero and is never relaxed.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
from collections import Counter
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Iterable


WARNING_RE = re.compile(
    r"^(?P<path>.*\.lean):(?P<line>\d+):(?P<column>\d+): "
    r"warning(?:\([^)]*\))?: ?(?P<head>.*)$"
)
ERROR_RE = re.compile(
    r"^(?P<path>.*\.lean):(?P<line>\d+):(?P<column>\d+): "
    r"error(?:\([^)]*\))?: ?(?P<head>.*)$"
)
OPTION_RE = re.compile(r"set_option\s+([^\s`]+)")

OPTION_CATEGORY = {
    "linter.unusedVariables": "unusedVariables",
    "linter.unusedSectionVars": "unusedSectionVars",
    "linter.unusedSimpArgs": "unusedSimpArgs",
    "linter.unnecessarySimpa": "unnecessarySimpa",
    "linter.unnecessarySeqFocus": "unnecessarySeqFocus",
    "linter.unusedTactic": "unusedTactic",
    "linter.unreachableTactic": "unreachable",
    "linter.defProp": "defProp",
    "linter.overlappingInstances": "overlap",
    "linter.checkUnivs": "checkUnivs",
    "warn.classDefReducibility": "classReducibility",
    "linter.style.haveILetI": "haveILetI",
}

FORBIDDEN_PATTERNS = {
    "sorry": re.compile(r"\bsorry\b"),
    "admit": re.compile(r"\badmit\b"),
    "new_global_axiom": re.compile(r"(?m)^\s*axiom\b"),
    "unsafe": re.compile(r"\bunsafe\b"),
    "native_decide": re.compile(r"\bnative_decide\b"),
    "Lean.ofReduceBool": re.compile(r"\bLean\.ofReduceBool\b"),
}

SUPPRESSION_RE = re.compile(
    r"set_option\s+(?:linter\.|warn\.classDefReducibility)[^\s]*\s+false"
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


@dataclass
class ParsedWarning:
    path: str
    line: int
    column: int
    category: str
    subject: str
    raw_head: str
    raw_block: str

    @property
    def signature(self) -> tuple[str, str]:
        return self.category, self.subject


def json_write(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git_blob_sha1(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode("ascii") + b"\0" + data).hexdigest()


def stable_decl_name(name: str) -> str:
    return re.sub(r"@\d+>", ">", name)


def qualify(namespace: list[str], name: str) -> str:
    if "." in name or not namespace:
        return name
    return ".".join((*namespace, name))


def find_header_end(lines: list[str], start: int, stop: int) -> tuple[int, int]:
    in_block_comment = 0
    for index in range(start - 1, stop):
        text = lines[index]
        masked: list[str] = []
        cursor = 0
        while cursor < len(text):
            if cursor + 1 < len(text) and text[cursor : cursor + 2] == "/-":
                in_block_comment += 1
                masked.extend("  ")
                cursor += 2
            elif cursor + 1 < len(text) and text[cursor : cursor + 2] == "-/" and in_block_comment:
                in_block_comment -= 1
                masked.extend("  ")
                cursor += 2
            elif in_block_comment:
                masked.append(" ")
                cursor += 1
            elif cursor + 1 < len(text) and text[cursor : cursor + 2] == "--":
                masked.extend(" " * (len(text) - cursor))
                break
            else:
                masked.append(text[cursor])
                cursor += 1
        code = "".join(masked)
        positions = [position for position in (code.find(":="), code.find(" where")) if position >= 0]
        stripped = code.lstrip()
        if stripped.startswith("|"):
            positions.append(len(code) - len(stripped))
        if positions:
            return index + 1, min(positions)
    return start, len(lines[start - 1])


def parse_declarations(lines: list[str]) -> list[Declaration]:
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
        declarations.append(Declaration(kind, name, full_name, start, end_line, end_column))
    return declarations


def declaration_header_text(lines: list[str], declaration: Declaration) -> str:
    start = declaration.start_line - 1
    end = declaration.header_end_line - 1
    if start == end:
        return lines[start][: declaration.header_end_column]
    return "\n".join([*lines[start:end], lines[end][: declaration.header_end_column]])


def header_manifest(source: str) -> dict[str, object]:
    lines = source.splitlines()
    declarations = parse_declarations(lines)
    sequence = [(decl.kind, stable_decl_name(decl.full_name)) for decl in declarations]
    all_headers = [
        (decl.kind, stable_decl_name(decl.full_name), declaration_header_text(lines, decl))
        for decl in declarations
    ]
    theorem_headers = [row for row in all_headers if row[0] in {"theorem", "lemma"}]

    def digest(value: object) -> str:
        encoded = json.dumps(value, ensure_ascii=False, separators=(",", ":")).encode("utf-8")
        return sha256_bytes(encoded)

    return {
        "declaration_count": len(sequence),
        "declaration_sequence_sha256": digest(sequence),
        "all_declaration_headers_sha256": digest(all_headers),
        "theorem_lemma_count": len(theorem_headers),
        "theorem_lemma_headers_sha256": digest(theorem_headers),
    }


def strip_comments_and_strings(source: str) -> str:
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
        raise RuntimeError("unterminated comment or string")
    return "".join(out)


def forbidden_audit(source: str) -> dict[str, object]:
    code = strip_comments_and_strings(source)
    original_lines = source.splitlines()
    result: dict[str, object] = {}
    for label, pattern in FORBIDDEN_PATTERNS.items():
        occurrences = []
        for match in pattern.finditer(code):
            line = code.count("\n", 0, match.start()) + 1
            occurrences.append(
                {
                    "line": line,
                    "token": match.group(0),
                    "source": original_lines[line - 1].strip() if line <= len(original_lines) else "",
                }
            )
        result[label] = {"count": len(occurrences), "occurrences": occurrences}
    return result


def forbidden_counts(audit: dict[str, object]) -> dict[str, int]:
    return {label: int(value["count"]) for label, value in audit.items()}


def apply_manifest_edits(source: str, edits: list[dict]) -> str:
    had_final_newline = source.endswith("\n")
    lines = source.splitlines()
    grouped: dict[int, list[dict]] = {}
    for edit in edits:
        grouped.setdefault(int(edit["line"]), []).append(edit)
    for line_no in sorted(grouped, reverse=True):
        if line_no < 1 or line_no > len(lines):
            raise RuntimeError(f"edit line out of range: {line_no}")
        same_line = grouped[line_no]
        remove = [edit for edit in same_line if edit["remove_line"]]
        if remove:
            if len(remove) != 1 or len(same_line) != 1:
                raise RuntimeError(f"conflicting whole-line edit at {line_no}")
            if lines[line_no - 1] != remove[0]["expected"]:
                raise RuntimeError(f"whole-line guard mismatch at {line_no}")
            del lines[line_no - 1]
            continue
        original = lines[line_no - 1]
        for edit in same_line:
            start, end = int(edit["start"]), int(edit["end"])
            if original[start:end] != edit["expected"]:
                raise RuntimeError(
                    f"span guard mismatch at {line_no}:{start}-{end}: "
                    f"{original[start:end]!r} != {edit['expected']!r}"
                )
        ordered = sorted(same_line, key=lambda item: (int(item["start"]), int(item["end"])), reverse=True)
        prior_start = len(original) + 1
        text = original
        for edit in ordered:
            start, end = int(edit["start"]), int(edit["end"])
            if end > prior_start:
                raise RuntimeError(f"overlapping edits at line {line_no}")
            text = text[:start] + edit["replacement"] + text[end:]
            prior_start = start
        lines[line_no - 1] = text
    candidate = "\n".join(lines) + ("\n" if had_final_newline else "")
    return candidate


def category_for(block: str) -> str:
    if match := OPTION_RE.search(block):
        return OPTION_CATEGORY.get(match.group(1), match.group(1))
    lowered = block.lower()
    if "deprecated" in lowered:
        return "deprecation"
    if "unreachable" in lowered:
        return "unreachable"
    if "constructor" in lowered and "variable" in lowered:
        return "constructorNameAsVariable"
    if "rcases" in lowered and "unused" in lowered:
        return "unusedRCasesPattern"
    return "other"


def subject_for(category: str, block: str, raw_head: str) -> str:
    patterns = {
        "unusedVariables": r"Variable name `([^`]+)` is not explicitly referenced",
        "unusedSimpArgs": r"This simp argument is unused:\s*\n\s*(.+)",
        "unusedTactic": r"warning(?:\([^)]*\))?: '(.+)' tactic does nothing",
        "unreachable": r"warning(?:\([^)]*\))?: (.+) tactic is unreachable",
        "unusedSectionVars": r"unused in theorem `([^`]+)`",
        "defProp": r"Definition `([^`]+)` is a proposition",
        "classReducibility": r"Definition `([^`]+)` of class type",
        "overlap": r"instance `([^`]+)`",
        "checkUnivs": r"declaration `([^`]+)`",
    }
    if category == "deprecation":
        match = re.search(r"`([^`]+)` has been deprecated", block)
        if match:
            return match.group(1)
        match = re.search(r"'([^']+)' has been deprecated", block)
        if match:
            return match.group(1)
    if pattern := patterns.get(category):
        if match := re.search(pattern, block):
            return re.sub(r"\s+", " ", match.group(1)).strip()
    if category == "unnecessarySimpa":
        return "simpa"
    if category == "unnecessarySeqFocus":
        return "<;>"
    return re.sub(r"\s+", " ", raw_head).strip() or "<empty-head>"


def parse_warnings(log: str) -> list[ParsedWarning]:
    lines = log.splitlines()
    starts = [index for index, line in enumerate(lines) if WARNING_RE.match(line)]
    parsed: list[ParsedWarning] = []
    for ordinal, index in enumerate(starts):
        end = starts[ordinal + 1] if ordinal + 1 < len(starts) else len(lines)
        block = "\n".join(lines[index:end]).rstrip()
        match = WARNING_RE.match(lines[index])
        assert match is not None
        category = category_for(block)
        parsed.append(
            ParsedWarning(
                path=match.group("path"),
                line=int(match.group("line")),
                column=int(match.group("column")),
                category=category,
                subject=subject_for(category, block, match.group("head")),
                raw_head=match.group("head"),
                raw_block=block,
            )
        )
    return parsed


def counter_json(counter: Counter) -> list[dict[str, object]]:
    return [
        {"category": key[0], "subject": key[1], "count": count}
        for key, count in sorted(counter.items())
        if count
    ]


def category_counter(warnings: Iterable[ParsedWarning]) -> Counter:
    return Counter(warning.category for warning in warnings)


def run_version(command: list[str], cwd: Path) -> dict[str, object]:
    completed = subprocess.run(command, cwd=cwd, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    return {"command": command, "exit": completed.returncode, "output": completed.stdout.strip()}


def direct_compile(
    *,
    label: str,
    source_path: Path,
    repo_root: Path,
    module: str,
    evidence_root: Path,
) -> dict[str, object]:
    compile_root = evidence_root / label
    compile_root.mkdir(parents=True, exist_ok=True)
    olean = compile_root / f"{module}.olean"
    ilean = compile_root / f"{module}.ilean"
    log_path = compile_root / f"{module}.log"
    project_output = repo_root / ".lake" / "build" / "lib" / "lean" / "PrimalitySheafVerification"
    deleted = []
    for path in (
        project_output / f"{module}.olean",
        project_output / f"{module}.ilean",
        project_output / f"{module}.olean.private",
        olean,
        ilean,
    ):
        if path.is_file():
            path.unlink()
            deleted.append(str(path))
    command = ["lake", "env", "lean", str(source_path), "-o", str(olean), "-i", str(ilean)]
    environment = os.environ.copy()
    environment["LEAN_ABORT_ON_PANIC"] = "1"
    completed = subprocess.run(
        command,
        cwd=repo_root,
        env=environment,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    log_path.write_text(completed.stdout, encoding="utf-8")
    warnings = parse_warnings(completed.stdout)
    errors = [line for line in completed.stdout.splitlines() if ERROR_RE.match(line)]
    panic_patterns = [
        "PANIC",
        "segmentation fault",
        "stack overflow",
        "maximum number of errors",
    ]
    return {
        "label": label,
        "command": command,
        "source_path": str(source_path),
        "deleted_before_compile": deleted,
        "exit": completed.returncode,
        "error_header_count": len(errors),
        "error_headers": errors,
        "warning_header_count": len(warnings),
        "warning_by_category": dict(sorted(category_counter(warnings).items())),
        "sorry_warning_count": sum(
            completed.stdout.count(token) for token in ("declaration uses 'sorry'", "sorryAx")
        ),
        "panic_count": sum(completed.stdout.lower().count(pattern.lower()) for pattern in panic_patterns),
        "olean_path": str(olean),
        "olean_bytes": olean.stat().st_size if olean.is_file() else 0,
        "ilean_path": str(ilean),
        "ilean_bytes": ilean.stat().st_size if ilean.is_file() else 0,
        "log_path": str(log_path),
        "warnings": warnings,
    }


def resolve_source(repo_root: Path, repository_path: str, module: str) -> Path:
    normal = repo_root / repository_path
    if normal.is_file():
        return normal
    flat = repo_root / f"{module}.lean"
    if flat.is_file():
        return flat
    raise FileNotFoundError(f"source not found: {normal} or {flat}")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--module", required=True)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--prepare-only", action="store_true", help="validate/materialize without invoking Lean")
    args = parser.parse_args()

    repo_root = args.repo_root.resolve()
    evidence_root = args.out.resolve()
    if evidence_root == repo_root or repo_root in evidence_root.parents:
        raise RuntimeError("evidence/output root must be outside the repository/source root")
    evidence_root.mkdir(parents=True, exist_ok=True)
    manifest = json.loads(args.manifest.resolve().read_text(encoding="utf-8"))
    if manifest.get("schema") != "codex-warning-mechanical-matrix-v1":
        raise RuntimeError("unsupported manifest schema")
    if args.module not in manifest["modules"]:
        raise RuntimeError(f"module not in manifest: {args.module}")
    expected = manifest["modules"][args.module]
    source_path = resolve_source(repo_root, expected["repository_path"], args.module)
    source_data = source_path.read_bytes()
    source = source_data.decode("utf-8")

    source_checks = {
        "sha256": sha256_bytes(source_data),
        "expected_sha256": expected["source_sha256"],
        "git_blob_sha1": git_blob_sha1(source_data),
        "expected_git_blob_sha1": expected["source_git_blob_sha1"],
        "bytes": len(source_data),
        "expected_bytes": expected["source_bytes"],
        "lines": len(source.splitlines()),
        "expected_lines": expected["source_lines"],
    }
    source_guard = (
        source_checks["sha256"] == source_checks["expected_sha256"]
        and source_checks["git_blob_sha1"] == source_checks["expected_git_blob_sha1"]
        and source_checks["bytes"] == source_checks["expected_bytes"]
        and source_checks["lines"] == source_checks["expected_lines"]
    )
    if not source_guard:
        metric = {
            "classification": "SOURCE_DRIFT",
            "module": args.module,
            "source_guard": False,
            "source_checks": source_checks,
            "all_gates_pass": False,
        }
        json_write(evidence_root / "METRIC.json", metric)
        print(json.dumps(metric, ensure_ascii=False, indent=2))
        return 1

    candidate = apply_manifest_edits(source, expected["edits"])
    candidate_data = candidate.encode("utf-8")
    candidate_checks = {
        "sha256": sha256_bytes(candidate_data),
        "expected_sha256": expected["candidate_sha256"],
        "git_blob_sha1": git_blob_sha1(candidate_data),
        "expected_git_blob_sha1": expected["candidate_git_blob_sha1"],
        "bytes": len(candidate_data),
        "expected_bytes": expected["candidate_bytes"],
        "lines": len(candidate.splitlines()),
        "expected_lines": expected["candidate_lines"],
    }
    candidate_guard = (
        candidate_checks["sha256"] == candidate_checks["expected_sha256"]
        and candidate_checks["git_blob_sha1"] == candidate_checks["expected_git_blob_sha1"]
        and candidate_checks["bytes"] == candidate_checks["expected_bytes"]
        and candidate_checks["lines"] == candidate_checks["expected_lines"]
    )
    source_header_manifest = header_manifest(source)
    candidate_header_manifest = header_manifest(candidate)
    header_gate = (
        source_header_manifest == expected["source_declaration_header_manifest"]
        and candidate_header_manifest == expected["candidate_declaration_header_manifest"]
        and source_header_manifest == candidate_header_manifest
    )
    suppression_added = bool(SUPPRESSION_RE.search(candidate)) and not bool(SUPPRESSION_RE.search(source))
    candidate_trailing_whitespace_lines = [
        line_no for line_no, line in enumerate(candidate.splitlines(), 1) if line.rstrip() != line
    ]
    whitespace_gate = not candidate_trailing_whitespace_lines
    baseline_forbidden = forbidden_audit(source)
    candidate_forbidden = forbidden_audit(candidate)
    candidate_forbidden_counts = forbidden_counts(candidate_forbidden)
    forbidden_gate = not any(candidate_forbidden_counts.values())

    candidate_path = evidence_root / "candidate" / "PrimalitySheafVerification" / f"{args.module}.lean"
    candidate_path.parent.mkdir(parents=True, exist_ok=True)
    candidate_path.write_bytes(candidate_data)
    json_write(
        evidence_root / "declaration-header-manifest.json",
        {
            "source": source_header_manifest,
            "candidate": candidate_header_manifest,
            "identical": header_gate,
        },
    )
    json_write(
        evidence_root / "forbidden-audit.json",
        {
            "baseline": baseline_forbidden,
            "candidate": candidate_forbidden,
            "candidate_absolute_zero": forbidden_gate,
        },
    )

    common = {
        "module": args.module,
        "repository_path": expected["repository_path"],
        "manifest_schema": manifest["schema"],
        "manifest_branch": manifest["branch"],
        "manifest_branch_head_observed_read_only": manifest["branch_head_observed_read_only"],
        "source_guard": source_guard,
        "source_checks": source_checks,
        "candidate_guard": candidate_guard,
        "candidate_checks": candidate_checks,
        "declaration_header_gate": header_gate,
        "source_declaration_header_manifest": source_header_manifest,
        "candidate_declaration_header_manifest": candidate_header_manifest,
        "warning_suppression_added": suppression_added,
        "candidate_trailing_whitespace_lines": candidate_trailing_whitespace_lines,
        "candidate_whitespace_clean": whitespace_gate,
        "forbidden_candidate_counts": candidate_forbidden_counts,
        "forbidden_absolute_zero": forbidden_gate,
        "edit_count": len(expected["edits"]),
        "candidate_path": str(candidate_path),
    }

    if args.prepare_only:
        gates = {
            "source_guard": source_guard,
            "candidate_guard": candidate_guard,
            "declaration_header_gate": header_gate,
            "no_warning_suppression_added": not suppression_added,
            "candidate_whitespace_clean": whitespace_gate,
            "forbidden_absolute_zero": forbidden_gate,
        }
        metric = {
            **common,
            "classification": "PREPARED_NOT_COMPILED" if all(gates.values()) else "PREPARED_TRUST_BLOCKED",
            "prepare_only": True,
            "gates": gates,
            "all_gates_pass": False,
            "candidate_is_pass_evidence": False,
        }
        json_write(evidence_root / "METRIC.json", metric)
        print(json.dumps(metric, ensure_ascii=False, indent=2))
        return 0

    lean_version = run_version(["lake", "env", "lean", "--version"], repo_root)
    lake_version = run_version(["lake", "--version"], repo_root)
    baseline = direct_compile(
        label="baseline",
        source_path=source_path,
        repo_root=repo_root,
        module=args.module,
        evidence_root=evidence_root,
    )
    candidate_run = direct_compile(
        label="candidate-direct",
        source_path=candidate_path,
        repo_root=repo_root,
        module=args.module,
        evidence_root=evidence_root,
    )
    baseline_warnings: list[ParsedWarning] = baseline.pop("warnings")
    candidate_warnings: list[ParsedWarning] = candidate_run.pop("warnings")
    baseline_signatures = Counter(warning.signature for warning in baseline_warnings)
    candidate_signatures = Counter(warning.signature for warning in candidate_warnings)
    expected_removed = Counter(tuple(edit["warning_signature"]) for edit in expected["edits"])
    missing_expected_baseline = expected_removed - baseline_signatures
    expected_candidate_signatures = baseline_signatures.copy()
    expected_candidate_signatures.subtract(expected_removed)
    expected_candidate_signatures = Counter({key: value for key, value in expected_candidate_signatures.items() if value})
    actual_removed = baseline_signatures - candidate_signatures
    actual_added = candidate_signatures - baseline_signatures
    warning_multiset_gate = (
        not missing_expected_baseline
        and candidate_signatures == expected_candidate_signatures
        and actual_removed == expected_removed
        and not actual_added
    )
    baseline_categories = category_counter(baseline_warnings)
    candidate_categories = category_counter(candidate_warnings)
    expected_baseline_categories = Counter(expected["baseline_warning_by_category"])
    expected_candidate_categories = Counter(expected["expected_candidate_warning_by_category"])
    baseline_warning_gate = (
        len(baseline_warnings) == expected["baseline_warning_total"]
        and baseline_categories == expected_baseline_categories
    )
    candidate_warning_gate = (
        len(candidate_warnings) == expected["expected_candidate_warning_total"]
        and candidate_categories == expected_candidate_categories
    )
    new_warning_categories = sorted(set(candidate_categories) - set(baseline_categories))
    new_warning_category_gate = not new_warning_categories

    warning_diff = {
        "baseline_total": len(baseline_warnings),
        "baseline_expected_total": expected["baseline_warning_total"],
        "baseline_by_category": dict(sorted(baseline_categories.items())),
        "baseline_expected_by_category": expected["baseline_warning_by_category"],
        "candidate_total": len(candidate_warnings),
        "candidate_expected_total": expected["expected_candidate_warning_total"],
        "candidate_by_category": dict(sorted(candidate_categories.items())),
        "candidate_expected_by_category": expected["expected_candidate_warning_by_category"],
        "expected_removed_multiset": counter_json(expected_removed),
        "actual_removed_multiset": counter_json(actual_removed),
        "actual_added_multiset": counter_json(actual_added),
        "missing_expected_in_baseline": counter_json(missing_expected_baseline),
        "new_warning_categories": new_warning_categories,
        "exact_expected_multiset_reduction": warning_multiset_gate,
    }
    json_write(evidence_root / "warning-diff.json", warning_diff)
    json_write(evidence_root / "baseline-warnings.json", [asdict(warning) for warning in baseline_warnings])
    json_write(evidence_root / "candidate-warnings.json", [asdict(warning) for warning in candidate_warnings])

    compile_gate = (
        baseline["exit"] == 0
        and candidate_run["exit"] == 0
        and baseline["error_header_count"] == 0
        and candidate_run["error_header_count"] == 0
        and baseline["olean_bytes"] > 0
        and baseline["ilean_bytes"] > 0
        and candidate_run["olean_bytes"] > 0
        and candidate_run["ilean_bytes"] > 0
        and baseline["sorry_warning_count"] == 0
        and candidate_run["sorry_warning_count"] == 0
        and baseline["panic_count"] == 0
        and candidate_run["panic_count"] == 0
    )
    gates = {
        "source_guard": source_guard,
        "candidate_guard": candidate_guard,
        "declaration_header_gate": header_gate,
        "no_warning_suppression_added": not suppression_added,
        "candidate_whitespace_clean": whitespace_gate,
        "baseline_direct_compile_clean": compile_gate,
        "baseline_warning_inventory_exact": baseline_warning_gate,
        "candidate_warning_inventory_exact": candidate_warning_gate,
        "exact_expected_warning_multiset_reduction": warning_multiset_gate,
        "new_warning_categories_zero": new_warning_category_gate,
        "forbidden_absolute_zero": forbidden_gate,
    }
    all_gates_pass = all(gates.values())
    if all_gates_pass:
        classification = "WARNING_MECHANICAL_PASS"
    elif all(value for key, value in gates.items() if key != "forbidden_absolute_zero") and not forbidden_gate:
        classification = "TRUST_BLOCKED"
    elif not compile_gate:
        classification = "DIRECT_COMPILE_FAILURE"
    elif not warning_multiset_gate or not candidate_warning_gate:
        classification = "WARNING_DIFF_MISMATCH"
    else:
        classification = "AUDIT_FAILURE"
    metric = {
        **common,
        "classification": classification,
        "prepare_only": False,
        "lean_version": lean_version,
        "lake_version": lake_version,
        "baseline_direct": baseline,
        "candidate_direct": candidate_run,
        "warning_diff": warning_diff,
        "gates": gates,
        "all_gates_pass": all_gates_pass,
        "warning_zero_required": False,
        "candidate_is_pass_evidence": all_gates_pass,
        "source_sha256_after_compile": sha256_bytes(source_path.read_bytes()),
        "source_unchanged_after_compile": sha256_bytes(source_path.read_bytes()) == expected["source_sha256"],
    }
    metric["gates"]["source_unchanged_after_compile"] = metric["source_unchanged_after_compile"]
    metric["all_gates_pass"] = all(metric["gates"].values())
    metric["candidate_is_pass_evidence"] = metric["all_gates_pass"]
    if not metric["all_gates_pass"] and metric["classification"] == "WARNING_MECHANICAL_PASS":
        metric["classification"] = "AUDIT_FAILURE"
    json_write(evidence_root / "METRIC.json", metric)
    print(json.dumps(metric, ensure_ascii=False, indent=2))
    return 0 if metric["all_gates_pass"] else 1


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as exc:
        print(f"FATAL: {exc}", file=sys.stderr)
        raise
