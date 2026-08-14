#!/usr/bin/env python3
"""Fail-closed helpers for the FA -> QYM -> 13-file verification pipeline.

This script never proves a candidate clean by construction.  It only patches proof
bodies, inventories direct Lean diagnostics, and selects candidates from measured
artifacts.  Clean status always comes from direct Lean exit zero plus zero parsed
errors under a non-truncated diagnostic log.
"""

from __future__ import annotations

import argparse
import collections
import hashlib
import json
import re
import shutil
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable, Sequence


DECL_RE = re.compile(
    r"^(?:protected\s+|private\s+|noncomputable\s+|local\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance|structure|class)\s+"
)
DECL_NAME_RE = re.compile(
    r"^(?:protected\s+|private\s+|noncomputable\s+|local\s+)*"
    r"(?P<kind>theorem|lemma|def|abbrev|instance|structure|class)\s+"
    r"(?P<name>[^\s:(]+)"
)
TRUST_TOKENS = (
    "sorry",
    "admit",
    "axiom",
    "unsafe",
    "native_decide",
    "Lean.ofReduceBool",
)
FA_ERROR_HEADER = re.compile(
    r"(?m)^.*Mock2_FunctionalAnalysis\.lean:(\d+):(\d+): error:(.*)$"
)
QYM_ERROR_HEADER = re.compile(r"(?m)^.*QYM\.lean:(\d+):(\d+): error:(.*)$")


class PipelineError(RuntimeError):
    pass


def die(message: str) -> None:
    raise PipelineError(message)


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_text(text: str) -> str:
    return sha256_bytes(text.encode("utf-8"))


def read_json(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        die(f"expected JSON object: {path}")
    return value


def write_json(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )


def strip_noncode(text: str) -> str:
    """Replace comments and string contents with spaces while preserving newlines."""
    chars = list(text)
    i = 0
    block_depth = 0
    in_string = False
    escaped = False
    while i < len(chars):
        if block_depth:
            if text.startswith("/-", i):
                chars[i] = chars[i + 1] = " "
                block_depth += 1
                i += 2
                continue
            if text.startswith("-/", i):
                chars[i] = chars[i + 1] = " "
                block_depth -= 1
                i += 2
                continue
            if chars[i] != "\n":
                chars[i] = " "
            i += 1
            continue
        if in_string:
            old = chars[i]
            if old != "\n":
                chars[i] = " "
            if escaped:
                escaped = False
            elif old == "\\":
                escaped = True
            elif old == '"':
                in_string = False
            i += 1
            continue
        if text.startswith("/-", i):
            chars[i] = chars[i + 1] = " "
            block_depth = 1
            i += 2
            continue
        if text.startswith("--", i):
            while i < len(chars) and chars[i] != "\n":
                chars[i] = " "
                i += 1
            continue
        if chars[i] == '"':
            chars[i] = " "
            in_string = True
        i += 1
    return "".join(chars)


def trust_counts(text: str) -> dict[str, int]:
    code = strip_noncode(text)
    return {
        token: len(
            re.findall(
                r"(?<![A-Za-z0-9_])"
                + re.escape(token)
                + r"(?![A-Za-z0-9_])",
                code,
            )
        )
        for token in TRUST_TOKENS
    }


def assert_trust_six_zero(text: str) -> dict[str, int]:
    counts = trust_counts(text)
    if any(counts.values()):
        die(f"executable trust token found: {counts}")
    return counts


def declaration_headers(text: str) -> list[str]:
    return [line for line in text.splitlines() if DECL_RE.match(line)]


def locate_declaration(lines: Sequence[str], name: str) -> tuple[int, int]:
    hits = [i for i, line in enumerate(lines) if DECL_RE.match(line) and name in line]
    if len(hits) != 1:
        die(f"declaration {name!r} is not unique: {hits}")
    start = hits[0]
    end = len(lines)
    for i in range(start + 1, len(lines)):
        if DECL_RE.match(lines[i]):
            end = i
            break
    return start, end


def declaration_owner(lines: Sequence[str], line_index: int) -> tuple[int, str]:
    starts = [i for i in range(line_index + 1) if DECL_RE.match(lines[i])]
    if not starts:
        die(f"no declaration owns source line {line_index + 1}")
    start = starts[-1]
    return start, lines[start].strip()


def owner_is_by_proof(lines: Sequence[str], line_index: int) -> bool:
    start, _ = declaration_owner(lines, line_index)
    return ":= by" in "".join(lines[start : line_index + 1])


def parse_error_blocks(log: str, header: re.Pattern[str]) -> list[dict[str, Any]]:
    matches = list(header.finditer(log))
    result: list[dict[str, Any]] = []
    for i, match in enumerate(matches):
        end = matches[i + 1].start() if i + 1 < len(matches) else len(log)
        result.append(
            {
                "line": int(match.group(1)),
                "column": int(match.group(2)),
                "block": log[match.start() : end].strip(),
            }
        )
    return result


def line_prefix(line: str) -> str:
    match = re.match(r"^(\s*(?:·\s*)?)", line)
    if match is None:
        die(f"could not determine tactic indentation: {line!r}")
    return match.group(1)


def newline_of(line: str) -> str:
    return "\n" if line.endswith("\n") else ""


def tactic_body(line: str) -> str:
    stripped = line.lstrip()
    if stripped.startswith("· "):
        stripped = stripped[2:].lstrip()
    return stripped


def nearby_line(
    lines: Sequence[str],
    line_number: int,
    predicate: Any,
    *,
    radius: int = 5,
    require_by_proof: bool = True,
) -> int | None:
    center = max(0, min(len(lines) - 1, line_number - 1))
    offsets = [0]
    for distance in range(1, radius + 1):
        offsets.extend((-distance, distance))
    for offset in offsets:
        index = center + offset
        if not (0 <= index < len(lines)):
            continue
        if require_by_proof and not owner_is_by_proof(lines, index):
            continue
        if predicate(lines[index]):
            return index
    return None


def add_simpa_lemmas(line: str, lemmas: Sequence[str]) -> str:
    missing = [lemma for lemma in lemmas if lemma not in line]
    if not missing:
        return line
    payload = ", ".join(missing)
    if "simpa only [" in line:
        return line.replace("simpa only [", f"simpa only [{payload}, ", 1)
    match = re.search(r"\bsimpa\s*\[", line)
    if match:
        bracket = line.find("[", match.start())
        if bracket >= 0:
            return line[: bracket + 1] + payload + ", " + line[bracket + 1 :]
    if "simpa using" in line:
        return line.replace("simpa using", f"simpa [{payload}] using", 1)
    return line


def apply_diagnostic_repairs(
    text: str,
    diagnostics: str,
    *,
    tendsto: bool,
    interval_tactic: str | None,
    edits: list[dict[str, Any]],
) -> str:
    lines = text.splitlines(keepends=True)
    errors = parse_error_blocks(diagnostics, FA_ERROR_HEADER)
    replacements: dict[int, str] = {}
    for error in errors:
        block = error["block"]
        if tendsto and (
            "Tendsto" in block
            or "Filter.Tendsto" in block
            or "Function.comp" in block
        ):
            index = nearby_line(lines, error["line"], lambda line: "simpa" in line)
            if index is not None:
                old = replacements.get(index, lines[index])
                new = add_simpa_lemmas(old, ("Function.comp_def",))
                if new != old:
                    replacements[index] = new
                    _, owner = declaration_owner(lines, index)
                    edits.append(
                        {
                            "classification": "TENDSTO_ETA_NORMALIZE_FUNCTION_COMP_DEF",
                            "line": index + 1,
                            "owner_header": owner,
                            "diagnostic_line": error["line"],
                            "old": old.rstrip("\n"),
                            "new": new.rstrip("\n"),
                        }
                    )
        if interval_tactic:
            half = any(
                token in block
                for token in ("1 / 2", "2⁻¹", "(2 : ℝ)⁻¹", "0.5")
            )
            inequality = "≤" in block or "<=" in block
            if half and inequality:
                starts = (
                    "exact ",
                    "simpa",
                    "norm_num",
                    "omega",
                    "positivity",
                    "linarith",
                    "nlinarith",
                    "aesop",
                    "ring",
                    "ring_nf",
                )
                index = nearby_line(
                    lines,
                    error["line"],
                    lambda line: tactic_body(line).startswith(starts),
                )
                if index is not None:
                    old = replacements.get(index, lines[index])
                    new = line_prefix(old) + interval_tactic + newline_of(old)
                    if new != old:
                        replacements[index] = new
                        _, owner = declaration_owner(lines, index)
                        edits.append(
                            {
                                "classification": "INTERVAL_HALF_BOUND_ARITHMETIC",
                                "tactic": interval_tactic,
                                "line": index + 1,
                                "owner_header": owner,
                                "diagnostic_line": error["line"],
                                "old": old.rstrip("\n"),
                                "new": new.rstrip("\n"),
                            }
                        )
    for index, replacement in replacements.items():
        lines[index] = replacement
    return "".join(lines)


def patch_w06(text: str, edits: list[dict[str, Any]]) -> str:
    lines = text.splitlines(keepends=True)
    start, end = locate_declaration(lines, "literalStageNegativePlaneWave_differentiable")
    block = "".join(lines[start:end])
    needle = "  letI : AddCommGroup ℂ := Complex.addCommGroup\n"
    if needle not in block:
        return text
    if block.count(needle) != 1:
        die("W06 local Complex AddCommGroup line is not unique")
    replacement = block.replace(needle, "", 1)
    lines[start:end] = replacement.splitlines(keepends=True)
    edits.append(
        {
            "classification": "DROP_LOCAL_COMPLEX_ADDCOMMGROUP_INSTANCE_ONLY",
            "owner": "literalStageNegativePlaneWave_differentiable",
            "old_block_sha256": sha256_text(block),
            "new_block_sha256": sha256_text(replacement),
        }
    )
    return "".join(lines)


def patch_w27(text: str, lemma: str, edits: list[dict[str, Any]]) -> str:
    lines = text.splitlines(keepends=True)
    start, end = locate_declaration(lines, "weightedFull_apply_core")
    block_lines = list(lines[start:end])
    block = "".join(block_lines)
    if lemma in block:
        return text
    tactic_hits = [
        i for i, line in enumerate(block_lines) if line.strip() in {"ring", "ring_nf"}
    ]
    if not tactic_hits:
        die("weightedFull_apply_core has no ring/ring_nf tactic")
    insertion = f"  simp only [{lemma}]\n"
    block_lines.insert(tactic_hits[-1], insertion)
    replacement = "".join(block_lines)
    lines[start:end] = block_lines
    edits.append(
        {
            "classification": "POINTWISE_PI_SMUL_NORMALIZATION_BEFORE_RING",
            "owner": "weightedFull_apply_core",
            "lemma": lemma,
            "old_block_sha256": sha256_text(block),
            "new_block_sha256": sha256_text(replacement),
        }
    )
    return "".join(lines)


def patch_holder_r1(text: str, edits: list[dict[str, Any]]) -> str:
    code = strip_noncode(text)
    pattern = re.compile(
        r"ContinuousLinearMap\.coeFn_holder"
        r"(?![A-Za-z0-9_'])"
        r"(?!\s*\(r\s*:=)"
    )
    matches = list(pattern.finditer(code))
    if not matches:
        return text
    lines = text.splitlines(keepends=True)
    line_starts: list[int] = []
    position = 0
    for line in lines:
        line_starts.append(position)
        position += len(line)
    owners: list[dict[str, Any]] = []
    for match in matches:
        line_index = max(i for i, start in enumerate(line_starts) if start <= match.start())
        if not owner_is_by_proof(lines, line_index):
            die(
                "refusing to patch coeFn_holder outside a := by proof at "
                f"line {line_index + 1}"
            )
        _, owner = declaration_owner(lines, line_index)
        owners.append({"line": line_index + 1, "owner_header": owner})
    result = text
    for match in reversed(matches):
        result = result[: match.end()] + " (r := 1)" + result[match.end() :]
    edits.append(
        {
            "classification": "PIN_COEFN_HOLDER_RESULT_EXPONENT_R_TO_ONE",
            "patched_count": len(matches),
            "owners": owners,
        }
    )
    return result


KNOWN_VARIANTS: dict[str, dict[str, Any]] = {
    "baseline": {},
    "w06_only": {"w06": True},
    "w27_pi_only": {"w27": "Pi.smul_apply"},
    "holder_only": {"holder": True},
    "holder_w06": {"holder": True, "w06": True},
    "holder_w27_pi": {"holder": True, "w27": "Pi.smul_apply"},
    "holder_w06_w27_pi": {
        "holder": True,
        "w06": True,
        "w27": "Pi.smul_apply",
    },
    "known_no_interval": {
        "holder": True,
        "w06": True,
        "w27": "Pi.smul_apply",
        "tendsto": True,
    },
    "known_no_tendsto": {
        "holder": True,
        "w06": True,
        "w27": "Pi.smul_apply",
        "interval": "linarith",
    },
    "full_linarith": {
        "holder": True,
        "w06": True,
        "w27": "Pi.smul_apply",
        "tendsto": True,
        "interval": "linarith",
    },
    "full_nlinarith": {
        "holder": True,
        "w06": True,
        "w27": "Pi.smul_apply",
        "tendsto": True,
        "interval": "nlinarith",
    },
    "full_prime_linarith": {
        "holder": True,
        "w06": True,
        "w27": "Pi.smul_apply'",
        "tendsto": True,
        "interval": "linarith",
    },
    "full_prime_nlinarith": {
        "holder": True,
        "w06": True,
        "w27": "Pi.smul_apply'",
        "tendsto": True,
        "interval": "nlinarith",
    },
}


def command_patch_fa_known(args: argparse.Namespace) -> None:
    source = Path(args.source)
    diagnostics = Path(args.diagnostics)
    out = Path(args.out)
    out.mkdir(parents=True, exist_ok=True)
    if args.variant not in KNOWN_VARIANTS:
        die(f"unknown FA known variant: {args.variant}")
    before = source.read_text(encoding="utf-8")
    before_headers = declaration_headers(before)
    config = KNOWN_VARIANTS[args.variant]
    edits: list[dict[str, Any]] = []
    text = before
    if config.get("tendsto") or config.get("interval"):
        text = apply_diagnostic_repairs(
            text,
            diagnostics.read_text(encoding="utf-8", errors="replace"),
            tendsto=bool(config.get("tendsto")),
            interval_tactic=config.get("interval"),
            edits=edits,
        )
    if config.get("holder"):
        text = patch_holder_r1(text, edits)
    if config.get("w06"):
        text = patch_w06(text, edits)
    if config.get("w27"):
        text = patch_w27(text, str(config["w27"]), edits)
    after_headers = declaration_headers(text)
    if after_headers != before_headers:
        die("known repair changed declaration headers or declaration order")
    counts = assert_trust_six_zero(text)
    source.write_text(text, encoding="utf-8")
    report = {
        "schema": "fa-v54-known-body-only-candidate-v1",
        "variant": args.variant,
        "configuration": config,
        "authority_source_sha256": sha256_text(before),
        "candidate_sha256": sha256_text(text),
        "source_bytes": len(text.encode("utf-8")),
        "source_lines": len(text.splitlines()),
        "declaration_header_count": len(after_headers),
        "edit_count": len(edits),
        "edits": edits,
        "trust_counts_after": counts,
        "trust_six_zero": True,
        "theorem_statements_changed": False,
        "declaration_order_changed": False,
        "source_moves": [],
    }
    write_json(out / "PATCH_REPORT.json", report)
    (out / "candidate.sha256").write_text(report["candidate_sha256"] + "\n")
    (out / "Mock2_FunctionalAnalysis-candidate.lean").write_text(
        text, encoding="utf-8"
    )


def as_int(value: Any, default: int = 10**9) -> int:
    try:
        return int(value)
    except (TypeError, ValueError):
        return default


def metric_int(
    metric: dict[str, Any], exact_keys: Sequence[str], tokens: Sequence[str]
) -> int:
    for key in exact_keys:
        if key in metric:
            value = as_int(metric[key])
            if value != 10**9:
                return value
    candidates: list[tuple[int, int, str, int]] = []
    for key, raw in metric.items():
        lower = key.lower()
        if not all(token in lower for token in tokens):
            continue
        value = as_int(raw)
        if value == 10**9:
            continue
        candidates.append(
            (0 if lower.startswith(("fa_", "qym_")) else 1, len(lower), key, value)
        )
    return sorted(candidates)[0][3] if candidates else 10**9


def pick_diagnostic_log(root: Path, filename_token: str) -> Path | None:
    choices: list[tuple[int, int, Path]] = []
    for path in root.rglob("*"):
        if not path.is_file():
            continue
        if filename_token not in path.name:
            continue
        if path.suffix not in {".log", ".txt"}:
            continue
        text = path.read_text(encoding="utf-8", errors="replace")
        error_count = len(re.findall(r"(?m)^.*error:", text))
        choices.append((error_count, len(text), path))
    if not choices:
        return None
    positive = [choice for choice in choices if choice[0] > 0]
    pool = positive or choices
    return max(pool, key=lambda item: (item[0], item[1]))[2]


def fallback_error_count(root: Path, filename_token: str) -> int:
    log = pick_diagnostic_log(root, filename_token)
    if log is None:
        return 10**9
    text = log.read_text(encoding="utf-8", errors="replace")
    return len(re.findall(r"(?m)^.*error:", text))


@dataclass
class CandidateBundle:
    variant: str
    root: Path
    patch: dict[str, Any]
    metric: dict[str, Any]
    source_path: Path
    source_text: str
    source_sha256: str


def discover_candidate_bundles(
    root: Path, candidate_filename: str
) -> tuple[list[CandidateBundle], list[dict[str, Any]]]:
    bundles: list[CandidateBundle] = []
    invalid: list[dict[str, Any]] = []
    for patch_path in sorted(root.rglob("PATCH_REPORT.json")):
        base = patch_path.parent
        try:
            patch = read_json(patch_path)
            variant = str(patch["variant"])
            metrics = list(base.rglob("METRIC.json"))
            sources = list(base.rglob(candidate_filename))
            if len(metrics) != 1 or len(sources) != 1:
                die(
                    f"bundle {base} has metrics={len(metrics)} sources={len(sources)}"
                )
            metric = read_json(metrics[0])
            source_path = sources[0]
            source_text = source_path.read_text(encoding="utf-8")
            source_sha = sha256_text(source_text)
            if patch.get("candidate_sha256") != source_sha:
                die("PATCH_REPORT candidate SHA mismatch")
            if "source_sha256" in metric and metric["source_sha256"] != source_sha:
                die("METRIC source SHA mismatch")
            bundles.append(
                CandidateBundle(
                    variant=variant,
                    root=base,
                    patch=patch,
                    metric=metric,
                    source_path=source_path,
                    source_text=source_text,
                    source_sha256=source_sha,
                )
            )
        except Exception as exc:  # fail closed by excluding malformed candidates
            invalid.append({"bundle": str(base), "reason": f"{type(exc).__name__}: {exc}"})
    return bundles, invalid


def validate_body_only_bundle(bundle: CandidateBundle, baseline_headers: list[str]) -> None:
    patch = bundle.patch
    if patch.get("theorem_statements_changed") is not False:
        die(f"{bundle.variant}: theorem statement flag is not false")
    if patch.get("declaration_order_changed") is not False:
        die(f"{bundle.variant}: declaration order flag is not false")
    if patch.get("source_moves") != []:
        die(f"{bundle.variant}: source_moves is not empty")
    if patch.get("trust_six_zero") is not True:
        die(f"{bundle.variant}: trust_six_zero is not true")
    counts = patch.get("trust_counts_after")
    if not isinstance(counts, dict) or any(as_int(value) != 0 for value in counts.values()):
        die(f"{bundle.variant}: non-zero trust counts")
    if declaration_headers(bundle.source_text) != baseline_headers:
        die(f"{bundle.variant}: declaration headers differ from baseline")


def fa_record(bundle: CandidateBundle) -> dict[str, Any]:
    metric = bundle.metric
    mock2 = as_int(metric.get("Mock2_exit"))
    advanced = as_int(metric.get("Mock2_Advanced_exit"))
    fa_exit = as_int(metric.get("FA_exit"))
    if mock2 != 0 or advanced != 0:
        die(f"{bundle.variant}: prerequisite exit mismatch {mock2}, {advanced}")
    if metric.get("FA_error_cap_sentinel_present") is not False:
        die(f"{bundle.variant}: FA error cap sentinel is not false")
    if metric.get("FA_inventory_complete_by_header_evidence") is not True:
        die(f"{bundle.variant}: FA inventory-complete flag is not true")
    error_count = metric_int(
        metric,
        ("FA_error_count", "FA_compile_error_count", "FA_total_error_count"),
        ("fa", "error", "count"),
    )
    if error_count == 10**9:
        error_count = fallback_error_count(bundle.root, "Mock2_FunctionalAnalysis")
    failing = metric_int(
        metric,
        ("FA_failing_declaration_count", "FA_error_declaration_count"),
        ("fa", "declaration", "count"),
    )
    signatures = metric_int(
        metric,
        ("FA_unique_error_signature_count", "FA_error_signature_count"),
        ("fa", "signature", "count"),
    )
    warnings = metric_int(
        metric,
        ("FA_warning_count", "warning_count"),
        ("warning", "count"),
    )
    if fa_exit == 0 and error_count not in (0, 10**9):
        die(f"{bundle.variant}: FA exit zero but parsed errors are non-zero")
    rank = [
        0 if fa_exit == 0 else 1,
        error_count,
        failing,
        signatures,
        warnings,
    ]
    return {
        "variant": bundle.variant,
        "source_sha256": bundle.source_sha256,
        "Mock2_exit": mock2,
        "Mock2_Advanced_exit": advanced,
        "FA_exit": fa_exit,
        "error_count": error_count,
        "failing_declaration_count": failing,
        "unique_error_signature_count": signatures,
        "warning_count": warnings,
        "rank": rank,
        "bundle_root": str(bundle.root),
    }


def command_select_fa(args: argparse.Namespace) -> None:
    root = Path(args.root)
    bundles, invalid = discover_candidate_bundles(
        root, "Mock2_FunctionalAnalysis-candidate.lean"
    )
    by_variant: dict[str, CandidateBundle] = {}
    for bundle in bundles:
        if bundle.variant in by_variant:
            die(f"duplicate candidate variant: {bundle.variant}")
        by_variant[bundle.variant] = bundle
    if args.baseline not in by_variant:
        die(f"baseline variant {args.baseline!r} is missing; invalid={invalid}")
    baseline_bundle = by_variant[args.baseline]
    baseline_headers = declaration_headers(baseline_bundle.source_text)
    records: list[dict[str, Any]] = []
    valid: dict[str, CandidateBundle] = {}
    for variant, bundle in by_variant.items():
        try:
            validate_body_only_bundle(bundle, baseline_headers)
            record = fa_record(bundle)
            records.append(record)
            valid[variant] = bundle
        except Exception as exc:
            invalid.append(
                {
                    "bundle": str(bundle.root),
                    "variant": variant,
                    "reason": f"{type(exc).__name__}: {exc}",
                }
            )
    if args.baseline not in valid:
        die(f"baseline candidate failed validation: {invalid}")
    records.sort(key=lambda record: (record["rank"], record["variant"]))
    baseline_record = next(
        record for record in records if record["variant"] == args.baseline
    )
    best = records[0]
    strictly_better = best["rank"] < baseline_record["rank"]
    selected_record = best if strictly_better else baseline_record
    selected_bundle = valid[selected_record["variant"]]
    selected_dir = Path(args.selected_dir)
    if selected_dir.exists():
        shutil.rmtree(selected_dir)
    shutil.copytree(selected_bundle.root, selected_dir)
    report = {
        "schema": "fa-v54-strict-selector-v1",
        "baseline": baseline_record,
        "best_observed": best,
        "strictly_better": strictly_better,
        "selected_variant": selected_record["variant"],
        "selected_source_sha256": selected_record["source_sha256"],
        "source_update_authorized": strictly_better
        and selected_record["variant"] != args.baseline,
        "clean_build_claimed": selected_record["FA_exit"] == 0
        and selected_record["error_count"] == 0,
        "direct_lean_verified": selected_record["FA_exit"] == 0
        and selected_record["error_count"] == 0,
        "theorem_statements_changed": False,
        "declaration_order_changed": False,
        "source_moves": [],
        "records": records,
        "invalid_candidates": invalid,
    }
    write_json(Path(args.report), report)
    write_json(selected_dir / "SELECTION.json", report)


def declaration_inventory(text: str) -> list[dict[str, Any]]:
    declarations: list[dict[str, Any]] = []
    for line_number, line in enumerate(text.splitlines(), 1):
        match = DECL_NAME_RE.match(line)
        if match:
            declarations.append(
                {
                    "line": line_number,
                    "kind": match.group("kind"),
                    "name": match.group("name"),
                    "header": line,
                }
            )
    return declarations


def inventory_errors(
    source_text: str,
    log: str,
    header: re.Pattern[str],
) -> list[dict[str, Any]]:
    source_lines = source_text.splitlines()
    declarations = declaration_inventory(source_text)

    def owner(line_number: int) -> dict[str, Any] | None:
        prior = [decl for decl in declarations if decl["line"] <= line_number]
        return prior[-1] if prior else None

    errors: list[dict[str, Any]] = []
    for index, error in enumerate(parse_error_blocks(log, header), 1):
        line_number = error["line"]
        block = error["block"]
        decl = owner(line_number)
        lower = block.lower()
        classes: list[str] = []
        classifications = {
            "tendsto_eta": ("tendsto", "function.comp"),
            "holder_exponent": ("coefn_holder", "holdertriple"),
            "scalar_action": ("pi.smul", "hsmul.hsmul", "smul"),
            "instance_synthesis": (
                "failed to synthesize",
                "synthesized type class",
            ),
            "type_mismatch": ("type mismatch", "application type mismatch"),
            "unsolved_goals": ("unsolved goals",),
            "arithmetic": ("linarith", "nlinarith", "≤", "inequality"),
            "unknown_identifier": ("unknown identifier", "invalid field notation"),
            "termination": (
                "decreasing argument",
                "termination",
                "declaration uses sorry",
            ),
        }
        for name, tokens in classifications.items():
            if any(token.lower() in lower for token in tokens):
                classes.append(name)
        normalized = re.sub(r"\s+", " ", block)
        normalized = re.sub(
            r"[^ ]*(?:Mock2_FunctionalAnalysis|QYM)\.lean:\d+:\d+:",
            "<source>:<line>:<column>:",
            normalized,
        )
        low = max(1, line_number - 4)
        high = min(len(source_lines), line_number + 4)
        errors.append(
            {
                "index": index,
                "line": line_number,
                "column": error["column"],
                "declaration_line": decl["line"] if decl else None,
                "declaration_name": decl["name"] if decl else None,
                "declaration_header": decl["header"] if decl else None,
                "code_line": source_lines[line_number - 1]
                if 1 <= line_number <= len(source_lines)
                else None,
                "classes": classes,
                "signature_sha256": sha256_text(normalized),
                "message": block[:12000],
                "snippet": [
                    {"line": number, "text": source_lines[number - 1]}
                    for number in range(low, high + 1)
                ],
            }
        )
    return errors


def command_inventory_fa(args: argparse.Namespace) -> None:
    bundle = Path(args.bundle)
    sources = list(bundle.rglob("Mock2_FunctionalAnalysis-candidate.lean"))
    metrics = list(bundle.rglob("METRIC.json"))
    if len(sources) != 1 or len(metrics) != 1:
        die(f"selected FA bundle is malformed: sources={sources}, metrics={metrics}")
    source_path = sources[0]
    source_text = source_path.read_text(encoding="utf-8")
    source_sha = sha256_text(source_text)
    metric = read_json(metrics[0])
    if "source_sha256" in metric and metric["source_sha256"] != source_sha:
        die("selected FA metric/source SHA mismatch")
    log_path = pick_diagnostic_log(bundle, "Mock2_FunctionalAnalysis")
    log = (
        log_path.read_text(encoding="utf-8", errors="replace") if log_path else ""
    )
    errors = inventory_errors(source_text, log, FA_ERROR_HEADER)
    fa_exit = as_int(metric.get("FA_exit"))
    cap = metric.get("FA_error_cap_sentinel_present")
    complete = metric.get("FA_inventory_complete_by_header_evidence")
    if cap is not False or complete is not True:
        die("selected FA diagnostics are capped or incomplete")
    if (fa_exit == 0) != (len(errors) == 0):
        die(f"FA exit/error inconsistency: exit={fa_exit}, errors={len(errors)}")
    declaration_counts = collections.Counter(
        error["declaration_name"] or "<none>" for error in errors
    )
    signature_counts = collections.Counter(error["signature_sha256"] for error in errors)
    selection_paths = list(bundle.rglob("SELECTION.json"))
    selection = read_json(selection_paths[0]) if len(selection_paths) == 1 else None
    counts = assert_trust_six_zero(source_text)
    report = {
        "schema": "fa-v54-complete-remaining-error-inventory-v1",
        "selected_source_sha256": source_sha,
        "selected_variant": selection.get("selected_variant") if selection else None,
        "Mock2_exit": as_int(metric.get("Mock2_exit")),
        "Mock2_Advanced_exit": as_int(metric.get("Mock2_Advanced_exit")),
        "FA_exit": fa_exit,
        "FA_compile_max_errors": as_int(metric.get("FA_compile_max_errors")),
        "error_cap_sentinel_present": cap,
        "inventory_complete_by_header_evidence": complete,
        "trust_counts": counts,
        "trust_six_zero": True,
        "raw_error_count": len(errors),
        "failing_declaration_count": len(declaration_counts),
        "unique_signature_count": len(signature_counts),
        "errors_by_declaration": dict(sorted(declaration_counts.items())),
        "signature_multiplicities": dict(sorted(signature_counts.items())),
        "diagnostic_log_path": str(log_path) if log_path else None,
        "clean_build_claimed": fa_exit == 0 and not errors,
        "direct_lean_verified": fa_exit == 0 and not errors,
        "theorem_statements_changed": False,
        "declaration_order_changed": False,
        "source_moves": [],
        "errors": errors,
    }
    write_json(Path(args.out), report)
    if args.source_out:
        Path(args.source_out).parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source_path, Path(args.source_out))


LOCAL_FA_VARIANTS = {
    "selected_base",
    "exact_to_simpa",
    "simpa_enriched",
    "simp_all_local",
    "aesop_local",
    "linarith_local",
    "nlinarith_local",
    "ring_normalize_local",
    "combined_conservative",
}


def apply_local_inventory_repairs(
    text: str,
    inventory: dict[str, Any],
    variant: str,
    *,
    qym: bool,
) -> tuple[str, list[dict[str, Any]]]:
    allowed = LOCAL_FA_VARIANTS
    if variant not in allowed:
        die(f"unknown local variant: {variant}")
    lines = text.splitlines(keepends=True)
    edits: list[dict[str, Any]] = []
    replacements: dict[int, str] = {}
    error_key = "qym_errors" if qym and "qym_errors" in inventory else "errors"
    errors = inventory.get(error_key)
    if not isinstance(errors, list):
        die(f"inventory does not contain {error_key}")

    def stage(index: int, new: str, kind: str, error: dict[str, Any]) -> None:
        old = replacements.get(index, lines[index])
        if new == old:
            return
        replacements[index] = new
        _, owner = declaration_owner(lines, index)
        edits.append(
            {
                "classification": kind,
                "line": index + 1,
                "owner_header": owner,
                "old": old.rstrip("\n"),
                "new": new.rstrip("\n"),
                "error_index": error.get("index"),
                "error_classes": error.get("classes", []),
            }
        )

    for error in errors:
        classes = set(error.get("classes", []))
        line_number = as_int(error.get("line"), 1)
        if variant in {"exact_to_simpa", "combined_conservative"}:
            index = nearby_line(
                lines,
                line_number,
                lambda line: tactic_body(line).startswith("exact "),
                radius=6,
            )
            if index is not None:
                old = replacements.get(index, lines[index])
                body = tactic_body(old).rstrip("\r\n")
                term = body[len("exact ") :]
                if term and not term.startswith("by"):
                    new = (
                        line_prefix(old)
                        + "simpa [Function.comp_def, Pi.smul_apply] using "
                        + term
                        + newline_of(old)
                    )
                    stage(index, new, "EXACT_TO_SIMPA_USING", error)
        if variant in {"simpa_enriched", "combined_conservative"}:
            index = nearby_line(
                lines,
                line_number,
                lambda line: "simpa" in tactic_body(line),
                radius=6,
            )
            if index is not None:
                old = replacements.get(index, lines[index])
                new = add_simpa_lemmas(
                    old, ("Function.comp_def", "Pi.smul_apply")
                )
                stage(index, new, "ENRICH_SIMPA_NORMALIZATION", error)
        if variant == "simp_all_local" or (
            variant == "combined_conservative" and "unsolved_goals" in classes
        ):
            index = nearby_line(
                lines,
                line_number,
                lambda line: tactic_body(line).startswith(
                    (
                        "exact ",
                        "simpa",
                        "simp",
                        "aesop",
                        "linarith",
                        "nlinarith",
                        "norm_num",
                        "ring",
                        "ring_nf",
                        "omega",
                    )
                ),
                radius=6,
            )
            if index is not None:
                old = replacements.get(index, lines[index])
                new = (
                    line_prefix(old)
                    + "simp_all [Function.comp_def, Pi.smul_apply]"
                    + newline_of(old)
                )
                stage(index, new, "LOCAL_SIMP_ALL", error)
        if variant == "aesop_local":
            index = nearby_line(
                lines,
                line_number,
                lambda line: tactic_body(line).startswith(
                    (
                        "exact ",
                        "simpa",
                        "simp",
                        "aesop",
                        "linarith",
                        "nlinarith",
                        "norm_num",
                        "ring",
                        "ring_nf",
                        "omega",
                    )
                ),
                radius=6,
            )
            if index is not None:
                old = replacements.get(index, lines[index])
                stage(
                    index,
                    line_prefix(old) + "aesop" + newline_of(old),
                    "LOCAL_AESOP",
                    error,
                )
        arithmetic_variant = variant in {"linarith_local", "nlinarith_local"}
        arithmetic_combined = (
            variant == "combined_conservative" and "arithmetic" in classes
        )
        if arithmetic_variant or arithmetic_combined:
            tactic = "linarith" if variant == "linarith_local" else "nlinarith"
            if "arithmetic" in classes or any(
                token in str(error.get("message", ""))
                for token in ("≤", "<", ">", "=")
            ):
                index = nearby_line(
                    lines,
                    line_number,
                    lambda line: tactic_body(line).startswith(
                        (
                            "exact ",
                            "simpa",
                            "linarith",
                            "nlinarith",
                            "norm_num",
                            "omega",
                            "positivity",
                            "ring",
                            "ring_nf",
                        )
                    ),
                    radius=6,
                )
                if index is not None:
                    old = replacements.get(index, lines[index])
                    stage(
                        index,
                        line_prefix(old) + tactic + newline_of(old),
                        "LOCAL_ARITHMETIC_REPLACEMENT",
                        error,
                    )
        ring_variant = variant == "ring_normalize_local"
        ring_combined = (
            variant == "combined_conservative" and "scalar_action" in classes
        )
        if ring_variant or ring_combined:
            index = nearby_line(
                lines,
                line_number,
                lambda line: tactic_body(line).startswith(
                    ("ring", "ring_nf", "simpa", "exact ")
                ),
                radius=6,
            )
            if index is not None:
                old = replacements.get(index, lines[index])
                new = (
                    line_prefix(old)
                    + "simp only [Pi.smul_apply] at *\n"
                    + line_prefix(old)
                    + "ring_nf"
                    + newline_of(old)
                )
                stage(index, new, "LOCAL_SCALAR_RING_NORMALIZATION", error)
    for index, replacement in replacements.items():
        lines[index] = replacement
    return "".join(lines), edits


def command_patch_fa_local(args: argparse.Namespace) -> None:
    source = Path(args.source)
    inventory = read_json(Path(args.inventory))
    out = Path(args.out)
    out.mkdir(parents=True, exist_ok=True)
    before = source.read_text(encoding="utf-8")
    before_headers = declaration_headers(before)
    after, edits = apply_local_inventory_repairs(
        before, inventory, args.variant, qym=False
    )
    if declaration_headers(after) != before_headers:
        die("local FA repair changed declaration headers or order")
    counts = assert_trust_six_zero(after)
    source.write_text(after, encoding="utf-8")
    report = {
        "schema": "fa-v54-inventory-local-body-only-candidate-v1",
        "variant": args.variant,
        "parent_source_sha256": sha256_text(before),
        "parent_inventory_sha256": sha256_bytes(Path(args.inventory).read_bytes()),
        "candidate_sha256": sha256_text(after),
        "source_bytes": len(after.encode("utf-8")),
        "source_lines": len(after.splitlines()),
        "declaration_header_count": len(before_headers),
        "edit_count": len(edits),
        "edits": edits,
        "trust_counts_after": counts,
        "trust_six_zero": True,
        "theorem_statements_changed": False,
        "declaration_order_changed": False,
        "source_moves": [],
    }
    write_json(out / "PATCH_REPORT.json", report)
    (out / "candidate.sha256").write_text(report["candidate_sha256"] + "\n")
    (out / "Mock2_FunctionalAnalysis-candidate.lean").write_text(
        after, encoding="utf-8"
    )


def command_inventory_qym(args: argparse.Namespace) -> None:
    source = Path(args.source)
    log_path = Path(args.log)
    source_text = source.read_text(encoding="utf-8")
    log = log_path.read_text(encoding="utf-8", errors="replace")
    exit_code = int(Path(args.exit_file).read_text().strip())
    errors = inventory_errors(source_text, log, QYM_ERROR_HEADER)
    cap = any(
        token in log.lower()
        for token in ("maximum number of errors", "maxerrors", "too many errors")
    )
    if cap:
        die("QYM diagnostics hit an error cap sentinel")
    if (exit_code == 0) != (len(errors) == 0):
        die(f"QYM exit/error inconsistency: exit={exit_code}, errors={len(errors)}")
    declarations = declaration_inventory(source_text)
    declaration_counts = collections.Counter(
        error["declaration_name"] or "<none>" for error in errors
    )
    signature_counts = collections.Counter(error["signature_sha256"] for error in errors)
    warnings = len(re.findall(r"(?m)^.*warning:", log))
    counts = assert_trust_six_zero(source_text)
    report = {
        "schema": "qym-v54-complete-inventory-v1",
        "variant": args.variant,
        "source_path": str(source),
        "source_sha256": sha256_text(source_text),
        "source_bytes": len(source_text.encode("utf-8")),
        "source_lines": len(source_text.splitlines()),
        "declaration_header_count": len(declarations),
        "QYM_exit": exit_code,
        "QYM_error_count": len(errors),
        "QYM_failing_declaration_count": len(declaration_counts),
        "QYM_unique_error_signature_count": len(signature_counts),
        "QYM_warning_count": warnings,
        "QYM_compile_max_errors": 2000,
        "QYM_error_cap_sentinel_present": False,
        "QYM_inventory_complete_by_header_evidence": True,
        "trust_counts": counts,
        "trust_six_zero": True,
        "qym_clean_build_claimed": exit_code == 0 and not errors,
        "qym_direct_lean_verified": exit_code == 0 and not errors,
        "theorem_statements_changed": False,
        "declaration_order_changed": False,
        "source_moves": [],
        "errors_by_declaration": dict(sorted(declaration_counts.items())),
        "signature_multiplicities": dict(sorted(signature_counts.items())),
        "errors": errors,
    }
    write_json(Path(args.out), report)


def command_patch_qym_local(args: argparse.Namespace) -> None:
    source = Path(args.source)
    inventory = read_json(Path(args.inventory))
    out = Path(args.out)
    out.mkdir(parents=True, exist_ok=True)
    before = source.read_text(encoding="utf-8")
    before_headers = declaration_headers(before)
    after, edits = apply_local_inventory_repairs(
        before, inventory, args.variant, qym=True
    )
    if declaration_headers(after) != before_headers:
        die("local QYM repair changed declaration headers or order")
    counts = assert_trust_six_zero(after)
    source.write_text(after, encoding="utf-8")
    report = {
        "schema": "qym-v54-inventory-local-body-only-candidate-v1",
        "variant": args.variant,
        "parent_source_sha256": sha256_text(before),
        "parent_inventory_sha256": sha256_bytes(Path(args.inventory).read_bytes()),
        "candidate_sha256": sha256_text(after),
        "source_bytes": len(after.encode("utf-8")),
        "source_lines": len(after.splitlines()),
        "declaration_header_count": len(before_headers),
        "edit_count": len(edits),
        "edits": edits,
        "trust_counts_after": counts,
        "trust_six_zero": True,
        "theorem_statements_changed": False,
        "declaration_order_changed": False,
        "source_moves": [],
    }
    write_json(out / "PATCH_REPORT.json", report)
    (out / "candidate.sha256").write_text(report["candidate_sha256"] + "\n")
    (out / "QYM-candidate.lean").write_text(after, encoding="utf-8")


def qym_record(bundle: CandidateBundle) -> dict[str, Any]:
    metric = bundle.metric
    qym_exit = as_int(metric.get("QYM_exit"))
    if metric.get("QYM_error_cap_sentinel_present") is not False:
        die(f"{bundle.variant}: QYM error cap sentinel is not false")
    if metric.get("QYM_inventory_complete_by_header_evidence") is not True:
        die(f"{bundle.variant}: QYM inventory-complete flag is not true")
    error_count = as_int(metric.get("QYM_error_count"))
    failing = as_int(metric.get("QYM_failing_declaration_count"))
    signatures = as_int(metric.get("QYM_unique_error_signature_count"))
    warnings = as_int(metric.get("QYM_warning_count"))
    if (qym_exit == 0) != (error_count == 0):
        die(f"{bundle.variant}: QYM exit/error inconsistency")
    return {
        "variant": bundle.variant,
        "source_sha256": bundle.source_sha256,
        "QYM_exit": qym_exit,
        "error_count": error_count,
        "failing_declaration_count": failing,
        "unique_error_signature_count": signatures,
        "warning_count": warnings,
        "rank": [
            0 if qym_exit == 0 else 1,
            error_count,
            failing,
            signatures,
            warnings,
        ],
        "bundle_root": str(bundle.root),
    }


def command_select_qym(args: argparse.Namespace) -> None:
    root = Path(args.root)
    bundles, invalid = discover_candidate_bundles(root, "QYM-candidate.lean")
    by_variant: dict[str, CandidateBundle] = {}
    for bundle in bundles:
        if bundle.variant in by_variant:
            die(f"duplicate QYM variant: {bundle.variant}")
        by_variant[bundle.variant] = bundle
    if args.baseline not in by_variant:
        die(f"QYM baseline {args.baseline!r} is missing; invalid={invalid}")
    baseline_bundle = by_variant[args.baseline]
    headers = declaration_headers(baseline_bundle.source_text)
    records: list[dict[str, Any]] = []
    valid: dict[str, CandidateBundle] = {}
    for variant, bundle in by_variant.items():
        try:
            validate_body_only_bundle(bundle, headers)
            record = qym_record(bundle)
            records.append(record)
            valid[variant] = bundle
        except Exception as exc:
            invalid.append(
                {
                    "bundle": str(bundle.root),
                    "variant": variant,
                    "reason": f"{type(exc).__name__}: {exc}",
                }
            )
    if args.baseline not in valid:
        die(f"QYM baseline failed validation: {invalid}")
    records.sort(key=lambda record: (record["rank"], record["variant"]))
    baseline_record = next(
        record for record in records if record["variant"] == args.baseline
    )
    best = records[0]
    strictly_better = best["rank"] < baseline_record["rank"]
    selected = best if strictly_better else baseline_record
    selected_bundle = valid[selected["variant"]]
    selected_dir = Path(args.selected_dir)
    if selected_dir.exists():
        shutil.rmtree(selected_dir)
    shutil.copytree(selected_bundle.root, selected_dir)
    report = {
        "schema": "qym-v54-strict-selector-v1",
        "baseline": baseline_record,
        "best_observed": best,
        "strictly_better": strictly_better,
        "selected_variant": selected["variant"],
        "selected_source_sha256": selected["source_sha256"],
        "source_update_authorized": strictly_better
        and selected["variant"] != args.baseline,
        "qym_clean_build_claimed": selected["QYM_exit"] == 0
        and selected["error_count"] == 0,
        "qym_direct_lean_verified": selected["QYM_exit"] == 0
        and selected["error_count"] == 0,
        "theorem_statements_changed": False,
        "declaration_order_changed": False,
        "source_moves": [],
        "records": records,
        "invalid_candidates": invalid,
    }
    write_json(Path(args.report), report)
    write_json(selected_dir / "SELECTION.json", report)


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser()
    sub = parser.add_subparsers(dest="command", required=True)

    known = sub.add_parser("patch-fa-known")
    known.add_argument("--source", required=True)
    known.add_argument("--diagnostics", required=True)
    known.add_argument("--variant", required=True)
    known.add_argument("--out", required=True)
    known.set_defaults(func=command_patch_fa_known)

    select_fa = sub.add_parser("select-fa")
    select_fa.add_argument("--root", required=True)
    select_fa.add_argument("--baseline", required=True)
    select_fa.add_argument("--report", required=True)
    select_fa.add_argument("--selected-dir", required=True)
    select_fa.set_defaults(func=command_select_fa)

    inv_fa = sub.add_parser("inventory-fa")
    inv_fa.add_argument("--bundle", required=True)
    inv_fa.add_argument("--out", required=True)
    inv_fa.add_argument("--source-out")
    inv_fa.set_defaults(func=command_inventory_fa)

    local_fa = sub.add_parser("patch-fa-local")
    local_fa.add_argument("--source", required=True)
    local_fa.add_argument("--inventory", required=True)
    local_fa.add_argument("--variant", required=True)
    local_fa.add_argument("--out", required=True)
    local_fa.set_defaults(func=command_patch_fa_local)

    inv_qym = sub.add_parser("inventory-qym")
    inv_qym.add_argument("--source", required=True)
    inv_qym.add_argument("--log", required=True)
    inv_qym.add_argument("--exit-file", required=True)
    inv_qym.add_argument("--variant", required=True)
    inv_qym.add_argument("--out", required=True)
    inv_qym.set_defaults(func=command_inventory_qym)

    local_qym = sub.add_parser("patch-qym-local")
    local_qym.add_argument("--source", required=True)
    local_qym.add_argument("--inventory", required=True)
    local_qym.add_argument("--variant", required=True)
    local_qym.add_argument("--out", required=True)
    local_qym.set_defaults(func=command_patch_qym_local)

    select_qym = sub.add_parser("select-qym")
    select_qym.add_argument("--root", required=True)
    select_qym.add_argument("--baseline", required=True)
    select_qym.add_argument("--report", required=True)
    select_qym.add_argument("--selected-dir", required=True)
    select_qym.set_defaults(func=command_select_qym)
    return parser


def main() -> int:
    parser = build_parser()
    args = parser.parse_args()
    try:
        args.func(args)
    except PipelineError as exc:
        print(f"pipeline error: {exc}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
