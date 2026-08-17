#!/usr/bin/env python3
"""Activation-disabled Probe14 repairs for exact terminal Probe13 QYM.

The first eight families are byte-identical repairs from the frozen Probe12
static package, with diagnostics reanchored to exact terminal Probe13.  Three
additional producer/API families repair the canonical-trace orthogonal
projection cluster at lines 37132--37258.  This helper never invokes Lean,
Lake, Git, a workflow, the network, or a remote service.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import re
import sys
from dataclasses import asdict, replace
from pathlib import Path
from types import ModuleType


sys.dont_write_bytecode = True

SCHEMA = "qym-probe14-30k47k-p13-reanchored-v1-exact-terminal-probe13"
INPUT_SHA256 = "92e91734eb4b1d406d854a6021c815636eff6cf0aa2f4924e710249a583ebe3b"
INPUT_GIT_BLOB = "5c895f906b516366653aaf6fc459825e89045076"
INPUT_BYTES = 2_938_395
INPUT_LF = 62_112
LOG_SHA256 = "e2a675d67ef304dbbf6b3800b9e1a8c2fd1183ff16a82eb7f46b5a64fdef0826"
HEADERS_SHA256 = "74e4c1505182503c4acc9dfe6be6a4316e44b821ec7897b377597af12c07bf02"
DIAGNOSTICS_SHA256 = "0dbe572bed4860fd6f843045d3fbc9b11edab1931f63d6b5acb70bfd88d85dcb"

# Filled after one deterministic bootstrap projection is inspected.  Bootstrap
# remains activation=false and promotion=false.
OUTPUT_SHA256 = "65c87b052d1dceac49b48f51700f873211dfb5089409ead64e4692bc3233212d"
OUTPUT_GIT_BLOB = "aa12275230341a2a90ac5c6a75d57582931395d9"
OUTPUT_BYTES = 2_938_739
OUTPUT_LF = 62_120

ROOT = Path(__file__).resolve().parent.parent
FROZEN_HELPER_RELATIVE = (
    "qym-probe14-30k47k-p12-static/qym_probe14_30k47k_p12_static.py"
)
FROZEN_HELPER_SHA256 = (
    "17bea33c936ce776544e16fb89d6c28d0601f962fae4e0f46f1649c90594ae15"
)


def sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def git_blob(raw: bytes) -> str:
    return hashlib.sha1(f"blob {len(raw)}\0".encode("ascii") + raw).hexdigest()


def load_exact_module(label: str, path: Path, expected_sha: str) -> ModuleType:
    raw = path.read_bytes()
    actual = sha256(raw)
    if actual != expected_sha:
        raise RuntimeError(
            f"helper identity mismatch for {label}: {actual} != {expected_sha}"
        )
    module_name = "_qym_probe14_p13_" + label
    spec = importlib.util.spec_from_file_location(module_name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot import helper: {label}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[module_name] = module
    spec.loader.exec_module(module)
    return module


_FROZEN = load_exact_module(
    "frozen_probe14_p12", ROOT / FROZEN_HELPER_RELATIVE, FROZEN_HELPER_SHA256
)
Header = _FROZEN.Header
Rule = _FROZEN.Rule

FROZEN_P13_HEADERS: dict[str, tuple[object, ...]] = {
    "stabilizer_map_eq_bot_supply_subgroup_argument": (
        Header(37547, 4, "Application type mismatch: The argument"),
    ),
    "twisted_difference_add_expose_pointwise_pi_add": (
        Header(40684, 2, "unsolved goals"),
    ),
    "twisted_difference_smul_expose_pointwise_pi_smul": (
        Header(40695, 2, "unsolved goals"),
    ),
    "eta_continuity_compose_full_composite_with_comp_prime": (
        Header(41332, 10, "Application type mismatch: The argument"),
    ),
    "right_normal_real_part_close_trivial_side_goal": (
        Header(44552, 51, "unsolved goals"),
    ),
    "selected_cusp_circle_pin_add_circle_quotient_map": (
        Header(
            45043,
            39,
            "failed to synthesize instance of type class",
            "lean.synthInstanceFailed",
        ),
    ),
    "smooth_transition_residual_use_explicit_proposition_variable": (
        Header(45321, 20, "invalid binder annotation, type is not a class instance"),
        Header(45329, 32, "Unknown identifier `hSmooth`", "lean.unknownIdentifier"),
    ),
    "negative_horocycle_derivative_normalize_comp_and_neg_smul": (
        Header(47230, 2, "'change' tactic failed, pattern"),
    ),
}

if len(_FROZEN.RULES) != 8:
    raise RuntimeError("frozen Probe14 rule count drifted")
if {rule.label for rule in _FROZEN.RULES} != set(FROZEN_P13_HEADERS):
    raise RuntimeError("frozen Probe14 rule labels drifted")

REANCHORED_FROZEN_RULES = tuple(
    replace(rule, headers=FROZEN_P13_HEADERS[rule.label])
    for rule in _FROZEN.RULES
)

NEW_RULES = (
    Rule(
        "canonical_zero_stored_projection_use_complete_space_constructor",
        "noncomputable instance actualFixedPhaseCanonicalZeroStored_hasOrthogonalProjection\n"
        "    (n : ℤ) (Y : ℝ) :\n"
        "    (ActualFixedPhaseCanonicalZeroStoredSubspace n Y).HasOrthogonalProjection := by\n"
        "  letI : CompleteSpace\n"
        "      (ActualFixedPhaseCanonicalZeroStoredSubspace n Y) :=\n"
        "    (actualFixedPhaseCuspTraceZeroBoundarySubspace_isClosed n Y).isComplete.completeSpace_coe\n"
        "  infer_instance\n",
        "noncomputable instance actualFixedPhaseCanonicalZeroStored_hasOrthogonalProjection\n"
        "    (n : ℤ) (Y : ℝ) :\n"
        "    (ActualFixedPhaseCanonicalZeroStoredSubspace n Y).HasOrthogonalProjection := by\n"
        "  letI : CompleteSpace\n"
        "      (ActualFixedPhaseCanonicalZeroStoredSubspace n Y) :=\n"
        "    (actualFixedPhaseCuspTraceZeroBoundarySubspace_isClosed n Y).isComplete.completeSpace_coe\n"
        "  exact Submodule.HasOrthogonalProjection.ofCompleteSpace _\n",
        (
            Header(
                37132,
                2,
                "failed to synthesize instance of type class",
                "lean.synthInstanceFailed",
            ),
        ),
        "Use the current explicit constructor from completeness instead of asking instance search to synthesize the projection structure.",
        "The immediately preceding local CompleteSpace instance supplies the constructor's only structural premise for this submodule.",
    ),
    Rule(
        "canonical_trace_remainder_rewrite_double_orthogonal",
        "  change x - (ActualFixedPhaseCanonicalTraceClass n Y).starProjection x ∈\n"
        "    ActualFixedPhaseCanonicalZeroStoredSubspace n Y\n"
        "  simpa using\n"
        "    (ActualFixedPhaseCanonicalTraceClass n Y).sub_starProjection_mem_orthogonal x\n",
        "  change x - (ActualFixedPhaseCanonicalTraceClass n Y).starProjection x ∈\n"
        "    ActualFixedPhaseCanonicalZeroStoredSubspace n Y\n"
        "  have h :=\n"
        "    (ActualFixedPhaseCanonicalTraceClass n Y).sub_starProjection_mem_orthogonal x\n"
        "  rw [Submodule.orthogonal_orthogonal\n"
        "    (ActualFixedPhaseCanonicalZeroStoredSubspace n Y)] at h\n"
        "  exact h\n",
        (Header(37232, 2, "Type mismatch: After simplification, term"),),
        "Rewrite the projection remainder's double orthogonal membership explicitly to the zero-stored subspace.",
        "The trace class is defined as the zero-stored subspace orthogonal, so sub_starProjection_mem_orthogonal lands in its double orthogonal.",
    ),
    Rule(
        "canonical_trace_projection_kernel_supply_orthogonal_argument",
        "  calc\n"
        "    (actualFixedPhaseCanonicalTraceClassProjection n Y).ker =\n"
        "        (ActualFixedPhaseCanonicalTraceClass n Y)ᗮ :=\n"
        "      Submodule.ker_orthogonalProjection\n"
        "    _ = ActualFixedPhaseCanonicalZeroStoredSubspace n Y :=\n"
        "      Submodule.orthogonal_orthogonal\n",
        "  calc\n"
        "    (actualFixedPhaseCanonicalTraceClassProjection n Y).ker =\n"
        "        (ActualFixedPhaseCanonicalTraceClass n Y)ᗮ :=\n"
        "      Submodule.ker_orthogonalProjection\n"
        "    _ = ActualFixedPhaseCanonicalZeroStoredSubspace n Y :=\n"
        "      Submodule.orthogonal_orthogonal\n"
        "        (ActualFixedPhaseCanonicalZeroStoredSubspace n Y)\n",
        (
            Header(37258, 6, "Type mismatch"),
            Header(37257, 4, "invalid 'calc' step, failed to synthesize `Trans` instance"),
        ),
        "Supply the zero-stored submodule explicitly to the current orthogonal_orthogonal API.",
        "The first calc step exposes the left side as the orthogonal of the trace class, which definitionally is the zero-stored double orthogonal.",
    ),
)

RULES = REANCHORED_FROZEN_RULES + NEW_RULES

ACTIVE_HELPERS: tuple[tuple[str, str, str], ...] = (
    (
        "probe12_early_frontier",
        "qym-probe12-early-frontier-p11-conditional/qym_probe12_early_frontier_p11_conditional.py",
        "35b5ccf5f04899c810ca798cbcf700230fdfc4b930d16ab5d9cf646584954215",
    ),
    (
        "probe12_36k42k",
        "qym-probe12-36k42k-p11-reanchored/qym_probe12_36k42k_p11_reanchored.py",
        "5bd02f57232ac30c336b3e13574b7cba4dc4b0998f159e3fdebd41ed6354a365",
    ),
    (
        "probe12_43k49k",
        "qym-probe12-43k49k-p11-conditional/qym_probe12_43k49k_p11_conditional.py",
        "5070ada686ac425b76403ae53210e586bda305a8a70606d6d3bc6529ff2b2523",
    ),
    (
        "probe12_50k53k",
        "qym-probe12-50k53k-p11-conditional/qym_probe12_50k53k_p11_conditional.py",
        "5352b37ec754a5131164e91649b54a277b5d257258bc316f653b6d218bfb63c8",
    ),
    (
        "probe12_52k61k",
        "qym-probe12-52k61k-p11-conditional/qym_probe12_52k61k_p11_conditional.py",
        "7066e3297bd171ec58a4547ed426a8d9a6228abf4de78bf3ad203d880ef7f795",
    ),
    (
        "probe13_early",
        "qym-probe13-early-p12-conditional/qym_probe13_early_p12_conditional.py",
        "5462da0d1e49fc9f5769eeaf9052515cc905cdd55740dc55c3d930992d878210",
    ),
    (
        "probe13_50k_direct",
        "qym-probe13-50k50599-p12-reanchored/qym_probe13_50k50599_p12_reanchored.py",
        "a2eacbaebd1f3fddcb865a551613ea8ebbcdf12d74869be2b61c663a0891ed50",
    ),
    (
        "probe13_mid_highleverage",
        "qym-probe13-highleverage-instances/qym_probe13_highleverage_instances.py",
        "e29672a27f2e6421426b73350655b3bae5dca187a8ab2fe39ea023cdf19ec47e",
    ),
    (
        "probe13_tail",
        "qym-probe13-tail-p12-direct/qym_probe13_tail_p12_direct.py",
        "11f19ecfabdde4da519321e133fd1a2265bedc7784cdd729e8dd05fbf310cc48",
    ),
)


def shape(raw: bytes) -> dict[str, object]:
    raw.decode("utf-8", errors="strict")
    return {
        "sha256": sha256(raw),
        "git_blob": git_blob(raw),
        "bytes": len(raw),
        "lf": raw.count(b"\n"),
        "cr": b"\r" in raw,
        "nul": b"\0" in raw,
        "bom": raw.startswith(b"\xef\xbb\xbf"),
        "terminal_lf": raw.endswith(b"\n"),
    }


def trust(text: str) -> dict[str, int]:
    patterns = {
        "sorry": r"\bsorry\b",
        "admit": r"\badmit\b",
        "native_decide": r"\bnative_decide\b",
        "Lean.ofReduceBool": r"\bLean\.ofReduceBool\b",
        "axiom_declaration": r"(?m)^\s*axiom\s+",
        "unsafe_declaration": r"(?m)^\s*unsafe\s+(?:def|theorem|opaque|abbrev|instance)\s+",
        "maxHeartbeats_zero": r"set_option\s+maxHeartbeats\s+0",
    }
    return {label: len(re.findall(pattern, text)) for label, pattern in patterns.items()}


def locate(text: str, needle: str) -> tuple[int, int, int, int]:
    pos = text.find(needle)
    if pos < 0 or text.find(needle, pos + 1) >= 0:
        raise RuntimeError("anchor is not uniquely located")
    start_line = text.count("\n", 0, pos) + 1
    end_line = start_line + needle.count("\n")
    return pos, pos + len(needle), start_line, end_line


def verify_authority(
    log_raw: bytes, headers_raw: bytes, diagnostics_raw: bytes
) -> list[dict[str, object]]:
    expected = (
        ("log", sha256(log_raw), LOG_SHA256),
        ("headers", sha256(headers_raw), HEADERS_SHA256),
        ("diagnostics", sha256(diagnostics_raw), DIAGNOSTICS_SHA256),
    )
    for label, actual, wanted in expected:
        if actual != wanted:
            raise RuntimeError(f"Probe13 {label} identity mismatch: {actual}")
    header_lines = headers_raw.decode("utf-8", errors="strict").splitlines()
    rows = [
        json.loads(line)
        for line in diagnostics_raw.decode("utf-8", errors="strict").splitlines()
    ]
    errors = [row for row in rows if row.get("severity") == "error"]
    warnings = [row for row in rows if row.get("severity") == "warning"]
    if len(header_lines) != 151 or len(errors) != 151 or len(warnings) != 341:
        raise RuntimeError("terminal Probe13 diagnostic counts drifted")
    mapped: list[dict[str, object]] = []
    for rule in RULES:
        for header in rule.headers:
            matches = [
                row
                for row in errors
                if row.get("line") == header.line
                and row.get("column") == header.column
                and row.get("message") == header.message
                and row.get("code") == header.code
            ]
            if len(matches) != 1:
                raise RuntimeError(
                    f"{rule.label}: exact diagnostic mismatch at "
                    f"{header.line}:{header.column}"
                )
            header_pattern = re.compile(
                rf"^PrimalitySheafVerification/QYM\.lean:{header.line}:{header.column}: error"
            )
            if sum(bool(header_pattern.match(line)) for line in header_lines) != 1:
                raise RuntimeError(
                    f"{rule.label}: exact header mismatch at "
                    f"{header.line}:{header.column}"
                )
            mapped.append({"rule": rule.label, **asdict(header)})
    return mapped


def collision_audit(source_text: str) -> dict[str, object]:
    own_ranges: list[tuple[int, int, str]] = []
    own_anchors: list[dict[str, object]] = []
    for rule in RULES:
        if source_text.count(rule.old) != rule.occurrences:
            raise RuntimeError(f"{rule.label}: Probe13 old anchor count drifted")
        if source_text.count(rule.new) != 0:
            raise RuntimeError(f"{rule.label}: Probe13 new anchor already active")
        start, end, start_line, end_line = locate(source_text, rule.old)
        if not (30_000 <= start_line <= 47_999 and end_line <= 48_050):
            raise RuntimeError(f"{rule.label}: source scope violation {start_line}-{end_line}")
        own_ranges.append((start, end, rule.label))
        own_anchors.append(
            {"label": rule.label, "start_line": start_line, "end_line": end_line}
        )
    for i, (a0, a1, alabel) in enumerate(own_ranges):
        for b0, b1, blabel in own_ranges[i + 1 :]:
            if max(a0, b0) < min(a1, b1):
                raise RuntimeError(f"own source-span collision: {alabel}/{blabel}")
    for i, left in enumerate(RULES):
        for right in RULES[i + 1 :]:
            for lv in (left.old, left.new):
                for rv in (right.old, right.new):
                    if lv == rv or lv in rv or rv in lv:
                        raise RuntimeError(f"own textual collision: {left.label}/{right.label}")

    helper_identities: dict[str, str] = {}
    foreign_families = 0
    foreign_variants_checked = 0
    foreign_active_spans_found = 0
    textual_collisions: list[dict[str, object]] = []
    span_collisions: list[dict[str, object]] = []
    for helper_label, relative, expected_sha in ACTIVE_HELPERS:
        module = load_exact_module(helper_label, ROOT / relative, expected_sha)
        helper_identities[helper_label] = expected_sha
        foreign_rules = tuple(getattr(module, "RULES", ()))
        foreign_families += len(foreign_rules)
        for foreign in foreign_rules:
            for variant_name, variant in (("old", foreign.old), ("new", foreign.new)):
                foreign_variants_checked += 1
                for own in RULES:
                    for own_variant_name, own_variant in (
                        ("old", own.old),
                        ("new", own.new),
                    ):
                        if (
                            own_variant == variant
                            or own_variant in variant
                            or variant in own_variant
                        ):
                            textual_collisions.append(
                                {
                                    "own": own.label,
                                    "own_variant": own_variant_name,
                                    "foreign": f"{helper_label}:{foreign.label}",
                                    "foreign_variant": variant_name,
                                }
                            )
                offset = 0
                while True:
                    pos = source_text.find(variant, offset)
                    if pos < 0:
                        break
                    foreign_active_spans_found += 1
                    vend = pos + len(variant)
                    for own_start, own_end, own_label in own_ranges:
                        if max(pos, own_start) < min(vend, own_end):
                            span_collisions.append(
                                {
                                    "own": own_label,
                                    "foreign": f"{helper_label}:{foreign.label}",
                                    "foreign_variant": variant_name,
                                }
                            )
                    offset = pos + 1
    if foreign_families != 89 or foreign_variants_checked != 178:
        raise RuntimeError(
            "active Probe12+Probe13 inventory count drifted: "
            f"{foreign_families}/{foreign_variants_checked}"
        )
    if textual_collisions or span_collisions:
        raise RuntimeError("collision with active Probe12+Probe13 repair inventory")
    return {
        "status": "PASS",
        "own_families": len(RULES),
        "own_occurrences": sum(rule.occurrences for rule in RULES),
        "own_anchors": own_anchors,
        "own_span_overlap_count": 0,
        "own_textual_collision_count": 0,
        "active_helper_identities": helper_identities,
        "foreign_families": foreign_families,
        "foreign_variants_checked": foreign_variants_checked,
        "foreign_active_variant_spans_found": foreign_active_spans_found,
        "foreign_textual_collision_count": 0,
        "foreign_source_span_collision_count": 0,
    }


def transform(text: str, inverse: bool) -> tuple[str, list[dict[str, object]]]:
    audits: list[dict[str, object]] = []
    ordered = tuple(reversed(RULES)) if inverse else RULES
    for rule in ordered:
        src, dst = (rule.new, rule.old) if inverse else (rule.old, rule.new)
        count = text.count(src)
        if count != rule.occurrences:
            raise RuntimeError(
                f"{rule.label}: exact anchor count {count}, expected {rule.occurrences}"
            )
        text = text.replace(src, dst)
        audits.append(
            {
                "label": rule.label,
                "direction": "inverse" if inverse else "forward",
                "occurrences": count,
                "headers": [asdict(header) for header in rule.headers],
                "rationale": rule.rationale,
                "precedent": rule.precedent,
                "origin": (
                    "frozen_probe12_reanchored"
                    if rule in REANCHORED_FROZEN_RULES
                    else "new_exact_probe13_producer"
                ),
            }
        )
    return text, audits


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--probe13-log", type=Path, required=True)
    parser.add_argument("--probe13-headers", type=Path, required=True)
    parser.add_argument("--probe13-diagnostics", type=Path, required=True)
    parser.add_argument("--audit", type=Path, required=True)
    parser.add_argument("--inverse", action="store_true")
    parser.add_argument("--bootstrap", action="store_true")
    args = parser.parse_args()

    source_raw = args.input.read_bytes()
    source = shape(source_raw)
    expected_source_sha = OUTPUT_SHA256 if args.inverse else INPUT_SHA256
    if args.bootstrap and args.inverse:
        raise RuntimeError("bootstrap inverse is forbidden")
    if not args.bootstrap and not expected_source_sha:
        raise RuntimeError("sealed output constants are not populated")
    if source["sha256"] != expected_source_sha:
        raise RuntimeError(f"source identity mismatch: {source['sha256']}")
    if not args.inverse:
        if (
            source["git_blob"] != INPUT_GIT_BLOB
            or source["bytes"] != INPUT_BYTES
            or source["lf"] != INPUT_LF
        ):
            raise RuntimeError("Probe13 source shape mismatch")
    elif (
        source["git_blob"] != OUTPUT_GIT_BLOB
        or source["bytes"] != OUTPUT_BYTES
        or source["lf"] != OUTPUT_LF
    ):
        raise RuntimeError("sealed Probe14 source shape mismatch")

    mapped = verify_authority(
        args.probe13_log.read_bytes(),
        args.probe13_headers.read_bytes(),
        args.probe13_diagnostics.read_bytes(),
    )
    source_text = source_raw.decode("utf-8", errors="strict")
    collisions = (
        collision_audit(source_text)
        if not args.inverse
        else {"status": "NOT_REPEATED_ON_INVERSE"}
    )
    result_text, rule_audits = transform(source_text, args.inverse)
    result_raw = result_text.encode("utf-8")
    result = shape(result_raw)
    expected_result_sha = INPUT_SHA256 if args.inverse else OUTPUT_SHA256
    if not args.bootstrap and result["sha256"] != expected_result_sha:
        raise RuntimeError(f"result identity mismatch: {result['sha256']}")
    if not args.inverse and not args.bootstrap and (
        result["git_blob"] != OUTPUT_GIT_BLOB
        or result["bytes"] != OUTPUT_BYTES
        or result["lf"] != OUTPUT_LF
    ):
        raise RuntimeError("sealed Probe14 result shape mismatch")
    if args.inverse and (
        result["git_blob"] != INPUT_GIT_BLOB
        or result["bytes"] != INPUT_BYTES
        or result["lf"] != INPUT_LF
    ):
        raise RuntimeError("inverse did not restore exact Probe13 source shape")

    trust_counts = trust(result_text)
    if any(trust_counts.values()):
        raise RuntimeError(f"trust-token audit failed: {trust_counts}")
    args.output.write_bytes(result_raw)
    audit = {
        "schema": SCHEMA,
        "status": (
            "STATIC_PASS_BOOTSTRAP_NOT_LEAN_EXECUTED"
            if args.bootstrap
            else "STATIC_PASS_SEALED_NOT_LEAN_EXECUTED"
        ),
        "activation": False,
        "promotion": False,
        "must_reanchor_after_terminal_probe14": True,
        "mode": "inverse" if args.inverse else "forward",
        "authority": {
            "candidate_sha256": INPUT_SHA256,
            "candidate_git_blob": INPUT_GIT_BLOB,
            "log_sha256": LOG_SHA256,
            "headers_sha256": HEADERS_SHA256,
            "diagnostics_sha256": DIAGNOSTICS_SHA256,
            "errors": 151,
            "warnings": 341,
            "panic": 0,
            "exit": 1,
        },
        "frozen_helper": {
            "relative_path": FROZEN_HELPER_RELATIVE,
            "sha256": FROZEN_HELPER_SHA256,
            "families_reanchored": len(REANCHORED_FROZEN_RULES),
        },
        "source": source,
        "result": result,
        "repair_families": len(RULES),
        "repair_occurrences": sum(rule.occurrences for rule in RULES),
        "frozen_survivor_families": len(REANCHORED_FROZEN_RULES),
        "new_exact_probe13_families": len(NEW_RULES),
        "diagnostic_ownership_records": len(mapped),
        "selected_exact_probe13_lines": sorted(
            {header.line for rule in RULES for header in rule.headers}
        ),
        "diagnostic_map": mapped,
        "rules": rule_audits,
        "collision_audit": collisions,
        "trust": trust_counts,
        "execution": {
            "lean": False,
            "lake": False,
            "git": False,
            "network": False,
            "remote": False,
            "repository_source_mutation": False,
        },
    }
    args.audit.write_text(
        json.dumps(audit, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
        newline="\n",
    )


if __name__ == "__main__":
    main()
