#!/usr/bin/env python3
"""Exact-P11 reanchor of the frozen Probe12 43k-49k direct-root helper.

All eighteen exact-P10 source anchors survive exactly once in terminal
Probe11 and map only to the surviving direct diagnostics selected by the root
audit.  No new roots are added.  This helper is byte-locked, exact-counted,
reversible, trust0, collision-audited against all 60 active Probe11 rules and
the frozen exact-P11 52k-61k sibling, and activation-disabled.  It never
invokes Lean, Lake, Git, the network, a workflow renderer, or a remote service.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import re
import sys
from pathlib import Path
from types import ModuleType


sys.dont_write_bytecode = True

SCHEMA = "qym-probe12-43k49k-p11-conditional-v1-exact-terminal-probe11"
INPUT_SHA256 = "d8290febb2b1c69cc8b911bcb672303beede1b87db290bd37c6608e39356cf25"
INPUT_GIT_BLOB = "9b5ba50acc8e2f3d6f55cf8cef6fc505926410cd"
INPUT_BYTES = 2_928_376
INPUT_LF = 61_891
LOG_SHA256 = "474f153278507d0ead7fe21675f326def15556281bd7b5cf67392836ea5ea97e"
HEADERS_SHA256 = "b0fe7508ba87fc324236cce71b74c59d042a0833ec1c101a1ae625a1f24dd4e6"
DIAGNOSTICS_SHA256 = "d9259b316d1c1317ea7e11f8f0370feaabacb3a2ae6066c3133ab748a2dee504"

BASE_HELPER_RELATIVE = "qym-probe12-43k49k-p10-conditional/qym_probe12_43k49k_p10_conditional.py"
BASE_HELPER_SHA256 = "5cea81a9deb981609655d767487a3cbb5fda032849869902ba074d8729fa976d"

# Sealed after one deterministic bootstrap projection.
OUTPUT_SHA256 = "a4246ffed06477b39460dd32db7b18c5974d01ef3cf7fa95143a98cb20347f6e"
OUTPUT_GIT_BLOB = "d75b98f86010a29d7df651394de6e13894238d7e"
OUTPUT_BYTES = 2_933_473
OUTPUT_LF = 61_991


def sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def git_blob(raw: bytes) -> str:
    return hashlib.sha1(f"blob {len(raw)}\0".encode("ascii") + raw).hexdigest()


def load_exact_module(name: str, path: Path, expected_sha: str) -> ModuleType:
    raw = path.read_bytes()
    if sha256(raw) != expected_sha:
        raise RuntimeError(f"module identity mismatch: {name}")
    module_name = "_qym_probe12_43k49k_p11_" + name
    spec = importlib.util.spec_from_file_location(module_name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot import module: {name}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[module_name] = module
    spec.loader.exec_module(module)
    return module


BASE_HELPER_PATH = Path(__file__).resolve().parent.parent / BASE_HELPER_RELATIVE
_BASE = load_exact_module("base_p10", BASE_HELPER_PATH, BASE_HELPER_SHA256)
Header = _BASE.Header
Rule = _BASE.Rule


SURVIVOR_HEADERS: dict[str, tuple[object, ...]] = {
    "hhalf_difference_to_l2_expose_raw_tolp": (
        Header(43313, 4, "Type mismatch: After simplification, term"),
    ),
    "hhalf_graph_fst_tendsto_expose_fstL": (
        Header(43380, 4, "Type mismatch: After simplification, term"),
    ),
    "hhalf_graph_snd_tendsto_expose_sndL": (
        Header(43399, 6, "Type mismatch: After simplification, term"),
    ),
    "hhalf_injective_unwrap_withlp_projections": (
        Header(43431, 4, "Type mismatch: After simplification, term"),
        Header(43432, 4, "Type mismatch: After simplification, term"),
    ),
    "circular_radicand_derivative_tolerate_normal_goals": (
        Header(43666, 8, "(kernel) declaration has metavariables 'QYM.FullCertification.P2ExplicitEdgeVelocityExtension.hasDerivAt_circularRadicand'"),
        Header(43667, 60, "unsolved goals"),
        Header(43670, 6, "`simp` made no progress"),
    ),
    "selected_representative_derivative_use_exact_det_pos": (
        Header(43760, 54, "`simp` made no progress"),
    ),
    "edge_velocity_tail_pin_canonical_derivative_instances": (
        Header(43809, 2, "Type mismatch: After simplification, term"),
        Header(43935, 4, "Type mismatch: After simplification, term"),
        Header(43948, 2, "Type mismatch: After simplification, term"),
        Header(43965, 2, "Type mismatch: After simplification, term"),
    ),
    "action_d1_change_to_moebius_coordinate": (
        Header(43927, 4, "Type mismatch: After simplification, term"),
    ),
    "inverse_eta_transition_contdiff_use_pointwise_bridge": (
        Header(44120, 6, "`simp` made no progress"),
    ),
    "right_normal_signed_area_finish_ring_nf": (
        Header(44447, 18, "unsolved goals"),
    ),
    "selected_horocycle_base_derivative_use_ofreal_clm": (
        Header(47058, 2, "Type mismatch: After simplification, term"),
    ),
    "product_collar_fst_norm_use_carrier_argument": (
        Header(48773, 29, "Application type mismatch: The argument"),
    ),
    "product_collar_pythagoras_normalize_pow_two": (
        Header(48998, 6, "Type mismatch"),
    ),
    "product_collar_core_smul_expose_exact_map": (
        Header(49025, 4, "`simp` made no progress"),
    ),
    "selected_high_point_use_typed_action_and_setof_goal": (
        Header(49360, 9, "failed to synthesize instance of type class", "lean.synthInstanceFailed"),
        Header(49365, 10, "Type mismatch: After simplification, term"),
    ),
    "one_sided_height_embedding_expose_codrestrict": (
        Header(49620, 2, "Type mismatch: After simplification, term"),
    ),
    "stage_boundary_certificate_eta_expand_implicit_level": (
        Header(49924, 6, "Application type mismatch: The argument"),
    ),
    "actual_stage_high_height_proof_skip_noop_dsimp": (
        Header(50069, 6, "`dsimp` made no progress"),
    ),
}


HEADER_MULTIPLICITY = {
    (43670, 6, "`simp` made no progress", None): 2,
}


def reanchor_rule(base: object) -> object:
    headers = SURVIVOR_HEADERS.get(base.label)
    if headers is None:
        raise RuntimeError(f"unmapped P10 rule: {base.label}")
    return Rule(
        base.label,
        base.old,
        base.new,
        headers,
        base.rationale,
        base.precedent + " The exact terminal Probe11 diagnostic and old anchor both survive.",
        base.provenance,
        base.occurrences,
    )


RULES = tuple(reanchor_rule(rule) for rule in _BASE.RULES)


FOREIGN_HELPERS: tuple[tuple[str, str, str, str], ...] = (
    ("active_probe11", "probe11_early_frontier", "qym-probe11-early-frontier-static/qym_probe11_early_frontier_static.py", "9177e4fd6aa03215aec4728415d095e7e099594f6bc12facbf5a2fd879175b9a"),
    ("active_probe11", "probe11_mid", "qym-probe11-mid-p10-authority/qym_probe11_mid_p10_authority.py", "f2adebd8803e40df538a8b85401ea5a26af4585aefe521135c77dde8576a1fc6"),
    ("active_probe11", "probe11_tail", "qym-probe11-tail-p10-conditional/qym_probe11_tail_p10_conditional.py", "e76d0830315918d8d51c5063048b0f85ad9f4a68c8dffa2dbab19da25a9aae49"),
    ("active_probe11", "probe11_earlymid", "qym-probe11-earlymid-p10-conditional/qym_probe11_earlymid_p10_conditional.py", "683e740e96970dd4ca53c51016f30839a4ead5c641c7c8619f5b85733e9612e6"),
    ("active_probe11", "probe11_40k", "qym-probe11-40k-p10-conditional/qym_probe11_40k_p10_conditional.py", "6765e05b8681e4d7e13bc735c4d37ea038c75423a7d5ebc1ad73b179a99e0052"),
    ("active_probe11", "probe11_structural50", "qym-probe11-50k-structural-p10/qym_probe11_50k_structural_p10.py", "82189532a76f4785734d851f459a67c2dc04e373d1fc70eb5a137506f2dc57ae"),
    ("active_probe11", "probe12_refinement", "qym-probe12-p10-midlate-refinement/qym_probe12_p10_midlate_refinement.py", "058dba8e252db0562b7b83ed5d6701445b41f189db0559e06613823f1565207d"),
    ("exact_p11_sibling", "probe12_52k61k", "qym-probe12-52k61k-p11-conditional/qym_probe12_52k61k_p11_conditional.py", "7066e3297bd171ec58a4547ed426a8d9a6228abf4de78bf3ad203d880ef7f795"),
)


EXCLUDED = (
    {
        "lines": [43709, 43716, 43724, 44148, 44153, 44427, 44439],
        "kind": "structural_or_secondary_cascade",
        "reason": "not selected as independent direct headers by the exact Probe11 root audit",
    },
    {
        "lines": [44918, 45196, 45204, 46279, 47098, 47980, 48065, 48079, 48084, 48087, 48091, 48096, 48137, 48154, 48163, 48171, 48214, 48232, 48317, 48330, 48356, 48365, 48372, 48409, 48426, 48475, 48484, 48777, 48778, 48786, 48787, 48907, 49039, 49112, 49140, 49142, 49164, 49175, 49177, 50024, 50031, 50033],
        "kind": "unowned_or_large_structural_cluster",
        "reason": "outside this exact reanchor; no new root is added without a separate bounded producer audit",
    },
    {
        "kind": "pending_exact_p11_sibling",
        "component": "probe12_36k42k_p11_reanchored",
        "reason": "the sibling was not frozen when this helper sealed; a later integrator must perform its pairwise collision and commutation audit",
    },
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
    return _BASE.trust(text)


def expected_input() -> dict[str, object]:
    return {"sha256": INPUT_SHA256, "git_blob": INPUT_GIT_BLOB, "bytes": INPUT_BYTES,
            "lf": INPUT_LF, "cr": False, "nul": False, "bom": False, "terminal_lf": True}


def expected_output() -> dict[str, object]:
    return {"sha256": OUTPUT_SHA256, "git_blob": OUTPUT_GIT_BLOB, "bytes": OUTPUT_BYTES,
            "lf": OUTPUT_LF, "cr": False, "nul": False, "bom": False, "terminal_lf": True}


def unsealed() -> bool:
    return OUTPUT_SHA256 == "" and OUTPUT_GIT_BLOB == "" and OUTPUT_BYTES == 0 and OUTPUT_LF == 0


def check_shape(actual: dict[str, object], expected: dict[str, object], *, bootstrap: bool = False) -> None:
    keys = ("cr", "nul", "bom", "terminal_lf") if bootstrap else tuple(expected)
    if any(actual[key] != expected[key] for key in keys):
        raise RuntimeError(f"shape mismatch: {actual} != {expected}")


def verify_authority(log_raw: bytes, header_raw: bytes, diagnostics_raw: bytes) -> tuple[list[dict[str, object]], int]:
    for label, actual, expected in (
        ("log", sha256(log_raw), LOG_SHA256),
        ("headers", sha256(header_raw), HEADERS_SHA256),
        ("diagnostics", sha256(diagnostics_raw), DIAGNOSTICS_SHA256),
    ):
        if actual != expected:
            raise RuntimeError(f"Probe11 {label} identity mismatch: {actual}")
    header_lines = header_raw.decode("utf-8", errors="strict").splitlines()
    rows = [json.loads(line) for line in diagnostics_raw.decode("utf-8", errors="strict").splitlines()]
    if len(header_lines) != 217:
        raise RuntimeError(f"expected 217 exact error headers, got {len(header_lines)}")
    if sum(row.get("severity") == "error" for row in rows) != 217:
        raise RuntimeError("diagnostic error count is not 217")
    if sum(row.get("severity") == "warning" for row in rows) != 350:
        raise RuntimeError("diagnostic warning count is not 350")
    mapped: list[dict[str, object]] = []
    records = 0
    for rule in RULES:
        for header in rule.headers:
            code = f"\\({re.escape(header.code)}\\)" if header.code else ""
            pattern = re.compile(
                rf"^PrimalitySheafVerification/QYM\.lean:{header.line}:{header.column}: "
                rf"error{code}: {re.escape(header.message)}"
            )
            hm = [line for line in header_lines if pattern.match(line)]
            dm = [row for row in rows if row.get("severity") == "error"
                  and row.get("line") == header.line and row.get("column") == header.column
                  and row.get("code") == header.code
                  and str(row.get("message", "")).startswith(header.message)]
            key = (header.line, header.column, header.message, header.code)
            multiplicity = HEADER_MULTIPLICITY.get(key, 1)
            if len(hm) != multiplicity or len(dm) != multiplicity:
                raise RuntimeError(f"{rule.label}: authority mapping mismatch at {header.line}:{header.column}")
            mapped.append({"rule": rule.label, **header.__dict__,
                           "authority_multiplicity": multiplicity,
                           "kind": "independent_direct_root"})
            records += multiplicity
    return mapped, records


def spans(text: str, needle: str) -> list[tuple[int, int]]:
    result: list[tuple[int, int]] = []
    start = 0
    while True:
        found = text.find(needle, start)
        if found < 0:
            return result
        result.append((found, found + len(needle)))
        start = found + 1


def audit_collisions(text: str, *, inverse: bool) -> dict[str, object]:
    own: list[tuple[int, int, str]] = []
    for rule in RULES:
        active = rule.new if inverse else rule.old
        found = spans(text, active)
        if len(found) != rule.occurrences:
            raise RuntimeError(f"{rule.label}: active anchor count {len(found)}")
        for start, end in found:
            line = text.count("\n", 0, start) + 1
            if not 43000 <= line <= 50999:
                raise RuntimeError(f"{rule.label}: scope violation at line {line}")
            own.append((start, end, rule.label))
    own_sorted = sorted(own)
    own_overlaps: list[dict[str, object]] = []
    for left, right in zip(own_sorted, own_sorted[1:]):
        if left[1] > right[0]:
            own_overlaps.append({"left": left[2], "right": right[2]})
    equalities: list[dict[str, str]] = []
    overlaps: list[dict[str, object]] = []
    identities: dict[str, str] = {}
    rule_counts = {"active_probe11": 0, "exact_p11_sibling": 0}
    span_counts = {"active_probe11": 0, "exact_p11_sibling": 0}
    new_span_counts = {"active_probe11": 0, "exact_p11_sibling": 0}
    for group, name, relative, expected_sha in FOREIGN_HELPERS:
        module = load_exact_module(name, Path(__file__).resolve().parent.parent / relative, expected_sha)
        identities[name] = expected_sha
        foreign_rules = tuple(getattr(module, "RULES", ()))
        rule_counts[group] += len(foreign_rules)
        for foreign in foreign_rules:
            for variant, anchor in (("old", foreign.old), ("new", foreign.new)):
                found = spans(text, anchor)
                span_counts[group] += len(found)
                if variant == "new":
                    new_span_counts[group] += len(found)
                for own_rule in RULES:
                    for own_variant, own_anchor in (("old", own_rule.old), ("new", own_rule.new)):
                        if own_anchor == anchor:
                            equalities.append({"own": own_rule.label, "own_variant": own_variant,
                                               "foreign": f"{name}:{foreign.label}", "foreign_variant": variant})
                for fstart, fend in found:
                    for ostart, oend, own_label in own:
                        if max(fstart, ostart) < min(fend, oend):
                            overlaps.append({"own": own_label, "foreign": f"{name}:{foreign.label}",
                                             "foreign_variant": variant,
                                             "own_span": [ostart, oend], "foreign_span": [fstart, fend]})
    if rule_counts != {"active_probe11": 60, "exact_p11_sibling": 20}:
        raise RuntimeError(f"foreign rule counts mismatch: {rule_counts}")
    if own_overlaps or equalities or overlaps:
        raise RuntimeError(f"collision: own={own_overlaps}, equalities={equalities}, foreign={overlaps}")
    return {
        "base_p10_helper_sha256": BASE_HELPER_SHA256,
        "foreign_helper_sha256": identities,
        "foreign_rule_counts": rule_counts,
        "foreign_active_span_counts": span_counts,
        "foreign_new_span_counts": new_span_counts,
        "own_spans_checked": len(own),
        "own_span_overlaps": own_overlaps,
        "exact_anchor_equalities": equalities,
        "foreign_span_overlaps": overlaps,
        "pending_exact_p11_siblings": ["probe12_36k42k_p11_reanchored"],
    }


def apply_rules(text: str, inverse: bool = False) -> tuple[str, list[dict[str, object]]]:
    audits: list[dict[str, object]] = []
    ordered = tuple(reversed(RULES)) if inverse else RULES
    for rule in ordered:
        old, new = (rule.new, rule.old) if inverse else (rule.old, rule.new)
        count = text.count(old)
        if count != rule.occurrences:
            raise RuntimeError(f"{rule.label}: exact anchor count {count}, expected {rule.occurrences}")
        text = text.replace(old, new)
        audits.append({"label": rule.label, "direction": "inverse" if inverse else "forward",
                       "occurrences": count, "headers": [header.__dict__ for header in rule.headers],
                       "rationale": rule.rationale, "precedent": rule.precedent,
                       "provenance": rule.provenance})
    return text, audits


transform = apply_rules


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--probe11-log", type=Path, required=True)
    parser.add_argument("--probe11-error-headers", type=Path, required=True)
    parser.add_argument("--probe11-diagnostics", type=Path, required=True)
    parser.add_argument("--audit", type=Path, required=True)
    parser.add_argument("--mode", choices=("forward", "inverse"), default="forward")
    parser.add_argument("--bootstrap-seal", action="store_true")
    args = parser.parse_args()
    inverse = args.mode == "inverse"
    if args.bootstrap_seal and not unsealed():
        raise RuntimeError("bootstrap refused: output identity already sealed")
    if not args.bootstrap_seal and unsealed():
        raise RuntimeError("output identity unsealed")
    source = args.input.read_bytes()
    source_shape = shape(source)
    check_shape(source_shape, expected_output() if inverse else expected_input(),
                bootstrap=args.bootstrap_seal and inverse)
    mapped, diagnostic_records = verify_authority(
        args.probe11_log.read_bytes(),
        args.probe11_error_headers.read_bytes(),
        args.probe11_diagnostics.read_bytes(),
    )
    source_text = source.decode("utf-8", errors="strict")
    collision = audit_collisions(source_text, inverse=inverse)
    before_trust = trust(source_text)
    result_text, rule_audit = apply_rules(source_text, inverse=inverse)
    result = result_text.encode("utf-8")
    result_shape = shape(result)
    check_shape(result_shape, expected_input() if inverse else expected_output(),
                bootstrap=args.bootstrap_seal and not inverse)
    after_trust = trust(result_text)
    if before_trust != after_trust or any(after_trust.values()):
        raise RuntimeError(f"trust0 failure: {before_trust} -> {after_trust}")
    restored, _ = apply_rules(result_text, inverse=not inverse)
    if restored.encode("utf-8") != source:
        raise RuntimeError("opposite transform failed byte-exact restoration")
    if args.output.exists() or args.audit.exists():
        raise RuntimeError("refusing to overwrite output or audit")
    record = {
        "schema": SCHEMA,
        "status": "STATIC_PASS_EXACT_TERMINAL_PROBE11_NOT_LEAN_EXECUTED",
        "activation": False,
        "promotion": False,
        "mode": args.mode,
        "authority": {"candidate_sha256": INPUT_SHA256, "candidate_git_blob": INPUT_GIT_BLOB,
                      "log_sha256": LOG_SHA256, "error_headers_sha256": HEADERS_SHA256,
                      "diagnostics_sha256": DIAGNOSTICS_SHA256, "errors": 217, "warnings": 350,
                      "panic": 0, "exit": 1},
        "scope": {"candidate_lines": [43000, 50999], "surviving_direct_roots_only": True,
                  "reanchored_rules": len(RULES), "new_rules": 0,
                  "foreign_helper_span_overlap": False, "cascade_diagnostics_selected": False,
                  "excluded": EXCLUDED},
        "source": source_shape,
        "result": result_shape,
        "repair_families": len(RULES),
        "repair_occurrences": sum(item["occurrences"] for item in rule_audit),
        "direct_header_positions": len(mapped),
        "direct_diagnostic_records": diagnostic_records,
        "selected_exact_probe11_lines": sorted({header.line for rule in RULES for header in rule.headers}),
        "diagnostic_map": mapped,
        "rules": rule_audit,
        "collision_audit": collision,
        "inverse_byte_equal": True,
        "trust": after_trust,
        "execution": {"lean": False, "lake": False, "git": False, "network": False,
                      "remote": False, "workflow": False, "repository_source_mutation": False},
    }
    args.output.write_bytes(result)
    args.audit.write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(json.dumps(record, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
