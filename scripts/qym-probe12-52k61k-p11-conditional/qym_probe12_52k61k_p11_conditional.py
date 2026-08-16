#!/usr/bin/env python3
"""Exact-P11 conditional repairs for surviving direct roots in lines 52000-61999.

Twenty exact-P10 rules are reanchored only because their source anchors and
diagnostics survive in the terminal Probe11 authority.  Three tempting
symmetry refinements were rejected because they overlap active Probe11-tail
new spans.  The helper is byte-locked,
exact-counted, reversible, trust0, collision-audited against all 60 active
Probe11 rules, and activation-disabled.  It never invokes Lean, Lake, Git,
the network, or a remote service.
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

SCHEMA = "qym-probe12-52k61k-p11-conditional-v1-exact-terminal-probe11"
INPUT_SHA256 = "d8290febb2b1c69cc8b911bcb672303beede1b87db290bd37c6608e39356cf25"
INPUT_GIT_BLOB = "9b5ba50acc8e2f3d6f55cf8cef6fc505926410cd"
INPUT_BYTES = 2_928_376
INPUT_LF = 61_891
LOG_SHA256 = "474f153278507d0ead7fe21675f326def15556281bd7b5cf67392836ea5ea97e"
HEADERS_SHA256 = "b0fe7508ba87fc324236cce71b74c59d042a0833ec1c101a1ae625a1f24dd4e6"
DIAGNOSTICS_SHA256 = "d9259b316d1c1317ea7e11f8f0370feaabacb3a2ae6066c3133ab748a2dee504"

BASE_HELPER_RELATIVE = "qym-probe12-52k61k-p10-conditional/qym_probe12_52k61k_p10_conditional.py"
BASE_HELPER_SHA256 = "dde4c4df0473bbbd1da69bce9968f00b0859d045d254740b5852f72e5b489545"

# Sealed after one deterministic bootstrap projection.
OUTPUT_SHA256 = "23be98d651a77ea06c843f5cb492142caf616f9f22db1e0adb49a6d7e379aeaa"
OUTPUT_GIT_BLOB = "9324161325d90eceecfcaca7da5a78adf791eb53"
OUTPUT_BYTES = 2_929_684
OUTPUT_LF = 61_918


def sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def git_blob(raw: bytes) -> str:
    return hashlib.sha1(f"blob {len(raw)}\0".encode("ascii") + raw).hexdigest()


def load_exact_module(name: str, path: Path, expected_sha: str) -> ModuleType:
    raw = path.read_bytes()
    if sha256(raw) != expected_sha:
        raise RuntimeError(f"module identity mismatch: {name}")
    module_name = "_qym_probe12_52k61k_p11_" + name
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
    "sector_potential_symmetry_use_generic_inner_smul": (
        Header(53424, 4, "Tactic `rewrite` failed: Did not find an occurrence of the pattern"),
    ),
    "sqrt_lower_bound_square_without_recursive_reverse_rw": (
        Header(54417, 78, "unsolved goals"),
    ),
    "sector_sqrt_symmetry_use_generic_inner_smul": (
        Header(54672, 4, "Tactic `rewrite` failed: Did not find an occurrence of the pattern"),
    ),
    "l2_delta_family_beta_reduce_both_types": (
        Header(55142, 2, "Type mismatch: After simplification, term"),
    ),
    "off_test_witness_change_to_p4_complement": (
        Header(55959, 2, "Type mismatch: After simplification, term"),
    ),
    "projection_hamiltonian_inner_self_close_cast_power": (
        Header(56489, 72, "unsolved goals"),
    ),
    "off_test_inner_self_close_cast_power": (
        Header(56515, 29, "unsolved goals"),
    ),
    "projection_absorb_left_simp_indicator_branches": (
        Header(57272, 2, "unsolved goals"),
        Header(57279, 35, "Tactic `rewrite` failed: Did not find an occurrence of the pattern"),
    ),
    "projection_error_bound_preserve_natural_stage_name": (
        Header(57417, 2, "unsolved goals"),
        Header(57420, 2, "unsolved goals"),
    ),
    "projection_error_eventually_zero_preserve_stage_name": (
        Header(57442, 66, "unsolved goals"),
    ),
    "projection_error_pointwise_tendsto_preserve_stage_name": (
        Header(57451, 21, "unsolved goals"),
    ),
    "covariant_derivative_symmetry_transport_ground_equality": (
        Header(58545, 6, "Tactic `rewrite` failed: Did not find an occurrence of the pattern"),
    ),
    "potential_symmetry_pin_complex_real_conjugation": (
        Header(58640, 21, "Tactic `rewrite` failed: Did not find an occurrence of the pattern"),
    ),
    "coordinate_hamiltonian_symmetry_transport_two_equalities": (
        Header(58665, 6, "Tactic `rewrite` failed: Did not find an occurrence of the pattern"),
    ),
    "hamiltonian_form_hermitian_pin_complex_conjugation": (
        Header(58792, 40, "Tactic `rewrite` failed: Did not find an occurrence of the pattern"),
    ),
    "hamiltonian_form_representation_pin_complex_conjugation": (
        Header(58806, 40, "Tactic `rewrite` failed: Did not find an occurrence of the pattern"),
    ),
    "hamiltonian_form_re_self_drop_redundant_final_simp": (
        Header(58828, 2, "`simp` made no progress"),
    ),
    "negative_one_left_inverse_expand_nested_projection_map": (
        Header(59600, 4, "Tactic `rewrite` failed: Did not find an occurrence of the pattern"),
    ),
    "negative_one_resolvent_tendsto_beta_reduce_composition": (
        Header(59695, 2, "Type mismatch: After simplification, term"),
    ),
    "ground_range_reverse_use_sub_eq_self": (
        Header(59762, 45, "Tactic `rewrite` failed: Did not find an occurrence of the pattern"),
    ),
}


UNIQUE_RE_SELF_OLD = (
    "@[simp]\n"
    "theorem coordinateHamiltonianForm_re_self (u : CoordinateL2) :\n"
    "    RCLike.re (coordinateHamiltonianForm u u) =\n"
    "      ‖covariantDerivative u‖ ^ 2 + (1 / 4 : ℝ) * ‖groundProjection u‖ ^ 2 := by\n"
    "  rw [coordinateHamiltonianForm_apply,\n"
    "    inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]\n"
    "  simp\n"
    "  simp only [Complex.ofReal_re]\n"
)
UNIQUE_RE_SELF_NEW = (
    "@[simp]\n"
    "theorem coordinateHamiltonianForm_re_self (u : CoordinateL2) :\n"
    "    RCLike.re (coordinateHamiltonianForm u u) =\n"
    "      ‖covariantDerivative u‖ ^ 2 + (1 / 4 : ℝ) * ‖groundProjection u‖ ^ 2 := by\n"
    "  rw [coordinateHamiltonianForm_apply,\n"
    "    inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]\n"
    "  simp\n"
)


def reanchor_rule(base: object) -> object:
    headers = SURVIVOR_HEADERS.get(base.label)
    if headers is None:
        raise RuntimeError(f"unmapped P10 rule: {base.label}")
    old = base.old
    new = base.new
    if base.label == "hamiltonian_form_re_self_drop_redundant_final_simp":
        old = UNIQUE_RE_SELF_OLD
        new = UNIQUE_RE_SELF_NEW
    return Rule(
        base.label,
        old,
        new,
        headers,
        base.rationale,
        base.precedent + " The exact terminal Probe11 diagnostic and old anchor both survive.",
        base.occurrences,
    )


REANCHORED_RULES = tuple(reanchor_rule(rule) for rule in _BASE.RULES)


PROPOSED_COLLIDING_REFINEMENTS = (
    Rule(
        "discriminant_operator_symmetry_pin_complex_conjugation",
        "  simpa only [actualStageDiscriminantPotentialComplex_apply, smul_eq_mul] using\n"
        "    (show\n"
        "      inner ℂ\n"
        "          ((actualStageDiscriminantPotential Y x : ℂ) • u x) (v x) =\n"
        "        inner ℂ (u x)\n"
        "          ((actualStageDiscriminantPotential Y x : ℂ) • v x) by\n"
        "      rw [inner_smul_left, inner_smul_right, starRingEnd_apply,\n"
        "        RCLike.star_def, RCLike.conj_ofReal])\n",
        "  simpa only [actualStageDiscriminantPotentialComplex_apply, smul_eq_mul] using\n"
        "    (show\n"
        "      inner ℂ\n"
        "          ((actualStageDiscriminantPotential Y x : ℂ) • u x) (v x) =\n"
        "        inner ℂ (u x)\n"
        "          ((actualStageDiscriminantPotential Y x : ℂ) • v x) by\n"
        "      rw [inner_smul_left, inner_smul_right, starRingEnd_apply,\n"
        "        Complex.star_def, Complex.conj_ofReal])\n",
        (Header(53103, 25, "Tactic `rewrite` failed: Did not find an occurrence of the pattern"),),
        "Pin the real-potential star and conjugation laws to the concrete Complex scalar field.",
        "The exact P11 residual is starRingEnd Complex on a real cast, matching the surviving failures at 58640/58792/58806.",
    ),
    Rule(
        "discriminant_sqrt_operator_symmetry_pin_complex_conjugation",
        "  simpa only [actualStageDiscriminantSqrtPotentialComplex_apply,\n"
        "    smul_eq_mul] using\n"
        "    (show\n"
        "      inner ℂ\n"
        "          ((actualStageDiscriminantSqrtPotential Y x : ℂ) • u x) (v x) =\n"
        "        inner ℂ (u x)\n"
        "          ((actualStageDiscriminantSqrtPotential Y x : ℂ) • v x) by\n"
        "      rw [inner_smul_left, inner_smul_right, starRingEnd_apply,\n"
        "        RCLike.star_def, RCLike.conj_ofReal])\n",
        "  simpa only [actualStageDiscriminantSqrtPotentialComplex_apply,\n"
        "    smul_eq_mul] using\n"
        "    (show\n"
        "      inner ℂ\n"
        "          ((actualStageDiscriminantSqrtPotential Y x : ℂ) • u x) (v x) =\n"
        "        inner ℂ (u x)\n"
        "          ((actualStageDiscriminantSqrtPotential Y x : ℂ) • v x) by\n"
        "      rw [inner_smul_left, inner_smul_right, starRingEnd_apply,\n"
        "        Complex.star_def, Complex.conj_ofReal])\n",
        (Header(54186, 25, "Tactic `rewrite` failed: Did not find an occurrence of the pattern"),),
        "Pin the square-root-potential star and conjugation laws to Complex.",
        "The exact P11 residual is the square-root analogue of line 53103 with the same concrete scalar mismatch.",
    ),
    Rule(
        "projection_hamiltonian_symmetry_transport_projection_equality",
        "  rw [actualInverseEtaProjectionHamiltonian_apply,\n"
        "    actualInverseEtaProjectionHamiltonian_apply,\n"
        "    inner_sub_left, inner_sub_right]\n"
        "  rw [(actualPaperRangeInverseEtaProjection_isSymmetricProjection hY).isSymmetric u v]\n",
        "  rw [actualInverseEtaProjectionHamiltonian_apply,\n"
        "    actualInverseEtaProjectionHamiltonian_apply,\n"
        "    inner_sub_left, inner_sub_right]\n"
        "  exact congrArg (fun z : ℂ => inner ℂ u v - z)\n"
        "    ((actualPaperRangeInverseEtaProjection_isSymmetricProjection hY).isSymmetric u v)\n",
        (Header(56436, 6, "Tactic `rewrite` failed: Did not find an occurrence of the pattern"),),
        "Transport the projection symmetry equality through subtraction instead of coercion-sensitive rewriting.",
        "The exact residual is A-B=A-C, identical in shape to the surviving coordinate projection root at line 58545.",
    ),
)


SELECTED_NEW_RULES: tuple[object, ...] = ()
RULES = REANCHORED_RULES + SELECTED_NEW_RULES


FOREIGN_HELPERS: tuple[tuple[str, str, str], ...] = (
    ("probe11_early_frontier", "qym-probe11-early-frontier-static/qym_probe11_early_frontier_static.py", "9177e4fd6aa03215aec4728415d095e7e099594f6bc12facbf5a2fd879175b9a"),
    ("probe11_mid", "qym-probe11-mid-p10-authority/qym_probe11_mid_p10_authority.py", "f2adebd8803e40df538a8b85401ea5a26af4585aefe521135c77dde8576a1fc6"),
    ("probe11_tail", "qym-probe11-tail-p10-conditional/qym_probe11_tail_p10_conditional.py", "e76d0830315918d8d51c5063048b0f85ad9f4a68c8dffa2dbab19da25a9aae49"),
    ("probe11_earlymid", "qym-probe11-earlymid-p10-conditional/qym_probe11_earlymid_p10_conditional.py", "683e740e96970dd4ca53c51016f30839a4ead5c641c7c8619f5b85733e9612e6"),
    ("probe11_40k", "qym-probe11-40k-p10-conditional/qym_probe11_40k_p10_conditional.py", "6765e05b8681e4d7e13bc735c4d37ea038c75423a7d5ebc1ad73b179a99e0052"),
    ("probe11_structural50", "qym-probe11-50k-structural-p10/qym_probe11_50k_structural_p10.py", "82189532a76f4785734d851f459a67c2dc04e373d1fc70eb5a137506f2dc57ae"),
    ("probe12_refinement", "qym-probe12-p10-midlate-refinement/qym_probe12_p10_midlate_refinement.py", "058dba8e252db0562b7b83ed5d6701445b41f189db0559e06613823f1565207d"),
)


EXCLUDED = (
    {
        "lines": [53103, 54186, 56436],
        "kind": "active_probe11_refinement_not_independent",
        "reason": "each proposed repair overlaps a frozen Probe11-tail new span, so fail-closed collision policy excludes it",
    },
    {
        "lines": [53197],
        "kind": "integral_rewrite_binder_blocker",
        "reason": "integral_re still does not match the coercion-heavy integrand and no exact local bridge is established",
    },
    {
        "lines": [58924],
        "kind": "normed_space_instance_coherence_blocker",
        "reason": "PiLp.innerProductSpace.toNormedSpace and PiLp.normedSpace remain mismatched without a principled local instance equality",
    },
    {
        "lines": [52991, 53008, 54072, 54089, 55452, 56935, 57068, 57087],
        "kind": "not_selected_this_bounded_tranche",
        "reason": "no more than three new independent roots were authorized; these require separate exact producer/API analysis",
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


def verify_authority(log_raw: bytes, header_raw: bytes, diagnostics_raw: bytes) -> list[dict[str, object]]:
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
            if len(hm) != 1 or len(dm) != 1:
                raise RuntimeError(f"{rule.label}: authority mapping mismatch at {header.line}:{header.column}")
            mapped.append({"rule": rule.label, **header.__dict__, "kind": "independent_direct_root"})
    return mapped


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
            if not 52000 <= line <= 61999:
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
    foreign_rule_count = 0
    foreign_active_spans = 0
    foreign_new_spans = 0
    for name, relative, expected_sha in FOREIGN_HELPERS:
        module = load_exact_module(name, Path(__file__).resolve().parent.parent / relative, expected_sha)
        identities[name] = expected_sha
        foreign_rules = tuple(getattr(module, "RULES", ()))
        foreign_rule_count += len(foreign_rules)
        for foreign in foreign_rules:
            for variant, anchor in (("old", foreign.old), ("new", foreign.new)):
                found = spans(text, anchor)
                foreign_active_spans += len(found)
                if variant == "new":
                    foreign_new_spans += len(found)
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
    if foreign_rule_count != 60:
        raise RuntimeError(f"active Probe11 rule count {foreign_rule_count} != 60")
    if own_overlaps or equalities or overlaps:
        raise RuntimeError(f"collision: own={own_overlaps}, equalities={equalities}, foreign={overlaps}")
    return {
        "base_p10_helper_sha256": BASE_HELPER_SHA256,
        "foreign_helper_sha256": identities,
        "foreign_rule_count": foreign_rule_count,
        "own_spans_checked": len(own),
        "foreign_active_spans_checked": foreign_active_spans,
        "foreign_new_spans_active": foreign_new_spans,
        "own_span_overlaps": own_overlaps,
        "exact_anchor_equalities": equalities,
        "foreign_span_overlaps": overlaps,
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
                       "rationale": rule.rationale, "precedent": rule.precedent})
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
    mapped = verify_authority(args.probe11_log.read_bytes(),
                              args.probe11_error_headers.read_bytes(),
                              args.probe11_diagnostics.read_bytes())
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
        "scope": {"candidate_lines": [52000, 61999], "surviving_direct_roots_only": True,
                  "reanchored_rules": len(REANCHORED_RULES), "new_rules": len(SELECTED_NEW_RULES),
                  "foreign_helper_span_overlap": False, "cascade_diagnostics_selected": False,
                  "excluded": EXCLUDED},
        "source": source_shape,
        "result": result_shape,
        "repair_families": len(RULES),
        "repair_occurrences": sum(item["occurrences"] for item in rule_audit),
        "direct_diagnostics": len(mapped),
        "selected_exact_probe11_lines": sorted({header.line for rule in RULES for header in rule.headers}),
        "diagnostic_map": mapped,
        "rules": rule_audit,
        "collision_audit": collision,
        "inverse_byte_equal": True,
        "trust": after_trust,
        "execution": {"lean": False, "lake": False, "git": False, "network": False,
                      "remote": False, "repository_source_mutation": False},
    }
    args.output.write_bytes(result)
    args.audit.write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(json.dumps(record, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
