#!/usr/bin/env python3
"""Exact-Probe12 direct/refinement repairs for QYM lines 53000--59999.

The selected rules repair only concrete terminal diagnostics.  They either
reorder a.e.-representative rewrites, make a current API equality explicit,
or refine a previously active rule whose producer proof did not close.  The
structural inverse-eta bridge, every 50k direct span, and uncertain carrier
instance equalities are deliberately outside this package.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from types import ModuleType

sys.dont_write_bytecode = True

SCHEMA = "qym-probe13-tail-p12-direct-v1"
INPUT_SHA256 = "4a123f69912bd7ce2ab070433f8cad0ecc284652a9cbab634def1936e9037212"
INPUT_GIT_BLOB = "76dd931638b9a6ad50ee764c65cd14489e8be310"
INPUT_BYTES = 2_936_558
INPUT_LF = 62_068
LOG_SHA256 = "62ce7c1b4ec23a23d690c64d49e45901faec66ff751d86e314e669b8c876c398"
HEADERS_SHA256 = "0cebf8d7bbcb923165a13f68f2afbbef1843bb26d77e072252c570b8e77b0dd9"
DIAGNOSTICS_SHA256 = "16b69f25e53f28d028cbefca21d5401e25dbfaa2847bdfdc8f7532034690ca23"

OUTPUT_SHA256 = "6b1ecbc494cbaaa71a3507e604594c7ffd173ee5ebaa7e5a6f42dab4dd74b823"
OUTPUT_GIT_BLOB = "6189c7cda9d73263f2a3a335b8591daf2b184b44"
OUTPUT_BYTES = 2_936_767
OUTPUT_LF = 62_072


def sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def git_blob(raw: bytes) -> str:
    return hashlib.sha1(f"blob {len(raw)}\0".encode() + raw).hexdigest()


@dataclass(frozen=True)
class Header:
    line: int
    column: int
    message: str
    code: str | None = None


@dataclass(frozen=True)
class Rule:
    label: str
    old: str
    new: str
    headers: tuple[Header, ...]
    rationale: str
    occurrences: int = 1


RULES: tuple[Rule, ...] = (
    Rule(
        "sqrt_mul_add_reorder_representative_rewrites",
        "  rw [hsum, hout, actualStageDiscriminantSqrtProduct_apply,\n"
        "    actualStageDiscriminantSqrtProduct_apply,\n"
        "    actualStageDiscriminantSqrtProduct_apply, huv, hu, hv, mul_add]\n",
        "  rw [hsum, hout, actualStageDiscriminantSqrtProduct_apply, huv,\n"
        "    hu, hv, actualStageDiscriminantSqrtProduct_apply,\n"
        "    actualStageDiscriminantSqrtProduct_apply, mul_add]\n",
        (Header(54222, 4, "Tactic `rewrite` failed: Did not find an occurrence of the pattern"),),
        "Expose the output representatives before rewriting their product formulas.",
    ),
    Rule(
        "sqrt_mul_smul_reorder_representative_rewrites",
        "  rw [hleft, hright, actualStageDiscriminantSqrtProduct_apply,\n"
        "    actualStageDiscriminantSqrtProduct_apply, hcu, hu]\n",
        "  rw [hleft, hright, actualStageDiscriminantSqrtProduct_apply, hcu,\n"
        "    hu, actualStageDiscriminantSqrtProduct_apply]\n",
        (Header(54239, 4, "Tactic `rewrite` failed: Did not find an occurrence of the pattern"),),
        "Rewrite the scalar representative before the second product expansion.",
    ),
    Rule(
        "sqrt_operator_symmetry_pin_complex_conjugation",
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
        (Header(54336, 25, "Tactic `rewrite` failed: Did not find an occurrence of the pattern"),),
        "Pin the concrete Complex star and real-conjugation API.",
    ),
    Rule(
        "projection_hamiltonian_symmetry_transport_equality",
        "  rw [actualInverseEtaProjectionHamiltonian_apply,\n"
        "    actualInverseEtaProjectionHamiltonian_apply,\n"
        "    inner_sub_left, inner_sub_right]\n"
        "  rw [(actualPaperRangeInverseEtaProjection_isSymmetricProjection hY).isSymmetric u v]\n",
        "  rw [actualInverseEtaProjectionHamiltonian_apply,\n"
        "    actualInverseEtaProjectionHamiltonian_apply,\n"
        "    inner_sub_left, inner_sub_right]\n"
        "  exact congrArg (fun z : ℂ => inner ℂ u v - z)\n"
        "    ((actualPaperRangeInverseEtaProjection_isSymmetricProjection hY).isSymmetric u v)\n",
        (Header(56601, 6, "Tactic `rewrite` failed: Did not find an occurrence of the pattern"),),
        "Transport the proved projection equality through subtraction.",
    ),
    Rule(
        "natural_stage_cutoff_monotone_direct_add",
        "  simpa [add_comm] using add_le_add_right (Nat.cast_le.mpr hmn) 2\n",
        "  exact add_le_add_right (Nat.cast_le.mpr hmn) 2\n",
        (Header(57102, 2, "Type mismatch: After simplification, term"),),
        "Avoid simp cancelling the common real addend back to a Nat goal.",
    ),
    Rule(
        "global_projection_add_reorder_representative_rewrites",
        "  rw [hsum, hu, hv, huv, hout]\n",
        "  rw [hsum, hout, hu, hv, huv]\n",
        (Header(57235, 12, "Tactic `rewrite` failed: Did not find an occurrence of the pattern"),),
        "Expose the sum output representative before rewriting its summands.",
    ),
    Rule(
        "global_projection_smul_reorder_representative_rewrites",
        "  rw [hleft, hu, hcu, hright]\n",
        "  rw [hleft, hright, hu, hcu]\n",
        (Header(57254, 13, "Tactic `rewrite` failed: Did not find an occurrence of the pattern"),),
        "Expose the scalar output representative before rewriting its input.",
    ),
    Rule(
        "projection_error_bound_restore_natural_stage_unfold",
        "  by_cases hx : x ∈ naturalStageSet n\n"
        "  · simp [globalStageProjectionErrorDensity,\n"
        "      globalL2DominatingDensity,\n"
        "      globalStageProjectionRepresentative, hx]\n"
        "  · simp [globalStageProjectionErrorDensity,\n"
        "      globalL2DominatingDensity,\n"
        "      globalStageProjectionRepresentative, hx]\n",
        "  by_cases hx : x ∈ naturalStageSet n\n"
        "  · simp [globalStageProjectionErrorDensity,\n"
        "      globalL2DominatingDensity, naturalStageSet,\n"
        "      globalStageProjectionRepresentative, hx]\n"
        "  · simp [globalStageProjectionErrorDensity,\n"
        "      globalL2DominatingDensity, naturalStageSet,\n"
        "      globalStageProjectionRepresentative, hx]\n",
        (Header(57582, 2, "unsolved goals"), Header(57585, 2, "unsolved goals")),
        "Unfold the natural-stage alias in both the indicator and membership proof.",
    ),
    Rule(
        "projection_error_eventually_zero_restore_stage_unfold",
        "  filter_upwards [eventually_mem_naturalStageSet x] with n hn\n"
        "  simp [globalStageProjectionErrorDensity,\n"
        "    globalStageProjectionRepresentative, hn]\n",
        "  filter_upwards [eventually_mem_naturalStageSet x] with n hn\n"
        "  simp [globalStageProjectionErrorDensity, naturalStageSet,\n"
        "    globalStageProjectionRepresentative, hn]\n",
        (Header(57607, 66, "unsolved goals"),),
        "Unfold the same stage alias before reducing the on-stage indicator.",
    ),
    Rule(
        "projection_error_tendsto_restore_stage_unfold",
        "  simp [globalStageProjectionErrorDensity,\n"
        "    globalStageProjectionRepresentative, hx]\n",
        "  simp [globalStageProjectionErrorDensity, naturalStageSet,\n"
        "    globalStageProjectionRepresentative, hx]\n",
        (Header(57616, 21, "unsolved goals"),),
        "Unfold the stage alias in the eventual constant-zero proof.",
    ),
    Rule(
        "potential_symmetry_transport_ground_equality",
        "  rw [inner_smul_left, inner_smul_right, starRingEnd_apply,\n"
        "    Complex.star_def, Complex.conj_ofReal,\n"
        "    groundProjection_isSymmetric u v]\n",
        "  rw [inner_smul_left, inner_smul_right, starRingEnd_apply,\n"
        "    Complex.star_def, Complex.conj_ofReal]\n"
        "  exact congrArg\n"
        "    (fun z : ℂ => (((1 : ℝ) / 4 : ℝ) : ℂ) * z)\n"
        "    (groundProjection_isSymmetric u v)\n",
        (Header(58807, 4, "Tactic `rewrite` failed: Did not find an occurrence of the pattern"),),
        "Transport symmetry through multiplication instead of coercion-sensitive rw.",
    ),
    Rule(
        "hamiltonian_form_re_self_finish_complex_re",
        "@[simp]\n"
        "theorem coordinateHamiltonianForm_re_self (u : CoordinateL2) :\n"
        "    RCLike.re (coordinateHamiltonianForm u u) =\n"
        "      ‖covariantDerivative u‖ ^ 2 + (1 / 4 : ℝ) * ‖groundProjection u‖ ^ 2 := by\n"
        "  rw [coordinateHamiltonianForm_apply,\n"
        "    inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]\n"
        "  simp\n",
        "@[simp]\n"
        "theorem coordinateHamiltonianForm_re_self (u : CoordinateL2) :\n"
        "    RCLike.re (coordinateHamiltonianForm u u) =\n"
        "      ‖covariantDerivative u‖ ^ 2 + (1 / 4 : ℝ) * ‖groundProjection u‖ ^ 2 := by\n"
        "  rw [coordinateHamiltonianForm_apply,\n"
        "    inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]\n"
        "  simp\n"
        "  simp only [Complex.ofReal_re]\n",
        (Header(58992, 78, "unsolved goals"),),
        "Finish the residual real-part coercions with the concrete Complex API.",
    ),
)


FOREIGN_HELPERS: tuple[tuple[str, str, str], ...] = (
    ("probe11_tail", "qym-probe11-tail-p10-conditional/qym_probe11_tail_p10_conditional.py", "e76d0830315918d8d51c5063048b0f85ad9f4a68c8dffa2dbab19da25a9aae49"),
    ("probe12_tail", "qym-probe12-52k61k-p11-conditional/qym_probe12_52k61k_p11_conditional.py", "7066e3297bd171ec58a4547ed426a8d9a6228abf4de78bf3ad203d880ef7f795"),
    ("probe13_50k", "qym-probe13-50k50599-p12-reanchored/qym_probe13_50k50599_p12_reanchored.py", "a2eacbaebd1f3fddcb865a551613ea8ebbcdf12d74869be2b61c663a0891ed50"),
)

# Frozen from the exact-P12 forward and matching-inverse collision scans.
EXPECTED_EQUALITIES: frozenset[tuple[str, str, str, str, str]] = frozenset({
    ("global_projection_add_reorder_representative_rewrites", "new", "probe11_tail", "global_stage_projection_add_restore_rewrite_order", "old"),
    ("global_projection_add_reorder_representative_rewrites", "old", "probe11_tail", "global_stage_projection_add_restore_rewrite_order", "new"),
    ("global_projection_smul_reorder_representative_rewrites", "new", "probe11_tail", "global_stage_projection_smul_restore_rewrite_order", "old"),
    ("global_projection_smul_reorder_representative_rewrites", "old", "probe11_tail", "global_stage_projection_smul_restore_rewrite_order", "new"),
    ("hamiltonian_form_re_self_finish_complex_re", "new", "probe12_tail", "hamiltonian_form_re_self_drop_redundant_final_simp", "old"),
    ("hamiltonian_form_re_self_finish_complex_re", "old", "probe12_tail", "hamiltonian_form_re_self_drop_redundant_final_simp", "new"),
    ("natural_stage_cutoff_monotone_direct_add", "new", "probe11_tail", "natural_stage_cutoff_normalize_add_comm", "old"),
    ("natural_stage_cutoff_monotone_direct_add", "old", "probe11_tail", "natural_stage_cutoff_normalize_add_comm", "new"),
    ("potential_symmetry_transport_ground_equality", "old", "probe12_tail", "potential_symmetry_pin_complex_real_conjugation", "new"),
    ("projection_error_bound_restore_natural_stage_unfold", "new", "probe12_tail", "projection_error_bound_preserve_natural_stage_name", "old"),
    ("projection_error_bound_restore_natural_stage_unfold", "old", "probe12_tail", "projection_error_bound_preserve_natural_stage_name", "new"),
    ("projection_error_eventually_zero_restore_stage_unfold", "new", "probe12_tail", "projection_error_eventually_zero_preserve_stage_name", "old"),
    ("projection_error_eventually_zero_restore_stage_unfold", "old", "probe12_tail", "projection_error_eventually_zero_preserve_stage_name", "new"),
    ("projection_error_tendsto_restore_stage_unfold", "new", "probe12_tail", "projection_error_pointwise_tendsto_preserve_stage_name", "old"),
    ("projection_error_tendsto_restore_stage_unfold", "old", "probe12_tail", "projection_error_pointwise_tendsto_preserve_stage_name", "new"),
})
EXPECTED_FORWARD_OVERLAPS: frozenset[tuple[str, str, str]] = frozenset({
    ("global_projection_add_reorder_representative_rewrites", "probe11_tail:global_stage_projection_add_restore_rewrite_order", "new"),
    ("global_projection_smul_reorder_representative_rewrites", "probe11_tail:global_stage_projection_smul_restore_rewrite_order", "new"),
    ("hamiltonian_form_re_self_finish_complex_re", "probe12_tail:hamiltonian_form_re_self_drop_redundant_final_simp", "new"),
    ("natural_stage_cutoff_monotone_direct_add", "probe11_tail:natural_stage_cutoff_normalize_add_comm", "new"),
    ("potential_symmetry_transport_ground_equality", "probe12_tail:potential_symmetry_pin_complex_real_conjugation", "new"),
    ("projection_error_bound_restore_natural_stage_unfold", "probe12_tail:projection_error_bound_preserve_natural_stage_name", "new"),
    ("projection_error_eventually_zero_restore_stage_unfold", "probe12_tail:projection_error_eventually_zero_preserve_stage_name", "new"),
    ("projection_error_tendsto_restore_stage_unfold", "probe12_tail:projection_error_pointwise_tendsto_preserve_stage_name", "new"),
    ("projection_hamiltonian_symmetry_transport_equality", "probe11_tail:projection_hamiltonian_attach_isSymmetric_projection", "new"),
    ("sqrt_mul_add_reorder_representative_rewrites", "probe11_tail:discriminant_sqrt_mul_add_expose_product_producer", "new"),
    ("sqrt_mul_smul_reorder_representative_rewrites", "probe11_tail:discriminant_sqrt_mul_smul_expose_product_producer", "new"),
    ("sqrt_operator_symmetry_pin_complex_conjugation", "probe11_tail:discriminant_sqrt_real_multiplier_use_current_inner_smul_api", "new"),
})
EXPECTED_INVERSE_OVERLAPS: frozenset[tuple[str, str, str]] = frozenset({
    ("global_projection_add_reorder_representative_rewrites", "probe11_tail:global_stage_projection_add_restore_rewrite_order", "old"),
    ("global_projection_smul_reorder_representative_rewrites", "probe11_tail:global_stage_projection_smul_restore_rewrite_order", "old"),
    ("hamiltonian_form_re_self_finish_complex_re", "probe12_tail:hamiltonian_form_re_self_drop_redundant_final_simp", "new"),
    ("hamiltonian_form_re_self_finish_complex_re", "probe12_tail:hamiltonian_form_re_self_drop_redundant_final_simp", "old"),
    ("natural_stage_cutoff_monotone_direct_add", "probe11_tail:natural_stage_cutoff_normalize_add_comm", "old"),
    ("projection_error_bound_restore_natural_stage_unfold", "probe12_tail:projection_error_bound_preserve_natural_stage_name", "old"),
    ("projection_error_eventually_zero_restore_stage_unfold", "probe12_tail:projection_error_eventually_zero_preserve_stage_name", "old"),
    ("projection_error_tendsto_restore_stage_unfold", "probe12_tail:projection_error_pointwise_tendsto_preserve_stage_name", "old"),
})


def shape(raw: bytes) -> dict[str, object]:
    raw.decode("utf-8", errors="strict")
    return {"sha256": sha256(raw), "git_blob": git_blob(raw), "bytes": len(raw),
            "lf": raw.count(b"\n"), "cr": b"\r" in raw, "nul": b"\0" in raw,
            "bom": raw.startswith(b"\xef\xbb\xbf"), "terminal_lf": raw.endswith(b"\n")}


def trust(text: str) -> dict[str, int]:
    return {
        "sorry": len(re.findall(r"\bsorry\b", text)),
        "admit": len(re.findall(r"\badmit\b", text)),
        "native_decide": len(re.findall(r"\bnative_decide\b", text)),
        "Lean.ofReduceBool": text.count("Lean.ofReduceBool"),
        "axiom_declaration": len(re.findall(r"(?m)^\s*axiom\s+", text)),
        "unsafe_declaration": len(re.findall(r"(?m)^\s*unsafe\s+", text)),
        "maxHeartbeats_zero": len(re.findall(r"set_option\s+maxHeartbeats\s+0\b", text)),
    }


def expected_input() -> dict[str, object]:
    return {"sha256": INPUT_SHA256, "git_blob": INPUT_GIT_BLOB, "bytes": INPUT_BYTES,
            "lf": INPUT_LF, "cr": False, "nul": False, "bom": False, "terminal_lf": True}


def expected_output() -> dict[str, object]:
    return {"sha256": OUTPUT_SHA256, "git_blob": OUTPUT_GIT_BLOB, "bytes": OUTPUT_BYTES,
            "lf": OUTPUT_LF, "cr": False, "nul": False, "bom": False, "terminal_lf": True}


def unsealed() -> bool:
    return not OUTPUT_SHA256 and not OUTPUT_GIT_BLOB and OUTPUT_BYTES == 0 and OUTPUT_LF == 0


def check_shape(actual: dict[str, object], expected: dict[str, object], bootstrap: bool = False) -> None:
    keys = ("cr", "nul", "bom", "terminal_lf") if bootstrap else tuple(expected)
    if any(actual[k] != expected[k] for k in keys):
        raise RuntimeError(f"shape mismatch: {actual} != {expected}")


def verify_authority(log: bytes, headers: bytes, diagnostics: bytes) -> list[dict[str, object]]:
    for label, raw, expected in (("log", log, LOG_SHA256), ("headers", headers, HEADERS_SHA256),
                                 ("diagnostics", diagnostics, DIAGNOSTICS_SHA256)):
        if sha256(raw) != expected:
            raise RuntimeError(f"Probe12 {label} identity mismatch")
    hs = headers.decode().splitlines()
    rows = [json.loads(x) for x in diagnostics.decode().splitlines()]
    if len(hs) != 183 or sum(r.get("severity") == "error" for r in rows) != 183:
        raise RuntimeError("Probe12 error count mismatch")
    mapped = []
    for rule in RULES:
        for h in rule.headers:
            hm = [x for x in hs if x.startswith(
                f"PrimalitySheafVerification/QYM.lean:{h.line}:{h.column}: error" +
                (f"({h.code})" if h.code else "") + f": {h.message}")]
            dm = [r for r in rows if r.get("severity") == "error" and r.get("line") == h.line
                  and r.get("column") == h.column and r.get("code") == h.code
                  and str(r.get("message", "")).startswith(h.message)]
            if len(hm) != 1 or len(dm) != 1:
                raise RuntimeError(f"diagnostic mismatch: {rule.label} {h.line}:{h.column}")
            mapped.append({"rule": rule.label, **h.__dict__})
    return mapped


def spans(text: str, needle: str) -> list[tuple[int, int]]:
    out = []
    start = 0
    while True:
        i = text.find(needle, start)
        if i < 0:
            return out
        out.append((i, i + len(needle)))
        start = i + 1


def load_foreign(name: str, relative: str, expected: str) -> ModuleType:
    path = Path(__file__).resolve().parent.parent / relative
    raw = path.read_bytes()
    if sha256(raw) != expected:
        raise RuntimeError(f"foreign helper drift: {name}")
    module_name = "_qym_probe13_tail_" + name
    spec = importlib.util.spec_from_file_location(module_name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot import {name}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[module_name] = module
    spec.loader.exec_module(module)
    return module


def collision_audit(text: str, inverse: bool, bootstrap: bool = False) -> dict[str, object]:
    own = []
    for rule in RULES:
        active = rule.new if inverse else rule.old
        found = spans(text, active)
        if len(found) != rule.occurrences:
            raise RuntimeError(f"active anchor count: {rule.label}: {len(found)}")
        for a, b in found:
            line = text.count("\n", 0, a) + 1
            if not 53000 <= line <= 59999:
                raise RuntimeError(f"scope violation: {rule.label}: {line}")
            own.append((a, b, rule.label))
    equalities = set()
    overlaps = set()
    identities = {}
    for name, relative, expected in FOREIGN_HELPERS:
        module = load_foreign(name, relative, expected)
        identities[name] = expected
        for foreign in module.RULES:
            for fv, fa in (("old", foreign.old), ("new", foreign.new)):
                for own_rule in RULES:
                    for ov, oa in (("old", own_rule.old), ("new", own_rule.new)):
                        if oa == fa:
                            equalities.add((own_rule.label, ov, name, foreign.label, fv))
                for a, b in spans(text, fa):
                    for oa, ob, label in own:
                        if max(a, oa) < min(b, ob):
                            overlaps.add((label, f"{name}:{foreign.label}", fv))
    expected_overlap = EXPECTED_INVERSE_OVERLAPS if inverse else EXPECTED_FORWARD_OVERLAPS
    if not bootstrap and (equalities != EXPECTED_EQUALITIES or overlaps != expected_overlap):
        raise RuntimeError(f"collision contract mismatch: equalities={sorted(equalities)} overlaps={sorted(overlaps)}")
    return {"foreign_sha256": identities, "equalities": sorted(equalities),
            "active_overlaps": sorted(overlaps), "own_spans": len(own),
            "bootstrap_contract": bootstrap}


def transform(text: str, inverse: bool = False) -> tuple[str, list[dict[str, object]]]:
    audit = []
    ordered = tuple(reversed(RULES)) if inverse else RULES
    for rule in ordered:
        old, new = (rule.new, rule.old) if inverse else (rule.old, rule.new)
        count = text.count(old)
        if count != rule.occurrences:
            raise RuntimeError(f"anchor count: {rule.label}: {count}")
        text = text.replace(old, new)
        audit.append({"label": rule.label, "direction": "inverse" if inverse else "forward",
                      "occurrences": count, "headers": [h.__dict__ for h in rule.headers],
                      "rationale": rule.rationale})
    return text, audit


apply_rules = transform


def main() -> int:
    p = argparse.ArgumentParser()
    p.add_argument("input", type=Path)
    p.add_argument("output", type=Path)
    p.add_argument("--probe12-log", type=Path, required=True)
    p.add_argument("--probe12-error-headers", type=Path, required=True)
    p.add_argument("--probe12-diagnostics", type=Path, required=True)
    p.add_argument("--audit", type=Path, required=True)
    p.add_argument("--mode", choices=("forward", "inverse"), default="forward")
    p.add_argument("--bootstrap-seal", action="store_true")
    args = p.parse_args()
    inverse = args.mode == "inverse"
    if args.bootstrap_seal != unsealed():
        raise RuntimeError("bootstrap/seal state mismatch")
    source = args.input.read_bytes()
    source_shape = shape(source)
    check_shape(source_shape, expected_output() if inverse else expected_input(), args.bootstrap_seal)
    mapped = verify_authority(args.probe12_log.read_bytes(), args.probe12_error_headers.read_bytes(),
                              args.probe12_diagnostics.read_bytes())
    text = source.decode()
    collisions = collision_audit(text, inverse, args.bootstrap_seal)
    before = trust(text)
    result_text, rules = transform(text, inverse)
    result = result_text.encode()
    result_shape = shape(result)
    check_shape(result_shape, expected_input() if inverse else expected_output(), args.bootstrap_seal)
    after = trust(result_text)
    if before != after or any(after.values()):
        raise RuntimeError(f"trust0 failure: {before} -> {after}")
    restored, _ = transform(result_text, not inverse)
    if restored.encode() != source:
        raise RuntimeError("byte inverse failure")
    if args.output.exists() or args.audit.exists():
        raise RuntimeError("refusing overwrite")
    record = {"schema": SCHEMA, "status": "STATIC_PASS_EXACT_PROBE12_NOT_LEAN_EXECUTED",
              "activation": False, "mode": args.mode,
              "authority": {"candidate_sha256": INPUT_SHA256, "log_sha256": LOG_SHA256,
                            "headers_sha256": HEADERS_SHA256, "diagnostics_sha256": DIAGNOSTICS_SHA256,
                            "errors": 183, "warnings": 350, "panic": 0, "exit": 1},
              "source": source_shape, "result": result_shape,
              "repair_families": len(RULES), "repair_occurrences": sum(r["occurrences"] for r in rules),
              "direct_diagnostics": len(mapped), "diagnostic_map": mapped, "rules": rules,
              "collision_audit": collisions, "inverse_byte_equal": True, "trust": after,
              "excluded": [53347, 55615, 58961, 58975, 59091],
              "execution": {"lean": False, "lake": False, "git": False, "network": False,
                            "remote": False, "repository_source_mutation": False}}
    args.output.write_bytes(result)
    args.audit.write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(json.dumps(record, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
