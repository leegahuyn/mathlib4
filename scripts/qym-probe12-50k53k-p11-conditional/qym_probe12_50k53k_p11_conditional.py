#!/usr/bin/env python3
"""Conditional local repairs for exact terminal-Probe11 lines 50000-53999.

The selected rules are limited to seven direct, local diagnostics: four
indicator negative-branch reductions, two pointwise Lp algebra rewrites, and
one declared downstream refinement of the active Probe11 tail's concrete
Complex conjugation rule.  The known InverseEtaBase carrier bridge and all
other structural/cascade clusters are deliberately excluded.

This transformer is activation-disabled, byte-locked, exact-counted,
reversible, trust0, and collision-audited against the active Probe11 helpers
and the frozen exact-Probe11 Probe12 siblings.  It never invokes Lean, Lake,
Git, a network, or a remote service, and it never mutates repository sources.
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

SCHEMA = "qym-probe12-50k53k-p11-conditional-v1"
INPUT_SHA256 = "d8290febb2b1c69cc8b911bcb672303beede1b87db290bd37c6608e39356cf25"
INPUT_GIT_BLOB = "9b5ba50acc8e2f3d6f55cf8cef6fc505926410cd"
INPUT_BYTES = 2_928_376
INPUT_LF = 61_891
LOG_SHA256 = "474f153278507d0ead7fe21675f326def15556281bd7b5cf67392836ea5ea97e"
HEADERS_SHA256 = "b0fe7508ba87fc324236cce71b74c59d042a0833ec1c101a1ae625a1f24dd4e6"
DIAGNOSTICS_SHA256 = "d9259b316d1c1317ea7e11f8f0370feaabacb3a2ae6066c3133ab748a2dee504"

# Filled from exactly one deterministic bootstrap projection, then frozen.
OUTPUT_SHA256 = "d71251281812bfc7ac9e8fc026417641a8402508f829de3fade71b44f3d04f61"
OUTPUT_GIT_BLOB = "5137efc0a551f8b26da079d5879012bf0791cb0c"
OUTPUT_BYTES = 2_928_674
OUTPUT_LF = 61_905


def sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def git_blob(raw: bytes) -> str:
    return hashlib.sha1(f"blob {len(raw)}\0".encode("ascii") + raw).hexdigest()


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
    precedent: str
    occurrences: int = 1


RULES: tuple[Rule, ...] = (
    Rule(
        "ambient_zero_extension_add_rewrite_all_negative_indicators",
        "  · simp only [hx, Set.indicator_of_notMem, add_zero]\n",
        "  · first\n"
        "    | rfl\n"
        "    | rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx,\n"
        "        Set.indicator_of_notMem hx, add_zero]\n",
        (Header(50860, 4, "`simp` made no progress"),),
        "Accept the definitionally reflexive branch first; otherwise rewrite the three concrete negative indicators in occurrence order and close 0 = 0 + 0.",
        "Exact Probe7 closed the no-progress form by rfl, while exact Probe9 later exposed propositionally reduced indicators; the ordered fallback covers both witnessed elaboration states without a broad simp.",
    ),
    Rule(
        "ambient_zero_extension_smul_rewrite_both_negative_indicators",
        "  · simp only [hx, Set.indicator_of_notMem, smul_zero]\n",
        "  · first\n"
        "    | rfl\n"
        "    | rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx,\n"
        "        smul_zero]\n",
        (Header(50880, 4, "`simp` made no progress"),),
        "Accept definitional reflexivity first; otherwise rewrite both negative indicators explicitly before reducing scalar multiplication by zero.",
        "This guarded form mirrors the witnessed add/indicator elaboration split and retains the exact repeated-rewrite fallback used elsewhere in the source.",
    ),
    Rule(
        "ambient_zero_extension_trans_rewrite_double_negative_branch",
        "    · simp only [hx, hxZ, Set.indicator_of_notMem]\n",
        "    · first\n"
        "      | rfl\n"
        "      | rw [Set.indicator_of_notMem hxZ,\n"
        "          Set.indicator_of_notMem hx]\n",
        (Header(50998, 6, "`simp` made no progress"),),
        "Try the exact historical reflexive close first; if the indicators remain propositionally exposed, reduce the outer Z-stage and direct Y-stage indicators with distinct witnesses.",
        "Probe7's exact no-progress root closed by rfl, while Probe9 later reported rfl failure on the same branch; the explicit two-indicator fallback covers that exact alternate state.",
    ),
    Rule(
        "inner_indicator_right_rewrite_negative_indicators",
        "  · simp only [hx, Set.indicator_of_notMem, inner_zero_right]\n",
        "  · first\n"
        "    | rfl\n"
        "    | rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx,\n"
        "        inner_zero_right]\n",
        (Header(51019, 4, "`simp` made no progress"),),
        "Try definitional reflexivity first; otherwise expose zero on both sides with two explicit indicator rewrites and reduce the right zero input of the inner product.",
        "Probe7's exact no-progress root closed by rfl, Probe9 later exposed a non-definitional form, and the same source supplies the explicit repeated-indicator/inner_zero_right fallback.",
    ),
    Rule(
        "discriminant_mul_add_expose_pi_add_before_local_representatives",
        "  rw [hsum, hout, actualStageDiscriminantProduct_apply,\n"
        "    actualStageDiscriminantProduct_apply,\n"
        "    actualStageDiscriminantProduct_apply, huv, hu, hv, mul_add]\n",
        "  rw [hsum, hout, actualStageDiscriminantProduct_apply, huv,\n"
        "    Pi.add_apply, Pi.add_apply, hu,\n"
        "    actualStageDiscriminantProduct_apply, hv,\n"
        "    actualStageDiscriminantProduct_apply, mul_add]\n",
        (Header(52991, 4, "Tactic `rewrite` failed: Did not find an occurrence of the pattern"),),
        "Expose both pointwise additions before rewriting the local representative equalities and only then unfold the two resulting products.",
        "The exact residual shows the first product already unfolded while the right side remains a Pi.add application; the new order follows those printed producers exactly.",
    ),
    Rule(
        "discriminant_mul_smul_expose_pi_smul_before_local_representative",
        "  rw [hleft, hright, actualStageDiscriminantProduct_apply,\n"
        "    actualStageDiscriminantProduct_apply, hcu, hu]\n",
        "  rw [hleft, hright, actualStageDiscriminantProduct_apply, hcu,\n"
        "    Pi.smul_apply, Pi.smul_apply, hu,\n"
        "    actualStageDiscriminantProduct_apply]\n",
        (Header(53008, 4, "Tactic `rewrite` failed: Did not find an occurrence of the pattern"),),
        "Expose both pointwise scalar applications before using hu, then unfold the product introduced by hu.",
        "The exact residual prints one coeFn_smul application on each side and no product on the right, fixing the rewrite dependency order without changing the final ring proof.",
    ),
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
        "The exact residual is starRingEnd Complex on a real cast, and exact compiled source precedents use Complex.star_def with Complex.conj_ofReal.",
    ),
)


FOREIGN_HELPERS: tuple[tuple[str, str, str], ...] = (
    ("probe11_early_frontier", "qym-probe11-early-frontier-static/qym_probe11_early_frontier_static.py", "9177e4fd6aa03215aec4728415d095e7e099594f6bc12facbf5a2fd879175b9a"),
    ("probe11_mid", "qym-probe11-mid-p10-authority/qym_probe11_mid_p10_authority.py", "f2adebd8803e40df538a8b85401ea5a26af4585aefe521135c77dde8576a1fc6"),
    ("probe11_tail", "qym-probe11-tail-p10-conditional/qym_probe11_tail_p10_conditional.py", "e76d0830315918d8d51c5063048b0f85ad9f4a68c8dffa2dbab19da25a9aae49"),
    ("probe11_earlymid", "qym-probe11-earlymid-p10-conditional/qym_probe11_earlymid_p10_conditional.py", "683e740e96970dd4ca53c51016f30839a4ead5c641c7c8619f5b85733e9612e6"),
    ("probe11_40k", "qym-probe11-40k-p10-conditional/qym_probe11_40k_p10_conditional.py", "6765e05b8681e4d7e13bc735c4d37ea038c75423a7d5ebc1ad73b179a99e0052"),
    ("probe11_structural50", "qym-probe11-50k-structural-p10/qym_probe11_50k_structural_p10.py", "82189532a76f4785734d851f459a67c2dc04e373d1fc70eb5a137506f2dc57ae"),
    ("probe12_refinement", "qym-probe12-p10-midlate-refinement/qym_probe12_p10_midlate_refinement.py", "058dba8e252db0562b7b83ed5d6701445b41f189db0559e06613823f1565207d"),
    ("probe12_frontier_p11", "qym-probe12-early-frontier-p11-conditional/qym_probe12_early_frontier_p11_conditional.py", "35b5ccf5f04899c810ca798cbcf700230fdfc4b930d16ab5d9cf646584954215"),
    ("probe12_36k42k_p11", "qym-probe12-36k42k-p11-reanchored/qym_probe12_36k42k_p11_reanchored.py", "5bd02f57232ac30c336b3e13574b7cba4dc4b0998f159e3fdebd41ed6354a365"),
    ("probe12_43k49k_p11", "qym-probe12-43k49k-p11-conditional/qym_probe12_43k49k_p11_conditional.py", "5070ada686ac425b76403ae53210e586bda305a8a70606d6d3bc6529ff2b2523"),
    ("probe12_52k61k_p11", "qym-probe12-52k61k-p11-conditional/qym_probe12_52k61k_p11_conditional.py", "7066e3297bd171ec58a4547ed426a8d9a6228abf4de78bf3ad203d880ef7f795"),
)


DECLARED_REFINEMENTS: dict[str, tuple[str, str]] = {
    "discriminant_mul_add_expose_pi_add_before_local_representatives": (
        "probe11_tail",
        "discriminant_mul_add_expose_product_producer",
    ),
    "discriminant_mul_smul_expose_pi_smul_before_local_representative": (
        "probe11_tail",
        "discriminant_mul_smul_expose_product_producer",
    ),
    "discriminant_operator_symmetry_pin_complex_conjugation": (
        "probe11_tail",
        "discriminant_real_multiplier_use_current_inner_smul_api",
    ),
}
DECLARED_EXACT_EQUALITIES: frozenset[str] = frozenset()
DECLARED_OVERLAP_VARIANTS: dict[str, frozenset[str]] = {
    "discriminant_mul_add_expose_pi_add_before_local_representatives": frozenset({"new"}),
    "discriminant_mul_smul_expose_pi_smul_before_local_representative": frozenset({"new"}),
    "discriminant_operator_symmetry_pin_complex_conjugation": frozenset({"new"}),
}
DECLARED_INVERSE_OVERLAP_VARIANTS: dict[str, frozenset[str]] = {
    "discriminant_mul_add_expose_pi_add_before_local_representatives": frozenset(),
    "discriminant_mul_smul_expose_pi_smul_before_local_representative": frozenset(),
    "discriminant_operator_symmetry_pin_complex_conjugation": frozenset(),
}


EXCLUDED: tuple[dict[str, object], ...] = (
    {
        "lines": [50024, 50031, 50033, 50140, 50155, 50158, 50161, 50167, 50190, 50252, 50261, 50273, 50274, 50280, 50281, 50283, 50286, 50288, 50290, 50297, 50299, 50307, 50323, 50377, 50381, 50437, 50506, 50510, 50544],
        "kind": "measure_submodule_structural_api_cluster",
        "reason": "the unknown measure map/comap APIs and the ensuing section/submodule elaboration failures have no verified local replacement producer",
    },
    {
        "lines": [50069],
        "kind": "owned_by_frozen_probe12_43k49k_p11",
        "reason": "excluded from this package because the exact sibling helper 5070ada6 owns this surviving direct diagnostic",
    },
    {
        "lines": [51201, 51216, 51222, 51230, 51235, 51300, 51383, 51417, 51420, 51423, 51445, 51464, 51514, 51940],
        "kind": "inverse_eta_base_carrier_bridge_blocker",
        "reason": "the original-versus-effective quotient carrier and chart transports require a validated Equiv/Homeomorph construction; no broad bridge is guessed here",
    },
    {
        "lines": [53197],
        "kind": "integral_rewrite_binder_blocker",
        "reason": "integral_re still does not match the coercion-heavy integrand and no exact local binder bridge is established",
    },
    {
        "lines": [53424],
        "kind": "owned_by_frozen_probe12_52k61k_p11",
        "reason": "excluded from this package because the exact sibling helper 7066e329 owns this surviving direct diagnostic",
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
    return {
        "sorry": len(re.findall(r"\bsorry\b", text)),
        "admit": len(re.findall(r"\badmit\b", text)),
        "native_decide": len(re.findall(r"\bnative_decide\b", text)),
        "Lean.ofReduceBool": text.count("Lean.ofReduceBool"),
        "axiom_declaration": len(re.findall(r"(?m)^\s*axiom\s+", text)),
        "unsafe_declaration": len(re.findall(r"(?m)^\s*unsafe\s+", text)),
        "maxHeartbeats_zero": len(re.findall(r"set_option\s+maxHeartbeats\s+0\b", text)),
    }


def input_expected() -> dict[str, object]:
    return {
        "sha256": INPUT_SHA256,
        "git_blob": INPUT_GIT_BLOB,
        "bytes": INPUT_BYTES,
        "lf": INPUT_LF,
        "cr": False,
        "nul": False,
        "bom": False,
        "terminal_lf": True,
    }


def output_expected() -> dict[str, object]:
    return {
        "sha256": OUTPUT_SHA256,
        "git_blob": OUTPUT_GIT_BLOB,
        "bytes": OUTPUT_BYTES,
        "lf": OUTPUT_LF,
        "cr": False,
        "nul": False,
        "bom": False,
        "terminal_lf": True,
    }


def sentinels_unsealed() -> bool:
    return OUTPUT_SHA256 == "" and OUTPUT_GIT_BLOB == "" and OUTPUT_BYTES == 0 and OUTPUT_LF == 0


def check_shape(actual: dict[str, object], expected: dict[str, object], *, unsealed: bool = False) -> None:
    keys = ("cr", "nul", "bom", "terminal_lf") if unsealed else tuple(expected)
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
            dm = [
                row
                for row in rows
                if row.get("severity") == "error"
                and row.get("line") == header.line
                and row.get("column") == header.column
                and row.get("code") == header.code
                and str(row.get("message", "")).startswith(header.message)
            ]
            if len(hm) != 1 or len(dm) != 1:
                raise RuntimeError(f"{rule.label}: authority mapping mismatch at {header.line}:{header.column}")
            mapped.append(
                {
                    "rule": rule.label,
                    **header.__dict__,
                    "kind": (
                        "declared_active_probe11_rule_refinement"
                        if rule.label in DECLARED_REFINEMENTS
                        else "exact_probe11_direct_local_root"
                    ),
                }
            )
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


def load_foreign(name: str, relative: str, expected_sha: str) -> ModuleType:
    path = Path(__file__).resolve().parent.parent / relative
    raw = path.read_bytes()
    if sha256(raw) != expected_sha:
        raise RuntimeError(f"foreign helper identity mismatch: {name}: {sha256(raw)}")
    module_name = "_qym_50k53k_foreign_" + name
    spec = importlib.util.spec_from_file_location(module_name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot import foreign helper: {name}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[module_name] = module
    spec.loader.exec_module(module)
    return module


def audit_collisions(text: str, *, inverse: bool) -> dict[str, object]:
    own: list[tuple[int, int, str]] = []
    for rule in RULES:
        active = rule.new if inverse else rule.old
        found = spans(text, active)
        if len(found) != rule.occurrences:
            raise RuntimeError(f"{rule.label}: active anchor count {len(found)}")
        for start, end in found:
            line = text.count("\n", 0, start) + 1
            if not 50000 <= line <= 53999:
                raise RuntimeError(f"{rule.label}: scope violation at line {line}")
            own.append((start, end, rule.label))
    own_sorted = sorted(own)
    own_overlaps: list[dict[str, object]] = []
    for left, right in zip(own_sorted, own_sorted[1:]):
        if left[1] > right[0]:
            own_overlaps.append({"left": left[2], "right": right[2]})
    equalities: list[dict[str, str]] = []
    overlaps: list[dict[str, object]] = []
    foreign_active_spans = 0
    identities: dict[str, str] = {}
    for name, relative, expected_sha in FOREIGN_HELPERS:
        module = load_foreign(name, relative, expected_sha)
        identities[name] = expected_sha
        foreign_rules = getattr(module, "RULES", None)
        if foreign_rules is None:
            raise RuntimeError(f"foreign helper has no RULES: {name}")
        for foreign in foreign_rules:
            for variant, anchor in (("old", foreign.old), ("new", foreign.new)):
                found = spans(text, anchor)
                foreign_active_spans += len(found)
                for own_rule in RULES:
                    for own_variant, own_anchor in (("old", own_rule.old), ("new", own_rule.new)):
                        if own_anchor == anchor:
                            equalities.append(
                                {
                                    "own": own_rule.label,
                                    "own_variant": own_variant,
                                    "foreign": f"{name}:{foreign.label}",
                                    "foreign_variant": variant,
                                }
                            )
                for fstart, fend in found:
                    for ostart, oend, own_label in own:
                        if max(fstart, ostart) < min(fend, oend):
                            overlaps.append(
                                {
                                    "own": own_label,
                                    "foreign": f"{name}:{foreign.label}",
                                    "foreign_variant": variant,
                                    "own_span": [ostart, oend],
                                    "foreign_span": [fstart, fend],
                                }
                            )
    expected_equalities = {
        (own, "old", f"{owner_name}:{owner_rule}", "new")
        for own, (owner_name, owner_rule) in DECLARED_REFINEMENTS.items()
        if own in DECLARED_EXACT_EQUALITIES
    }
    actual_equalities = {
        (item["own"], item["own_variant"], item["foreign"], item["foreign_variant"])
        for item in equalities
    }
    expected_overlaps = {
        (own, f"{owner_name}:{owner_rule}", variant)
        for own, (owner_name, owner_rule) in DECLARED_REFINEMENTS.items()
        for variant in (
            DECLARED_INVERSE_OVERLAP_VARIANTS[own]
            if inverse
            else DECLARED_OVERLAP_VARIANTS[own]
        )
    }
    actual_overlaps = {
        (item["own"], item["foreign"], item["foreign_variant"])
        for item in overlaps
    }
    undeclared_equalities = actual_equalities - expected_equalities
    missing_equalities = expected_equalities - actual_equalities
    undeclared_overlaps = actual_overlaps - expected_overlaps
    missing_overlaps = expected_overlaps - actual_overlaps
    if own_overlaps or undeclared_equalities or missing_equalities or undeclared_overlaps or missing_overlaps:
        raise RuntimeError(
            "collision contract mismatch: "
            f"own={own_overlaps}, "
            f"undeclared_equalities={sorted(undeclared_equalities)}, "
            f"missing_equalities={sorted(missing_equalities)}, "
            f"undeclared_overlaps={sorted(undeclared_overlaps)}, "
            f"missing_overlaps={sorted(missing_overlaps)}"
        )
    return {
        "foreign_helper_sha256": identities,
        "own_spans_checked": len(own),
        "foreign_active_spans_checked": foreign_active_spans,
        "own_span_overlaps": own_overlaps,
        "declared_exact_anchor_equalities": equalities,
        "declared_foreign_span_overlaps": overlaps,
        "declared_refinements": {
            label: {
                "foreign_helper": owner[0],
                "foreign_rule": owner[1],
                "exact_anchor_equality": label in DECLARED_EXACT_EQUALITIES,
                "overlap_variants": sorted(DECLARED_OVERLAP_VARIANTS[label]),
                "inverse_overlap_variants": sorted(DECLARED_INVERSE_OVERLAP_VARIANTS[label]),
            }
            for label, owner in DECLARED_REFINEMENTS.items()
        },
        "undeclared_exact_anchor_equalities": [],
        "undeclared_foreign_span_overlaps": [],
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
        audits.append(
            {
                "label": rule.label,
                "direction": "inverse" if inverse else "forward",
                "occurrences": count,
                "headers": [header.__dict__ for header in rule.headers],
                "rationale": rule.rationale,
                "precedent": rule.precedent,
                "declared_refinement": (
                    {
                        "foreign_helper": DECLARED_REFINEMENTS[rule.label][0],
                        "foreign_rule": DECLARED_REFINEMENTS[rule.label][1],
                    }
                    if rule.label in DECLARED_REFINEMENTS
                    else None
                ),
            }
        )
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
    if args.bootstrap_seal and not sentinels_unsealed():
        raise RuntimeError("bootstrap refused: output identity already sealed")
    if not args.bootstrap_seal and sentinels_unsealed():
        raise RuntimeError("output identity unsealed")
    source = args.input.read_bytes()
    source_shape = shape(source)
    check_shape(
        source_shape,
        output_expected() if inverse else input_expected(),
        unsealed=args.bootstrap_seal and inverse,
    )
    mapped = verify_authority(
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
    check_shape(
        result_shape,
        input_expected() if inverse else output_expected(),
        unsealed=args.bootstrap_seal and not inverse,
    )
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
        "authority": {
            "candidate_sha256": INPUT_SHA256,
            "candidate_git_blob": INPUT_GIT_BLOB,
            "log_sha256": LOG_SHA256,
            "error_headers_sha256": HEADERS_SHA256,
            "diagnostics_sha256": DIAGNOSTICS_SHA256,
            "errors": 217,
            "warnings": 350,
            "panic": 0,
            "exit": 1,
        },
        "scope": {
            "candidate_lines": [50000, 53999],
            "independent_direct_roots_only": True,
            "declared_active_probe11_refinements": len(DECLARED_REFINEMENTS),
            "undeclared_foreign_helper_span_overlap": False,
            "cascade_diagnostics_selected": False,
            "excluded": EXCLUDED,
        },
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
        "execution": {
            "lean": False,
            "lake": False,
            "git": False,
            "network": False,
            "remote": False,
            "repository_source_mutation": False,
        },
    }
    args.output.write_bytes(result)
    args.audit.write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(json.dumps(record, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
