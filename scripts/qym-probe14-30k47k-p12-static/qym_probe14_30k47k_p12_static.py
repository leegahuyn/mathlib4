#!/usr/bin/env python3
"""Probe14 static-only repairs for exact terminal Probe12 QYM lines 30k-47k.

This helper is deliberately activation-disabled and must be reanchored after a
terminal Probe13 artifact exists.  It applies only eight direct, unowned,
high-confidence repairs to the exact Probe12 candidate.  It never invokes
Lean, Lake, Git, a workflow, the network, or a remote service.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import re
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from types import ModuleType


sys.dont_write_bytecode = True

SCHEMA = "qym-probe14-30k47k-p12-static-v1-exact-terminal-probe12"
INPUT_SHA256 = "4a123f69912bd7ce2ab070433f8cad0ecc284652a9cbab634def1936e9037212"
INPUT_GIT_BLOB = "76dd931638b9a6ad50ee764c65cd14489e8be310"
INPUT_BYTES = 2_936_558
INPUT_LF = 62_068
LOG_SHA256 = "62ce7c1b4ec23a23d690c64d49e45901faec66ff751d86e314e669b8c876c398"
HEADERS_SHA256 = "0cebf8d7bbcb923165a13f68f2afbbef1843bb26d77e072252c570b8e77b0dd9"
DIAGNOSTICS_SHA256 = "16b69f25e53f28d028cbefca21d5401e25dbfaa2847bdfdc8f7532034690ca23"

# Filled only after a deterministic bootstrap projection is independently
# inspected.  Bootstrap mode is still activation=false and promotion=false.
OUTPUT_SHA256 = "d5ca1062ed58f797ac546219147cf14a6086990c110ed0f376392c2aa4c46cc0"
OUTPUT_GIT_BLOB = "025c8a32dd7792947cbae2b52519ded7769ade4c"
OUTPUT_BYTES = 2_936_695
OUTPUT_LF = 62_072


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
        "stabilizer_map_eq_bot_supply_subgroup_argument",
        "  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj]\n"
        "  exact Subgroup.map_eq_bot_iff_of_injective\n"
        "    (MulAut.conj g).injective\n",
        "  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj]\n"
        "  exact Subgroup.map_eq_bot_iff_of_injective\n"
        "    (MulAction.stabilizer EffectiveGroup z)\n"
        "    (MulAut.conj g).injective\n",
        (Header(37536, 4, "Application type mismatch: The argument"),),
        "Supply the explicit subgroup consumed by the current map_eq_bot API before its injectivity proof.",
        "The exact diagnostic says the injectivity proposition was parsed where the first explicit Subgroup argument is required.",
    ),
    Rule(
        "twisted_difference_add_expose_pointwise_pi_add",
        "  · simp only [widthTwoTwistedDifferenceQuotient, hp, if_false,\n"
        "      Pi.add_apply, widthTwoTwistedIncrement_add]\n"
        "    ring_nf\n",
        "  · simp only [widthTwoTwistedDifferenceQuotient, hp, if_false,\n"
        "      Pi.add_apply]\n"
        "    have hfg : f + g = fun t => f t + g t := rfl\n"
        "    rw [hfg, widthTwoTwistedIncrement_add]\n"
        "    ring\n",
        (Header(40673, 2, "unsolved goals"),),
        "Expose Pi addition as the pointwise lambda expected by the already-proved twisted-increment add theorem.",
        "The exact residual differs from widthTwoTwistedIncrement_add only by opaque Pi addition, after which it is a commutative-field identity.",
    ),
    Rule(
        "twisted_difference_smul_expose_pointwise_pi_smul",
        "  · simp only [widthTwoTwistedDifferenceQuotient, hp, if_false,\n"
        "      Pi.smul_apply, smul_eq_mul, widthTwoTwistedIncrement_smul]\n"
        "    ring_nf\n",
        "  · simp only [widthTwoTwistedDifferenceQuotient, hp, if_false,\n"
        "      Pi.smul_apply, smul_eq_mul]\n"
        "    have hcf : c • f = fun t => c * f t := rfl\n"
        "    rw [hcf, widthTwoTwistedIncrement_smul]\n"
        "    ring\n",
        (Header(40684, 2, "unsolved goals"),),
        "Expose Pi scalar multiplication as the pointwise lambda expected by the twisted-increment scalar theorem.",
        "The exact residual is the scalar version of the adjacent addition residual and becomes a ring identity after the existing producer rewrite.",
    ),
    Rule(
        "eta_continuity_compose_full_composite_with_comp_prime",
        "      (ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet\n"
        "        (actualFixedPhaseCuspHorocyclePoint kappa Y x).2).continuousAt.comp\n"
        "          hcoe.continuousAt\n",
        "      (ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet\n"
        "        (actualFixedPhaseCuspHorocyclePoint kappa Y x).2).continuousAt.comp'\n"
        "          hcoe.continuousAt\n",
        (Header(41321, 10, "Application type mismatch: The argument"),),
        "Use ContinuousAt.comp' because hcoe already certifies the full horocycle-to-complex composite.",
        "The exit-zero Mock2 FunctionalAnalysis producer continuous_eta_upperHalfPlane uses this exact eta theorem followed by continuousAt.comp'.",
    ),
    Rule(
        "right_normal_real_part_close_trivial_side_goal",
        "  simp [Complex.mul_re] <;> ring_nf\n",
        "  simp [Complex.mul_re] <;> ring_nf <;> simp\n",
        (Header(44541, 51, "unsolved goals"),),
        "Close the sole residual disjunction whose right branch is True after the existing algebra normalization.",
        "The exact residual is `(y = 0 ∨ w = 0) ∨ True`; a final simp closes it without changing the theorem statement or algebraic producer.",
    ),
    Rule(
        "selected_cusp_circle_pin_add_circle_quotient_map",
        "  have hfun : selectedCuspCircle q Y ∘ Quotient.mk' =\n"
        "      QYM.FullCertification.P2ConnectedCuspComponentsExtension.selectedCuspQuotientLoop q Y := by\n",
        "  have hfun : selectedCuspCircle q Y ∘\n"
        "      QuotientAddGroup.mk' (AddSubgroup.zmultiples (2 : ℝ)) =\n"
        "      QYM.FullCertification.P2ConnectedCuspComponentsExtension.selectedCuspQuotientLoop q Y := by\n",
        (Header(45032, 39, "failed to synthesize instance of type class", "lean.synthInstanceFailed"),),
        "Pin the quotient map defining AddCircle 2 instead of asking typeclass search to invent an unconstrained Setoid Real.",
        "The adjacent cylinder quotient producer uses the identical QuotientAddGroup.mk' (AddSubgroup.zmultiples (2 : Real)) map.",
    ),
    Rule(
        "smooth_transition_residual_use_explicit_proposition_variable",
        "variable [hSmooth : SmoothTransitionResidual]\n",
        "variable (hSmooth : SmoothTransitionResidual)\n",
        (
            Header(45310, 20, "invalid binder annotation, type is not a class instance"),
            Header(45318, 32, "Unknown identifier `hSmooth`", "lean.unknownIdentifier"),
        ),
        "Bind the residual proposition as an ordinary section variable; it is not a class and remains available to the local HasGroupoid instance.",
        "The preceding allCoveringSheets_hasGroupoid theorem already consumes SmoothTransitionResidual as an ordinary explicit proposition argument.",
    ),
    Rule(
        "negative_horocycle_derivative_normalize_comp_and_neg_smul",
        "  have h := (selectedHorocycleCoordinate_hasDerivAt q Y (-t)).scomp t\n"
        "    (hasDerivAt_neg t)\n"
        "  change HasDerivAt\n"
        "    (fun s => selectedHorocycleCoordinate q Y (-s))\n"
        "    (-explicitSelectedHorocycleVelocity q Y (-t)) t at h\n"
        "  simpa only [selectedHorocycleBoundaryVelocity] using h\n",
        "  have h := (selectedHorocycleCoordinate_hasDerivAt q Y (-t)).scomp t\n"
        "    (hasDerivAt_neg t)\n"
        "  simpa only [Function.comp_apply, selectedHorocycleBoundaryVelocity,\n"
        "    neg_smul, one_smul] using h\n",
        (Header(47219, 2, "'change' tactic failed, pattern"),),
        "Normalize the actual scomp result rather than requiring a false definitional equality between composition and lambda forms.",
        "The exact diagnostic prints composition with (-1) scalar multiplication; Function.comp_apply plus neg_smul and one_smul yields the stated boundary velocity.",
    ),
)


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
)


def sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def git_blob(raw: bytes) -> str:
    return hashlib.sha1(f"blob {len(raw)}\0".encode("ascii") + raw).hexdigest()


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


def load_exact_module(label: str, path: Path, expected_sha: str) -> ModuleType:
    raw = path.read_bytes()
    if sha256(raw) != expected_sha:
        raise RuntimeError(f"active helper identity mismatch: {label}")
    module_name = "_qym_probe14_active_" + label
    spec = importlib.util.spec_from_file_location(module_name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot import active helper: {label}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[module_name] = module
    spec.loader.exec_module(module)
    return module


def locate(text: str, needle: str) -> tuple[int, int, int, int]:
    pos = text.find(needle)
    if pos < 0 or text.find(needle, pos + 1) >= 0:
        raise RuntimeError("anchor is not uniquely located")
    start_line = text.count("\n", 0, pos) + 1
    end_line = start_line + needle.count("\n")
    return pos, pos + len(needle), start_line, end_line


def verify_authority(log_raw: bytes, headers_raw: bytes, diagnostics_raw: bytes) -> list[dict[str, object]]:
    expected = (
        ("log", sha256(log_raw), LOG_SHA256),
        ("headers", sha256(headers_raw), HEADERS_SHA256),
        ("diagnostics", sha256(diagnostics_raw), DIAGNOSTICS_SHA256),
    )
    for label, actual, wanted in expected:
        if actual != wanted:
            raise RuntimeError(f"Probe12 {label} identity mismatch: {actual}")
    header_lines = headers_raw.decode("utf-8", errors="strict").splitlines()
    rows = [json.loads(line) for line in diagnostics_raw.decode("utf-8", errors="strict").splitlines()]
    errors = [row for row in rows if row.get("severity") == "error"]
    warnings = [row for row in rows if row.get("severity") == "warning"]
    if len(header_lines) != 183 or len(errors) != 183 or len(warnings) != 350:
        raise RuntimeError("terminal Probe12 diagnostic counts drifted")
    mapped: list[dict[str, object]] = []
    for rule in RULES:
        for header in rule.headers:
            matches = [
                row for row in errors
                if row.get("line") == header.line
                and row.get("column") == header.column
                and row.get("message") == header.message
                and row.get("code") == header.code
            ]
            if len(matches) != 1:
                raise RuntimeError(f"{rule.label}: exact diagnostic mismatch at {header.line}:{header.column}")
            header_pattern = re.compile(
                rf"^PrimalitySheafVerification/QYM\.lean:{header.line}:{header.column}: error"
            )
            if sum(bool(header_pattern.match(line)) for line in header_lines) != 1:
                raise RuntimeError(f"{rule.label}: exact header mismatch at {header.line}:{header.column}")
            mapped.append({"rule": rule.label, **asdict(header)})
    return mapped


def collision_audit(source_text: str) -> dict[str, object]:
    own_ranges: list[tuple[int, int, str]] = []
    for rule in RULES:
        if source_text.count(rule.old) != rule.occurrences or source_text.count(rule.new) != 0:
            raise RuntimeError(f"{rule.label}: Probe12 anchor activation mismatch")
        start, end, start_line, end_line = locate(source_text, rule.old)
        if not (30_000 <= start_line <= 47_999 and end_line <= 48_050):
            raise RuntimeError(f"{rule.label}: source scope violation {start_line}-{end_line}")
        own_ranges.append((start, end, rule.label))
    for i, (a0, a1, alabel) in enumerate(own_ranges):
        for b0, b1, blabel in own_ranges[i + 1:]:
            if max(a0, b0) < min(a1, b1):
                raise RuntimeError(f"own source-span collision: {alabel}/{blabel}")
    for i, left in enumerate(RULES):
        for right in RULES[i + 1:]:
            for lv in (left.old, left.new):
                for rv in (right.old, right.new):
                    if lv == rv or lv in rv or rv in lv:
                        raise RuntimeError(f"own textual collision: {left.label}/{right.label}")

    root = Path(__file__).resolve().parent.parent
    helper_identities: dict[str, str] = {}
    foreign_families = 0
    foreign_variants_checked = 0
    foreign_active_spans_found = 0
    textual_collisions: list[dict[str, object]] = []
    span_collisions: list[dict[str, object]] = []
    for helper_label, relative, expected_sha in ACTIVE_HELPERS:
        module = load_exact_module(helper_label, root / relative, expected_sha)
        helper_identities[helper_label] = expected_sha
        foreign_rules = tuple(getattr(module, "RULES", ()))
        foreign_families += len(foreign_rules)
        for foreign in foreign_rules:
            for variant_name, variant in (("old", foreign.old), ("new", foreign.new)):
                foreign_variants_checked += 1
                for own in RULES:
                    for own_variant_name, own_variant in (("old", own.old), ("new", own.new)):
                        if own_variant == variant or own_variant in variant or variant in own_variant:
                            textual_collisions.append({
                                "own": own.label,
                                "own_variant": own_variant_name,
                                "foreign": f"{helper_label}:{foreign.label}",
                                "foreign_variant": variant_name,
                            })
                offset = 0
                while True:
                    pos = source_text.find(variant, offset)
                    if pos < 0:
                        break
                    foreign_active_spans_found += 1
                    vend = pos + len(variant)
                    for own_start, own_end, own_label in own_ranges:
                        if max(pos, own_start) < min(vend, own_end):
                            span_collisions.append({
                                "own": own_label,
                                "foreign": f"{helper_label}:{foreign.label}",
                                "foreign_variant": variant_name,
                            })
                    offset = pos + 1
    if textual_collisions or span_collisions:
        raise RuntimeError("collision with active Probe12 repair inventory")
    return {
        "status": "PASS",
        "own_families": len(RULES),
        "own_occurrences": sum(rule.occurrences for rule in RULES),
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
            raise RuntimeError(f"{rule.label}: exact anchor count {count}, expected {rule.occurrences}")
        text = text.replace(src, dst)
        audits.append({
            "label": rule.label,
            "direction": "inverse" if inverse else "forward",
            "occurrences": count,
            "headers": [asdict(header) for header in rule.headers],
            "rationale": rule.rationale,
            "precedent": rule.precedent,
        })
    return text, audits


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--probe12-log", type=Path, required=True)
    parser.add_argument("--probe12-headers", type=Path, required=True)
    parser.add_argument("--probe12-diagnostics", type=Path, required=True)
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
        if source["git_blob"] != INPUT_GIT_BLOB or source["bytes"] != INPUT_BYTES or source["lf"] != INPUT_LF:
            raise RuntimeError("Probe12 source shape mismatch")
    elif (
        source["git_blob"] != OUTPUT_GIT_BLOB
        or source["bytes"] != OUTPUT_BYTES
        or source["lf"] != OUTPUT_LF
    ):
        raise RuntimeError("sealed Probe14 source shape mismatch")

    mapped = verify_authority(
        args.probe12_log.read_bytes(),
        args.probe12_headers.read_bytes(),
        args.probe12_diagnostics.read_bytes(),
    )
    source_text = source_raw.decode("utf-8", errors="strict")
    collisions = collision_audit(source_text) if not args.inverse else {"status": "NOT_REPEATED_ON_INVERSE"}
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
        raise RuntimeError("inverse did not restore exact Probe12 source shape")

    trust_counts = trust(result_text)
    if any(trust_counts.values()):
        raise RuntimeError(f"trust-token audit failed: {trust_counts}")
    args.output.write_bytes(result_raw)
    audit = {
        "schema": SCHEMA,
        "status": "STATIC_PASS_BOOTSTRAP_NOT_LEAN_EXECUTED" if args.bootstrap else "STATIC_PASS_SEALED_NOT_LEAN_EXECUTED",
        "activation": False,
        "promotion": False,
        "must_reanchor_after_terminal_probe13": True,
        "mode": "inverse" if args.inverse else "forward",
        "authority": {
            "candidate_sha256": INPUT_SHA256,
            "candidate_git_blob": INPUT_GIT_BLOB,
            "log_sha256": LOG_SHA256,
            "headers_sha256": HEADERS_SHA256,
            "diagnostics_sha256": DIAGNOSTICS_SHA256,
            "errors": 183,
            "warnings": 350,
        },
        "source": source,
        "result": result,
        "repair_families": len(RULES),
        "repair_occurrences": sum(rule.occurrences for rule in RULES),
        "diagnostic_ownership_records": len(mapped),
        "selected_exact_probe12_lines": sorted({header.line for rule in RULES for header in rule.headers}),
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
    args.audit.write_text(json.dumps(audit, indent=2, ensure_ascii=False) + "\n", encoding="utf-8", newline="\n")


if __name__ == "__main__":
    main()
