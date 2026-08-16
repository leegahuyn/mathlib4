#!/usr/bin/env python3
"""Probe9 early2 projection over exact authoritative Probe8.

Only direct high-confidence roots in candidate lines 25,000--29,999 which are
not already repaired by Probe7 or any Probe8 tranche are included.  The helper
is static, exact-counted, reversible, and anchored to the terminal Probe8
artifact after a survivor rebase.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from dataclasses import dataclass
from pathlib import Path


SCHEMA = "qym-probe9-early2-static-transform-v2"
INPUT_SHA256 = "63baae8766e3208ac1d8dfa66946ac5ae3cf4a4264d21218a1ccb17aed3c4fd8"
INPUT_GIT_BLOB = "a2d3f4f60018fc2bfebd904db17aa13025c39ed6"
INPUT_BYTES = 2_916_737
INPUT_LF = 61_671
LOG_SHA256 = "4408bf46825d32a935de970904c711510b774ef93026fbee3e20dbc18392beea"
ERROR_HEADERS_SHA256 = "9f0d91787942db9470e307c5a44d8523b2b362ad31f737da0eb48b3f9f2d181f"

OUTPUT_SHA256 = "ee93d31d02b79f177d7ce7691f323df27baa1c09da873439089c6eac32d8b966"
OUTPUT_GIT_BLOB = "d5aa1649ae5691fb1019c06dfaa324c29598159e"
OUTPUT_BYTES = 2_916_744
OUTPUT_LF = 61_677


@dataclass(frozen=True)
class Header:
    line: int
    column: int
    message: str
    kind: str = "direct"


@dataclass(frozen=True)
class Rule:
    label: str
    old: str
    new: str
    headers: tuple[Header, ...]
    occurrences: int = 1
    rationale: str = ""


RULES: tuple[Rule, ...] = (
    Rule(
        "unit_eigenvector_ne_zero_use_local_norm_certificate",
        "theorem unitEigenvector_ne_zero\n"
        "    (T : E →L[𝕜] E) (μ : PointEigenvalue T) :\n"
        "    unitEigenvector T μ ≠ 0 := by\n"
        "  intro h\n"
        "  apply chosenEigenvector_ne_zero T μ\n"
        "  exact NormedSpace.normalize_eq_zero_iff.mp (by\n"
        "    simpa only [unitEigenvector] using h)\n",
        "theorem unitEigenvector_ne_zero\n"
        "    (T : E →L[𝕜] E) (μ : PointEigenvalue T) :\n"
        "    unitEigenvector T μ ≠ 0 := by\n"
        "  intro h\n"
        "  have hnorm := unitEigenvector_norm T μ\n"
        "  rw [h, norm_zero] at hnorm\n"
        "  norm_num at hnorm\n",
        (
            Header(
                25161,
                8,
                "Unknown constant `NormedSpace.normalize_eq_zero_iff.mp`",
            ),
        ),
        rationale="Contradict the already-proved unit norm after h rewrites the vector to zero; this avoids the unavailable normalize_eq_zero_iff projection entirely.",
    ),
    Rule(
        "quotient_map_measurable_supply_orbit_setoid",
        "  change Measurable\n"
        "    (Quotient.mk' : H → Quotient (MulAction.orbitRel Gamma2 H))\n"
        "  exact measurable_quotient_mk'\n",
        "  change Measurable\n"
        "    (@Quotient.mk' H (MulAction.orbitRel Gamma2 H))\n"
        "  exact measurable_quotient_mk'\n",
        (
            Header(
                29115,
                5,
                "failed to synthesize instance of type class",
            ),
        ),
        rationale="Supply the orbit Setoid explicitly instead of asking typeclass synthesis to infer it from a result annotation.",
    ),
    Rule(
        "quotient_map_surjective_supply_orbit_setoid",
        "  change Function.Surjective\n"
        "    (Quotient.mk' : H → Quotient (MulAction.orbitRel Gamma2 H))\n"
        "  exact Quotient.mk'_surjective\n",
        "  change Function.Surjective\n"
        "    (@Quotient.mk' H (MulAction.orbitRel Gamma2 H))\n"
        "  exact Quotient.mk'_surjective\n",
        (
            Header(
                29125,
                5,
                "failed to synthesize instance of type class",
            ),
        ),
        rationale="Use the same explicit orbit Setoid for the quotient-map surjectivity theorem.",
    ),
    Rule(
        "quotient_pullback_ae_unfold_function_comp",
        "  simpa only [Function.comp_apply] using\n"
        "    (MeasureTheory.Lp.coeFn_compMeasurePreserving F\n"
        "      (quotientMap_measurePreserving Y))\n",
        "  simpa only [Function.comp_def] using\n"
        "    (MeasureTheory.Lp.coeFn_compMeasurePreserving F\n"
        "      (quotientMap_measurePreserving Y))\n",
        (Header(29237, 2, "Type mismatch: After simplification"),),
        rationale="The theorem contains a naked function composition; unfold comp rather than only its pointwise apply lemma.",
    ),
    Rule(
        "descend_memlp_unfold_function_comp",
        "  simpa only [truncatedQuotientMeasure, Function.comp_apply,\n"
        "    descendInvariant_quotientMap] using hMap\n",
        "  simpa only [truncatedQuotientMeasure, Function.comp_def,\n"
        "    descendInvariant_quotientMap] using hMap\n",
        (Header(29306, 2, "Type mismatch: After simplification"),),
        rationale="Beta-expose the composed descent before applying its quotientMap simp theorem.",
    ),
    Rule(
        "eta_trivialized_memlp_supply_bound_constant",
        "  refine MemLp.of_le_mul f.property.2.2\n"
        "    (etaTrivializedScalar_continuous Y f).aestronglyMeasurable ?_\n",
        "  refine MemLp.of_le_mul (c := C) f.property.2.2\n"
        "    (etaTrivializedScalar_continuous Y f).aestronglyMeasurable ?_\n",
        (
            Header(29363, 9, "don't know how to synthesize implicit argument `c`"),
            Header(29351, 40, "unsolved goals", "cascade"),
        ),
        rationale="The compactness argument has already named the real bound C; pass it to the current MemLp.of_le_mul API.",
    ),
    Rule(
        "matched_orthogonal_pair_normalize_coordinates",
        "  · intro hx y hy\n"
        "    simp [InMatchedOrthogonal, InMatchedNullSpace, modelPair, hx, hy]\n",
        "  · intro hx y hy\n"
        "    change x.1 = 0 at hx\n"
        "    change y.2 = 0 at hy\n"
        "    simp [modelPair, hx, hy]\n",
        (Header(29837, 2, "unsolved goals"),),
        rationale="Normalize both coordinate predicates before simplifying the bilinear pairing.",
    ),
    Rule(
        "ground_eigenvector_normalize_null_coordinate",
        "    {x : Vec2} (hx : InMatchedNullSpace x) :\n"
        "    modelHamiltonian x = modelGroundLevel • x := by\n"
        "  ext <;>\n",
        "    {x : Vec2} (hx : InMatchedNullSpace x) :\n"
        "    modelHamiltonian x = modelGroundLevel • x := by\n"
        "  change x.2 = 0 at hx\n"
        "  ext <;>\n",
        (Header(29883, 49, "unsolved goals"),),
        rationale="Expose the stored null-space predicate as x.2 = 0 before coordinatewise simplification.",
    ),
    Rule(
        "ground_eigenspace_eliminate_numeric_disjunct",
        "  · intro hx\n"
        "    have hsnd := congrArg Prod.snd hx\n"
        "    simp [modelHamiltonian, modelGroundLevel, modelOffGroundLevel,\n"
        "      InMatchedNullSpace] at hsnd ⊢\n"
        "    linarith\n",
        "  · intro hx\n"
        "    have hsnd := congrArg Prod.snd hx\n"
        "    simp [modelHamiltonian, modelGroundLevel, modelOffGroundLevel] at hsnd\n"
        "    norm_num at hsnd\n"
        "    change x.2 = 0\n"
        "    exact hsnd\n",
        (Header(29898, 4, "linarith failed to find a contradiction"),),
        rationale="The second-coordinate equation is a disjunction; norm_num rejects 201/2 = 100 and leaves x.2 = 0.",
    ),
    Rule(
        "offground_eigenvector_normalize_orthogonal_coordinate",
        "    {x : Vec2} (hx : InMatchedOrthogonal x) :\n"
        "    modelHamiltonian x = modelOffGroundLevel • x := by\n"
        "  ext <;>\n",
        "    {x : Vec2} (hx : InMatchedOrthogonal x) :\n"
        "    modelHamiltonian x = modelOffGroundLevel • x := by\n"
        "  change x.1 = 0 at hx\n"
        "  ext <;>\n",
        (Header(29903, 52, "unsolved goals"),),
        rationale="Expose the orthogonal-space predicate as x.1 = 0 before simplifying the diagonal operator.",
    ),
    Rule(
        "mass_coercive_normalize_orthogonal_coordinate",
        "    {x : Vec2} (hx : InMatchedOrthogonal x) :\n"
        "    modelC * modelNormSq x ≤ modelMassForm x := by\n"
        "  simp [modelC, modelNormSq, modelMassForm, InMatchedOrthogonal, hx]\n",
        "    {x : Vec2} (hx : InMatchedOrthogonal x) :\n"
        "    modelC * modelNormSq x ≤ modelMassForm x := by\n"
        "  change x.1 = 0 at hx\n"
        "  simp [modelC, modelNormSq, modelMassForm, hx]\n",
        (Header(29940, 48, "unsolved goals"),),
        rationale="Normalize the complement hypothesis before the coercivity expression is simplified.",
    ),
)


RETAINED_FAILED_PROBE8_ROOT_LINES = (25161,)
DELIBERATE_UNHANDLED_FAILED_PROBE8_LINES = (25170, 25203, 28359, 28373)
DELIBERATE_UNHANDLED_LINES = (
    29468, 29469, 29471, 29473, 29506, 29515, 29516,
    29518, 29519, 29554, 29659,
)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git_blob(data: bytes) -> str:
    return hashlib.sha1(
        b"blob " + str(len(data)).encode("ascii") + b"\0" + data
    ).hexdigest()


def shape(data: bytes) -> dict[str, object]:
    data.decode("utf-8")
    return {
        "sha256": sha256(data),
        "git_blob": git_blob(data),
        "bytes": len(data),
        "lf": data.count(b"\n"),
        "cr": b"\r" in data,
        "nul": b"\0" in data,
        "bom": data.startswith(b"\xef\xbb\xbf"),
        "terminal_lf": data.endswith(b"\n"),
    }


def trust(text: str) -> dict[str, int]:
    return {
        "sorry": len(re.findall(r"\bsorry\b", text)),
        "admit": len(re.findall(r"\badmit\b", text)),
        "native_decide": len(re.findall(r"\bnative_decide\b", text)),
        "Lean.ofReduceBool": text.count("Lean.ofReduceBool"),
        "axiom_declaration": len(re.findall(r"(?m)^\s*axiom\s+", text)),
        "unsafe_declaration": len(re.findall(r"(?m)^\s*unsafe\s+", text)),
        "maxHeartbeats_zero": len(
            re.findall(r"set_option\s+maxHeartbeats\s+0\b", text)
        ),
    }


def expected(inverse: bool, result: bool) -> tuple[str, str, int, int]:
    source = (INPUT_SHA256, INPUT_GIT_BLOB, INPUT_BYTES, INPUT_LF)
    output = (OUTPUT_SHA256, OUTPUT_GIT_BLOB, OUTPUT_BYTES, OUTPUT_LF)
    if inverse:
        source, output = output, source
    return output if result else source


def check_shape(
    actual: dict[str, object],
    wanted: tuple[str, str, int, int],
    *,
    allow_unsealed: bool = False,
) -> None:
    if wanted[0] != "__TO_SEAL__" or not allow_unsealed:
        for key, value in zip(("sha256", "git_blob", "bytes", "lf"), wanted, strict=True):
            if actual[key] != value:
                raise RuntimeError(f"{key}: {actual[key]} != {value}")
    if actual["cr"] or actual["nul"] or actual["bom"] or not actual["terminal_lf"]:
        raise RuntimeError(f"text hygiene failure: {actual}")


def verify_authority(log: bytes, error_headers: bytes) -> list[dict[str, object]]:
    if sha256(log) != LOG_SHA256:
        raise RuntimeError(f"Probe8 log sha256 {sha256(log)} != {LOG_SHA256}")
    if sha256(error_headers) != ERROR_HEADERS_SHA256:
        raise RuntimeError(
            f"Probe8 error headers sha256 {sha256(error_headers)} != {ERROR_HEADERS_SHA256}"
        )
    log_text = log.decode("utf-8")
    header_lines = error_headers.decode("utf-8").splitlines()
    extracted = [
        line
        for line in log_text.splitlines()
        if re.match(
            r"^PrimalitySheafVerification/QYM\.lean:\d+:\d+: error(?:\([^)]*\))?: ",
            line,
        )
    ]
    if extracted != header_lines or len(header_lines) != 344:
        raise RuntimeError("Probe8 coded/uncoded error-header artifact mismatch")
    verified: list[dict[str, object]] = []
    for rule in RULES:
        for header in rule.headers:
            pattern = re.compile(
                rf"PrimalitySheafVerification/QYM\.lean:{header.line}:{header.column}: "
                rf"error(?:\([^\n)]*\))?: {re.escape(header.message)}"
            )
            count = len(pattern.findall(log_text))
            if count != 1:
                raise RuntimeError(
                    f"{rule.label}: header {header.line}:{header.column} count {count}, expected 1"
                )
            verified.append(
                {
                    "rule": rule.label,
                    "kind": header.kind,
                    "line": header.line,
                    "column": header.column,
                    "message": header.message,
                    "count": count,
                }
            )
    return verified


def transform(text: str, inverse: bool) -> tuple[str, list[dict[str, object]]]:
    rules = tuple(reversed(RULES)) if inverse else RULES
    audit: list[dict[str, object]] = []
    for rule in rules:
        old, new = (rule.new, rule.old) if inverse else (rule.old, rule.new)
        count = text.count(old)
        if count != rule.occurrences:
            raise RuntimeError(
                f"{rule.label}: exact count {count}, expected {rule.occurrences}"
            )
        text = text.replace(old, new)
        audit.append(
            {
                "label": rule.label,
                "direction": "inverse" if inverse else "forward",
                "occurrences": count,
                "headers": [h.__dict__ for h in rule.headers],
                "rationale": rule.rationale,
            }
        )
    return text, audit


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--probe8-log", type=Path, required=True)
    parser.add_argument("--probe8-error-headers", type=Path, required=True)
    parser.add_argument("--audit", type=Path, required=True)
    parser.add_argument("--mode", choices=("forward", "inverse"), default="forward")
    parser.add_argument("--bootstrap-seal", action="store_true")
    args = parser.parse_args()
    inverse = args.mode == "inverse"

    source = args.input.read_bytes()
    source_shape = shape(source)
    check_shape(
        source_shape,
        expected(inverse, False),
        allow_unsealed=args.bootstrap_seal and inverse,
    )
    verified = verify_authority(
        args.probe8_log.read_bytes(), args.probe8_error_headers.read_bytes()
    )
    source_text = source.decode("utf-8")
    before_trust = trust(source_text)
    result_text, rule_audit = transform(source_text, inverse)
    result = result_text.encode("utf-8")
    result_shape = shape(result)
    check_shape(
        result_shape,
        expected(inverse, True),
        allow_unsealed=args.bootstrap_seal and not inverse,
    )
    after_trust = trust(result_text)
    if before_trust != after_trust or any(after_trust.values()):
        raise RuntimeError(f"trust inventory changed or nonzero: {before_trust} -> {after_trust}")
    restored, _ = transform(result_text, not inverse)
    if restored.encode("utf-8") != source:
        raise RuntimeError("opposite transform did not restore source byte-for-byte")
    if args.output.exists() or args.audit.exists():
        raise RuntimeError("refusing to overwrite output or audit")

    record = {
        "schema": SCHEMA,
        "status": "STATIC_PASS_EXACT_PROBE8_REANCHORED_NOT_LEAN_EXECUTED",
        "activation": True,
        "activation_blocker": None,
        "promotion": False,
        "mode": args.mode,
        "authority": {
            "probe8_run": 31969310662,
            "probe8_github_sha": "a973fa165427d73a143d30cbe58a06405d88996c",
            "probe8_candidate_sha256": INPUT_SHA256,
            "probe8_candidate_git_blob": INPUT_GIT_BLOB,
            "probe8_log_sha256": LOG_SHA256,
            "probe8_error_headers_sha256": ERROR_HEADERS_SHA256,
            "probe8_error_headers": 344,
            "probe8_warning_headers": 374,
            "probe8_exit": 1,
            "probe8_panic": 0,
        },
        "source": source_shape,
        "result": result_shape,
        "scope": {"candidate_line_min": 25000, "candidate_line_max": 29999},
        "repair_families": len(RULES),
        "active_occurrences": sum(x["occurrences"] for x in rule_audit),
        "direct_headers_verified": sum(x["kind"] == "direct" for x in verified),
        "cascade_headers_verified": sum(x["kind"] == "cascade" for x in verified),
        "selected_exact_probe8_lines": sorted(
            {h.line for rule in RULES for h in rule.headers}
        ),
        "retained_failed_probe8_root_lines": list(RETAINED_FAILED_PROBE8_ROOT_LINES),
        "deliberate_unhandled_failed_probe8_lines": list(
            DELIBERATE_UNHANDLED_FAILED_PROBE8_LINES
        ),
        "deliberate_unhandled_lines": list(DELIBERATE_UNHANDLED_LINES),
        "rules": rule_audit,
        "inverse_byte_equal": True,
        "trust": after_trust,
        "execution": {
            "lean": False,
            "lake": False,
            "git_mutation": False,
            "network": False,
            "remote": False,
            "canonical_source_mutation": False,
        },
    }
    args.output.write_bytes(result)
    args.audit.write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(record, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
