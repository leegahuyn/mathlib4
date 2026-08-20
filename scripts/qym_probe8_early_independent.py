#!/usr/bin/env python3
"""Exact early-root Probe8 projection over authoritative Probe7 bytes.

Local static transformer only: no Lean/Lake/Git/network, no source writes, no
promotion.  All anchors occur exactly once, all 12 compiler headers are locked,
and the inverse must restore the input byte-for-byte.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from dataclasses import dataclass
from pathlib import Path


SCHEMA = "qym-probe8-early-independent-transform-v1"
INPUT_SHA256 = "342eb7aab3d5e71fc242706188abdb7cb1804cd04c79ed254e1715fe0876f3eb"
INPUT_GIT_BLOB = "9b53049115afcc674fac88f998b6716abddb0162"
INPUT_BYTES = 2_913_545
INPUT_LF = 61_593
LOG_SHA256 = "c31e12c9b5a47358a5128295f9c05d90783e9c5af79f63576c22f2e0a30120ee"

# Sealed after deterministic bootstrap projection, then enforced both ways.
OUTPUT_SHA256 = "f3e39898781be3d2199cb297b5bc3fabcc782ae1adc0e971f3360f4aa3a9f4ca"
OUTPUT_GIT_BLOB = "eba3347f64ddd7edd5868640425eb1dc2cd929ef"
OUTPUT_BYTES = 2_914_059
OUTPUT_LF = 61_601


@dataclass(frozen=True)
class Header:
    line: int
    column: int
    message: str


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
        "unit_eigenvector_ne_zero_direct_normalize_iff",
        "  rw [unitEigenvector, NormedSpace.normalize_eq_zero_iff]\n"
        "  exact chosenEigenvector_ne_zero T μ\n",
        "  intro h\n"
        "  apply chosenEigenvector_ne_zero T μ\n"
        "  exact NormedSpace.normalize_eq_zero_iff.mp (by\n"
        "    simpa only [unitEigenvector] using h)\n",
        (Header(25159, 23, "Tactic `rewrite` failed"),),
        "Eliminate Ne explicitly, then use normalize_eq_zero_iff on the equality hypothesis.",
    ),
    Rule(
        "unit_eigenvector_explicit_real_smul_change",
        "  rw [unitEigenvector, NormedSpace.normalize, RCLike.real_smul_eq_coe_smul]\n",
        "  change (‖chosenEigenvector T μ‖⁻¹ : ℝ) • chosenEigenvector T μ =\n"
        "    ((‖chosenEigenvector T μ‖⁻¹ : ℝ) : 𝕜) • chosenEigenvector T μ\n"
        "  exact RCLike.real_smul_eq_coe_smul (K := 𝕜)\n"
        "    (‖chosenEigenvector T μ‖⁻¹ : ℝ) (chosenEigenvector T μ)\n",
        (Header(25166, 46, "typeclass instance problem is stuck"),),
        "Pin the real scalar and vector before invoking the scalar-restriction equality.",
    ),
    Rule(
        "unit_eigenvector_apply_congr_under_smul",
        "      rw [(chosenEigenvector_hasEigenvector T μ).apply_eq_smul]\n",
        "      exact congrArg (fun y : E => a • y)\n"
        "        (chosenEigenvector_hasEigenvector T μ).apply_eq_smul\n",
        (Header(25179, 10, "Tactic `rewrite` failed"),),
        "Transport the eigenvector equation under the outer scalar action explicitly.",
    ),
    Rule(
        "orthogonal_family_supply_second_vector",
        "  exact hsymm.orthogonalFamily_eigenspaces.pairwise hμν\n"
        "    (unitEigenvector_hasEigenvector T μ).1\n"
        "    (unitEigenvector_hasEigenvector T ν).1\n",
        "  exact hsymm.orthogonalFamily_eigenspaces.pairwise hμν\n"
        "    (unitEigenvector_hasEigenvector T μ).1\n"
        "    (unitEigenvector T ν) (unitEigenvector_hasEigenvector T ν).1\n",
        (Header(25199, 4, "Application type mismatch"),),
        "Probe6 showed the first vector is inferred; Probe7 showed the second vector remains explicit.",
    ),
    Rule(
        "resolvent_zero_eigenvalue_expose_eigenspace_abbrev",
        "  simpa only [hν] using\n"
        "    QYM.UnboundedCompactSpectralMappingExtension.inverse_zero_eigenspace_eq_bot ρ\n",
        "  change eigenspace (ρ.inverse : Module.End 𝕜 H) (ν : 𝕜) = ⊥\n"
        "  rw [hν]\n"
        "  exact QYM.UnboundedCompactSpectralMappingExtension.inverse_zero_eigenspace_eq_bot ρ\n",
        (Header(26430, 2, "Type mismatch: After simplification"),),
        "Expose the definitionally equal eigenspace abbreviation before rewriting ν to zero.",
    ),
    Rule(
        "eta_trivialization_section_mul_div_cancel",
        "  simp only [etaTrivializationLinear, etaSectionLinear, etaTrivialization,\n"
        "    etaSection]\n"
        "  field_simp [EtaHalfWeight.etaValue_ne_zero]\n"
        "  <;> ring\n",
        "  change EtaHalfWeight.etaValue τ *\n"
        "    (g.1 τ / EtaHalfWeight.etaValue τ) = g.1 τ\n"
        "  exact mul_div_cancel₀ _ (EtaHalfWeight.etaValue_ne_zero τ)\n",
        (Header(28286, 2, "`field_simp` made no progress"),),
        "Use the exact nonzero denominator cancellation theorem on the exposed scalar goal.",
    ),
    Rule(
        "eta_section_trivialization_mul_div_cancel_left",
        "  simp only [etaSectionLinear, etaTrivializationLinear, etaSection,\n"
        "    etaTrivialization]\n"
        "  field_simp [EtaHalfWeight.etaValue_ne_zero]\n"
        "  <;> ring\n",
        "  change (EtaHalfWeight.etaValue τ * f.1 τ) /\n"
        "    EtaHalfWeight.etaValue τ = f.1 τ\n"
        "  exact mul_div_cancel_left₀ _ (EtaHalfWeight.etaValue_ne_zero τ)\n",
        (Header(28296, 2, "`field_simp` made no progress"),),
        "Use the exact left-factor cancellation theorem on the exposed scalar goal.",
    ),
    Rule(
        "raw_differential_deck_comp_pin_intermediate_type",
        "        mfderiv 𝓘(ℂ) 𝓘(ℂ) (g.1 ∘ manifoldDeckMap γ) τ := by\n",
        "        (mfderiv 𝓘(ℂ) 𝓘(ℂ) (g.1 ∘ manifoldDeckMap γ) τ :\n"
        "          ScalarOneFormValue) := by\n",
        (Header(28353, 4, "invalid 'calc' step, failed to synthesize `Trans` instance"),),
        "Fix the dependent mfderiv codomain of the shared calc intermediate.",
    ),
    Rule(
        "raw_differential_add_pin_all_clm_types",
        "  change mfderiv 𝓘(ℂ) 𝓘(ℂ) (g.1 + h.1) τ =\n"
        "    mfderiv 𝓘(ℂ) 𝓘(ℂ) g.1 τ + mfderiv 𝓘(ℂ) 𝓘(ℂ) h.1 τ\n"
        "  exact mfderiv_add hg hh\n",
        "  change (mfderiv 𝓘(ℂ) 𝓘(ℂ) (g.1 + h.1) τ :\n"
        "      ScalarOneFormValue) =\n"
        "    (mfderiv 𝓘(ℂ) 𝓘(ℂ) g.1 τ : ScalarOneFormValue) +\n"
        "      (mfderiv 𝓘(ℂ) 𝓘(ℂ) h.1 τ : ScalarOneFormValue)\n"
        "  exact mfderiv_add hg hh\n",
        (Header(28366, 4, "failed to synthesize instance of type class"),),
        "Pin all three continuous-linear-map result types before HAdd synthesis.",
    ),
    Rule(
        "eta_covariant_derivative_apply_change_to_linear_rhs",
        "  have h := congrArg\n"
        "    (fun A : EtaTwistedOneForm => A.1 τ)\n"
        "    (etaCovariantDerivative_etaSection g)\n"
        "  simpa only [etaCovariantDerivativeLinear, covariantDerivativeLinear,\n"
        "    etaGaugeDifferential, rawDifferential] using h\n",
        "  change (etaCovariantDerivativeLinear (etaSectionLinear g)).1 τ =\n"
        "    (covariantDerivativeLinear g).1 τ\n"
        "  exact congrArg (fun A : EtaTwistedOneForm => A.1 τ)\n"
        "    (etaCovariantDerivative_etaSection g)\n",
        (Header(28526, 2, "Type mismatch: After simplification"),),
        "Use definitional equality only to expose the linear-map RHS, then exact congrArg.",
    ),
    Rule(
        "raw_differential_constant_one_close_reflexive",
        "  simp only [rawDifferential, constantOneInvariant, mfderiv_const]\n",
        "  simp only [rawDifferential, constantOneInvariant, mfderiv_const]\n"
        "  rfl\n",
        (Header(28730, 52, "unsolved goals"),),
        "The remaining compiler goal is exactly 0 = 0.",
    ),
    Rule(
        "eta_gauge_constant_one_reduce_clm_smul_apply",
        "  simp only [etaGaugeOneFormCoefficient, etaGaugeDifferential,\n"
        "    rawDifferential_constantOne, smul_zero, ContinuousLinearMap.zero_apply,\n"
        "    Pi.zero_apply]\n",
        "  simp only [etaGaugeOneFormCoefficient, etaGaugeDifferential,\n"
        "    rawDifferential_constantOne, ContinuousLinearMap.smul_apply,\n"
        "    smul_zero, ContinuousLinearMap.zero_apply, Pi.zero_apply]\n",
        (Header(28736, 59, "unsolved goals"),),
        "Reduce application of a scalar-multiplied zero continuous linear map before zero simp.",
    ),
)


def sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def blob(raw: bytes) -> str:
    return hashlib.sha1(f"blob {len(raw)}\0".encode("ascii") + raw).hexdigest()


def shape(raw: bytes) -> dict[str, object]:
    raw.decode("utf-8", errors="strict")
    return {
        "sha256": sha256(raw),
        "git_blob": blob(raw),
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


def expected(inverse: bool, result: bool) -> tuple[str, str, int, int]:
    source = (INPUT_SHA256, INPUT_GIT_BLOB, INPUT_BYTES, INPUT_LF)
    output = (OUTPUT_SHA256, OUTPUT_GIT_BLOB, OUTPUT_BYTES, OUTPUT_LF)
    if inverse:
        source, output = output, source
    return output if result else source


def check_shape(actual: dict[str, object], wanted: tuple[str, str, int, int], allow_unsealed: bool) -> None:
    if wanted[0] != "__TO_SEAL__" or not allow_unsealed:
        for key, value in zip(("sha256", "git_blob", "bytes", "lf"), wanted, strict=True):
            if actual[key] != value:
                raise RuntimeError(f"{key}: {actual[key]} != {value}")
    if actual["cr"] or actual["nul"] or actual["bom"] or not actual["terminal_lf"]:
        raise RuntimeError(f"text hygiene failure: {actual}")


def verify_log(raw: bytes) -> list[dict[str, object]]:
    if sha256(raw) != LOG_SHA256:
        raise RuntimeError(f"Probe7 log sha256 {sha256(raw)} != {LOG_SHA256}")
    text = raw.decode("utf-8")
    verified: list[dict[str, object]] = []
    for rule in RULES:
        for header in rule.headers:
            pattern = re.compile(
                rf"PrimalitySheafVerification/QYM\.lean:{header.line}:{header.column}: "
                rf"error(?:\([^\n)]*\))?: {re.escape(header.message)}"
            )
            count = len(pattern.findall(text))
            if count != 1:
                raise RuntimeError(f"{rule.label}: header count {count}, expected 1")
            verified.append({"rule": rule.label, "line": header.line, "column": header.column,
                             "message": header.message, "count": count})
    return verified


def transform(text: str, inverse: bool) -> tuple[str, list[dict[str, object]]]:
    audit: list[dict[str, object]] = []
    rules = tuple(reversed(RULES)) if inverse else RULES
    for rule in rules:
        old, new = (rule.new, rule.old) if inverse else (rule.old, rule.new)
        count = text.count(old)
        if count != rule.occurrences:
            raise RuntimeError(f"{rule.label}: exact count {count}, expected {rule.occurrences}")
        text = text.replace(old, new)
        audit.append({
            "label": rule.label,
            "direction": "inverse" if inverse else "forward",
            "occurrences": count,
            "direct_headers": [h.__dict__ for h in rule.headers],
            "rationale": rule.rationale,
        })
    return text, audit


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--probe7-log", type=Path, required=True)
    parser.add_argument("--audit", type=Path, required=True)
    parser.add_argument("--mode", choices=("forward", "inverse"), default="forward")
    parser.add_argument("--bootstrap-seal", action="store_true")
    args = parser.parse_args()
    inverse = args.mode == "inverse"

    source = args.input.read_bytes()
    source_shape = shape(source)
    check_shape(source_shape, expected(inverse, False), args.bootstrap_seal and inverse)
    verified = verify_log(args.probe7_log.read_bytes())
    source_text = source.decode("utf-8")
    before_trust = trust(source_text)
    result_text, rule_audit = transform(source_text, inverse)
    result = result_text.encode("utf-8")
    result_shape = shape(result)
    check_shape(result_shape, expected(inverse, True), args.bootstrap_seal and not inverse)
    after_trust = trust(result_text)
    if before_trust != after_trust or any(after_trust.values()):
        raise RuntimeError(f"trust changed or nonzero: {before_trust} -> {after_trust}")
    restored, _ = transform(result_text, not inverse)
    if restored.encode("utf-8") != source:
        raise RuntimeError("opposite transform failed byte identity")
    if args.output.exists() or args.audit.exists():
        raise RuntimeError("refusing to overwrite output or audit")

    record = {
        "schema": SCHEMA,
        "status": "STATIC_PASS_EXACT_PROBE7_AUTHORITY_NOT_LEAN_EXECUTED",
        "activation": True,
        "promotion": False,
        "mode": args.mode,
        "authority": {
            "probe7_run_id": 31967530559,
            "probe7_job_id": 95214871166,
            "probe7_artifact_id": 9268991946,
            "probe7_result_sha256": "5f63c123667c452b0d0b83cab03863ecdb849501bccff6bd95d787e89abb95c9",
            "probe7_candidate_sha256": INPUT_SHA256,
            "probe7_log_sha256": LOG_SHA256,
            "probe7_error_headers": 414,
            "probe7_warning_headers": 378,
            "probe7_exit": 1,
            "probe7_panic": 0,
        },
        "source": source_shape,
        "result": result_shape,
        "repair_families": len(RULES),
        "active_occurrences": sum(item["occurrences"] for item in rule_audit),
        "direct_headers_verified": len(verified),
        "rules": rule_audit,
        "selected_exact_probe7_lines": sorted({h.line for rule in RULES for h in rule.headers}),
        "inverse_byte_equal": True,
        "trust": after_trust,
        "execution": {"lean": False, "lake": False, "git_mutation": False, "network": False,
                      "remote": False, "repository_source_mutation": False},
    }
    args.output.write_bytes(result)
    args.audit.write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(json.dumps(record, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
