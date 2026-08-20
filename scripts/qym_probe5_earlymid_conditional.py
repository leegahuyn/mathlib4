#!/usr/bin/env python3
"""Conditional Probe5 repairs for the first independent Probe4 survivors.

The transformer is deliberately locked to the exact, statically integrated
Probe4 candidate.  It does not run Lean/Lake, inspect the network, mutate the
repository source, or authorize promotion.  Every rule is exact-count guarded
and the opposite transform must recover the input byte-for-byte.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from dataclasses import dataclass
from pathlib import Path


EXPECTED_PROBE4_INPUT_SHA256 = (
    "fb9d451c88d55e71398f3e3a4b38b3cc9ff5e0a37273115579fc2351d1fdad9c"
)
EXPECTED_PROBE4_INPUT_GIT_BLOB = "b08d7bb621d8acc8338f3afa3f12ac2ff2c7e6d1"
EXPECTED_PROBE4_INPUT_BYTES = 2_910_229
EXPECTED_PROBE4_INPUT_LF = 61_523
EXPECTED_PROBE3_LOG_SHA256 = (
    "501029e514ba6bc875527e1bc96fb9f571afda222e53e633078736dccaa71f56"
)

# Sealed after deriving the exact seven-rule projection in memory.
EXPECTED_CONDITIONAL_OUTPUT_SHA256 = (
    "1927b4432bc68bdbe6c7c1bdcc6bfb9c06e79e44013ea65d9d05373c9a491245"
)
EXPECTED_CONDITIONAL_OUTPUT_GIT_BLOB = "268a3ffe4b0adcead567b75fe4d95126c4174c03"
EXPECTED_CONDITIONAL_OUTPUT_BYTES = 2_910_598
EXPECTED_CONDITIONAL_OUTPUT_LF = 61_534


@dataclass(frozen=True)
class ExactRule:
    label: str
    probe3_error_lines: tuple[int, ...]
    old: str
    new: str
    expected: int = 1


RULES: tuple[ExactRule, ...] = (
    ExactRule(
        "expose_addEverywhere_value_in_adjoint_domain_proof",
        (21738,),
        "      _ = ⟪y, A x⟫ := by\n"
        "            rw [addEverywhere_apply, inner_add_right]\n"
        "            simp\n",
        "      _ = ⟪y, A x⟫ := by\n"
        "            change\n"
        "              ⟪y, B (x : H) + A x⟫ - ⟪y, B (x : H)⟫ = ⟪y, A x⟫\n"
        "            rw [inner_add_right]\n"
        "            exact add_sub_cancel_left _ _\n",
    ),
    ExactRule(
        "pin_real_inner_argument_for_neg_abs_le",
        (21838,),
        "      exact add_le_add_left (neg_abs_le _) _\n",
        "      exact add_le_add_left\n"
        "        (neg_abs_le (inner ℝ (B (x : H₀)) (x : H₀)))\n"
        "        (inner ℝ (A x) (x : H₀))\n",
    ),
    ExactRule(
        "expose_real_addEverywhere_value_before_inner_add_left",
        (21839,),
        "    _ = inner ℝ (addEverywhere B.toLinearMap A x) (x : H₀) := by\n"
        "      rw [addEverywhere_apply, inner_add_left, add_comm]\n",
        "    _ = inner ℝ (addEverywhere B.toLinearMap A x) (x : H₀) := by\n"
        "      change\n"
        "        inner ℝ (A x) (x : H₀) + inner ℝ (B (x : H₀)) (x : H₀) =\n"
        "          inner ℝ (B (x : H₀) + A x) (x : H₀)\n"
        "      rw [inner_add_left, add_comm]\n",
    ),
    ExactRule(
        "unfold_perturbedRealization_before_realization_diagonal_rewrite",
        (22250,),
        "  rw [hNorm] at hLower\n"
        "  rw [QYM.FormDomainRealizationExtension.inner_realization_self\n"
        "    (perturbedForm B E) j hj hjDense x]\n",
        "  rw [hNorm] at hLower\n"
        "  unfold perturbedRealization\n"
        "  rw [QYM.FormDomainRealizationExtension.inner_realization_self\n"
        "    (perturbedForm B E) j hj hjDense x]\n",
    ),
    ExactRule(
        "expose_domainEquiv_underlying_formEmbedding",
        (23013,),
        "@[simp]\n"
        "theorem coe_domainEquiv_apply\n"
        "    (B : SesqForm 𝕜 V) (j : V →L[𝕜] H)\n"
        "    (hj : Function.Injective j) (u : formDomain B j) :\n"
        "    ((domainEquiv B j hj u : operatorDomain B j) : H) = j (u : V) := by\n"
        "  simp only [domainEquiv, LinearEquiv.ofInjective_apply, formEmbedding_apply]\n",
        "@[simp]\n"
        "theorem coe_domainEquiv_apply\n"
        "    (B : SesqForm 𝕜 V) (j : V →L[𝕜] H)\n"
        "    (hj : Function.Injective j) (u : formDomain B j) :\n"
        "    ((domainEquiv B j hj u : operatorDomain B j) : H) = j (u : V) := by\n"
        "  change formEmbedding B j u = j (u : V)\n"
        "  exact formEmbedding_apply B j u\n",
    ),
    ExactRule(
        "expose_formEmbedding_in_operatorDomain_witness",
        (23038,),
        "theorem embed_mem_operatorDomain_iff\n"
        "    (B : SesqForm 𝕜 V) {j : V →L[𝕜] H}\n"
        "    (hj : Function.Injective j) (u : V) :\n"
        "    j u ∈ operatorDomain B j ↔ ∃ f : H, Represents B j u f := by\n"
        "  constructor\n"
        "  · rintro ⟨w, hw⟩\n"
        "    have hwu : (w : V) = u := by\n"
        "      apply hj\n"
        "      simpa only [formEmbedding_apply] using hw\n",
        "theorem embed_mem_operatorDomain_iff\n"
        "    (B : SesqForm 𝕜 V) {j : V →L[𝕜] H}\n"
        "    (hj : Function.Injective j) (u : V) :\n"
        "    j u ∈ operatorDomain B j ↔ ∃ f : H, Represents B j u f := by\n"
        "  constructor\n"
        "  · rintro ⟨w, hw⟩\n"
        "    have hwu : (w : V) = u := by\n"
        "      apply hj\n"
        "      change formEmbedding B j w = j u at hw\n"
        "      exact hw\n",
    ),
    ExactRule(
        "beta_reduce_formEmbedding_denseRange_composition",
        (23160,),
        "  have hcomp : DenseRange (j ∘ fun u : formDomain B j => (u : V)) :=\n"
        "    hjDense.comp hFormDense.denseRange_val j.continuous\n"
        "  change DenseRange (fun u : formDomain B j => j (u : V))\n"
        "  simpa only [Function.comp_apply] using hcomp\n",
        "  have hcomp : DenseRange (j ∘ fun u : formDomain B j => (u : V)) :=\n"
        "    hjDense.comp hFormDense.denseRange_val j.continuous\n"
        "  change DenseRange (fun u : formDomain B j => j (u : V))\n"
        "  change DenseRange (fun u : formDomain B j => j (u : V)) at hcomp\n"
        "  exact hcomp\n",
    ),
)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git_blob(data: bytes) -> str:
    header = b"blob " + str(len(data)).encode("ascii") + b"\0"
    return hashlib.sha1(header + data).hexdigest()


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
        "utf8": True,
    }


def trust_counts(text: str) -> dict[str, int]:
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


def transform(text: str, *, inverse: bool) -> tuple[str, list[dict[str, object]]]:
    sequence = tuple(reversed(RULES)) if inverse else RULES
    audit: list[dict[str, object]] = []
    for rule in sequence:
        old, new = (rule.new, rule.old) if inverse else (rule.old, rule.new)
        count = text.count(old)
        if count != rule.expected:
            raise RuntimeError(
                f"{rule.label}: {count} exact occurrences, expected {rule.expected}"
            )
        text = text.replace(old, new)
        audit.append(
            {
                "label": rule.label,
                "probe3_error_lines": list(rule.probe3_error_lines),
                "occurrences": count,
                "direction": "inverse" if inverse else "forward",
            }
        )
    return text, audit


def expected_source(*, inverse: bool) -> tuple[str, str, int, int]:
    if inverse:
        return (
            EXPECTED_CONDITIONAL_OUTPUT_SHA256,
            EXPECTED_CONDITIONAL_OUTPUT_GIT_BLOB,
            EXPECTED_CONDITIONAL_OUTPUT_BYTES,
            EXPECTED_CONDITIONAL_OUTPUT_LF,
        )
    return (
        EXPECTED_PROBE4_INPUT_SHA256,
        EXPECTED_PROBE4_INPUT_GIT_BLOB,
        EXPECTED_PROBE4_INPUT_BYTES,
        EXPECTED_PROBE4_INPUT_LF,
    )


def expected_result(*, inverse: bool) -> tuple[str, str, int, int]:
    return expected_source(inverse=not inverse)


def assert_sealed(values: tuple[str, str, int, int]) -> None:
    if "__TO_SEAL__" in values[:2] or values[2] < 0 or values[3] < 0:
        raise RuntimeError("conditional output identity has not been sealed")


def assert_shape(actual: dict[str, object], expected: tuple[str, str, int, int]) -> None:
    assert_sealed(expected)
    keys = ("sha256", "git_blob", "bytes", "lf")
    for key, wanted in zip(keys, expected, strict=True):
        if actual[key] != wanted:
            raise RuntimeError(f"{key} mismatch: {actual[key]} != {wanted}")
    if actual["cr"] or actual["nul"] or actual["bom"] or not actual["terminal_lf"]:
        raise RuntimeError(f"text hygiene failure: {actual}")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--audit", type=Path, required=True)
    parser.add_argument("--mode", choices=("forward", "inverse"), default="forward")
    args = parser.parse_args()

    inverse = args.mode == "inverse"
    source = args.input.read_bytes()
    source_shape = shape(source)
    assert_shape(source_shape, expected_source(inverse=inverse))
    source_text = source.decode("utf-8")
    before_trust = trust_counts(source_text)

    result_text, rules = transform(source_text, inverse=inverse)
    result = result_text.encode("utf-8")
    result_shape = shape(result)
    assert_shape(result_shape, expected_result(inverse=inverse))
    after_trust = trust_counts(result_text)
    if after_trust != before_trust:
        raise RuntimeError(f"trust inventory changed: {before_trust} -> {after_trust}")

    restored_text, _ = transform(result_text, inverse=not inverse)
    if restored_text.encode("utf-8") != source:
        raise RuntimeError("opposite transform failed byte-exact roundtrip")

    if args.output.exists() or args.audit.exists():
        raise RuntimeError("refusing to overwrite output or audit")
    args.output.write_bytes(result)
    audit = {
        "schema": "qym-probe5-earlymid-conditional-transform-v1",
        "status": "STATIC_CONDITIONAL_ONLY_NOT_PROBE4_CONFIRMED_NOT_LEAN_EXECUTED",
        "mode": args.mode,
        "authority": {
            "probe4_candidate_sha256": EXPECTED_PROBE4_INPUT_SHA256,
            "probe4_candidate_git_blob": EXPECTED_PROBE4_INPUT_GIT_BLOB,
            "probe3_log_sha256": EXPECTED_PROBE3_LOG_SHA256,
            "scope_probe3_lines": [17600, 40000],
            "first_likely_remaining_error_line": 21738,
        },
        "source": source_shape,
        "result": result_shape,
        "rules": rules,
        "active_occurrences": sum(item["occurrences"] for item in rules),
        "inverse_byte_equal": True,
        "trust_counts": after_trust,
        "activation_gate": {
            "promotion_authorized": False,
            "probe4_terminal_artifact_checked": False,
            "required": (
                "Exact Probe4 artifact for candidate fb9d451c must confirm matching "
                "surviving owner diagnostics before composition into Probe5."
            ),
        },
        "execution": {"lean": False, "lake": False, "remote": False},
    }
    args.audit.write_text(
        json.dumps(audit, ensure_ascii=False, indent=2) + "\n", encoding="utf-8"
    )
    print(json.dumps(audit, ensure_ascii=False, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
