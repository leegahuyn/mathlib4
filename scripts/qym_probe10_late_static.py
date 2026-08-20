#!/usr/bin/env python3
"""Conditional exact-P9 repairs for surviving direct QYM roots after line 50000.

This helper is an activation-disabled, byte-locked, exact-counted and
reversible static transformer.  It reads only the immutable Probe9 authority
artifacts and the exact sibling helper used for collision exclusion.  It
does not invoke Lean, Lake, Git, a network, or mutate repository sources.
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

SCHEMA = "qym-probe10-late-static-transform-v2-exact-probe9"
INPUT_SHA256 = "fb37854ff158ae20a2acebe7722847726eb651ba9c716eff6b903cb4f32e8029"
INPUT_GIT_BLOB = "d29c6aff411f93b3c44d7d866fe2b2558f616a87"
INPUT_BYTES = 2_921_397
INPUT_LF = 61_746
LOG_SHA256 = "e8315f541ddcd8d9f99a395caddbcf57ceb3a1457a900bcefb45422dff81cd0f"
HEADERS_SHA256 = "e8b25cc78d4f2a9915cd25c6c7700f7f80ca73c7f01229fe531e3ef13386186f"
DIAGNOSTICS_SHA256 = "a34f5b424f8aac739ac05ce4375003fe9da7f0ee4689050d4d712c9816f66580"

# Filled from the deterministic bootstrap projection, then enforced both ways.
OUTPUT_SHA256 = "f31c5aeaf56f8b751cc92b7be4ba0685601f05c55a351ac8695fcb970fb36d78"
OUTPUT_GIT_BLOB = "781f4aff16af80292dfa1a0fccec74514377949f"
OUTPUT_BYTES = 2_922_171
OUTPUT_LF = 61_754

ACTIVE_FOREIGN_HELPER_SHA256 = {
    "qym_probe10_midlate_static.py":
        "42d8f76c68b19aac520d15659c71d02db2e1beb397cfe0865bcdaf436e885be0",
}


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
        "ambient_zero_extension_add_reduce_pi_add_apply",
        "  by_cases hx : x ∈ QYM.FullCertification.P2IntrinsicTruncatedQuotientExtension.XSet Y\n"
        "  · simp only [hx, Set.indicator_of_mem]\n"
        "  · simp only [hx, Set.indicator_of_notMem, add_zero]\n"
        "\n"
        "theorem ambientZeroExtension_smul",
        "  by_cases hx : x ∈ QYM.FullCertification.P2IntrinsicTruncatedQuotientExtension.XSet Y\n"
        "  · simp only [hx, Set.indicator_of_mem, Pi.add_apply]\n"
        "  · simp only [hx, Set.indicator_of_notMem, add_zero]\n"
        "\n"
        "theorem ambientZeroExtension_smul",
        (Header(50726, 2, "unsolved goals"),),
        "After indicator reduction, expose pointwise addition of the two source representatives.",
    ),
    Rule(
        "ambient_zero_extension_smul_reduce_pi_smul_apply",
        "  by_cases hx : x ∈ QYM.FullCertification.P2IntrinsicTruncatedQuotientExtension.XSet Y\n"
        "  · simp only [hx, Set.indicator_of_mem]\n"
        "  · simp only [hx, Set.indicator_of_notMem, smul_zero]\n"
        "\n"
        "/-- Extension by zero as a linear map. -/",
        "  by_cases hx : x ∈ QYM.FullCertification.P2IntrinsicTruncatedQuotientExtension.XSet Y\n"
        "  · simp only [hx, Set.indicator_of_mem, Pi.smul_apply]\n"
        "  · simp only [hx, Set.indicator_of_notMem, smul_zero]\n"
        "\n"
        "/-- Extension by zero as a linear map. -/",
        (Header(50746, 2, "unsolved goals"),),
        "After indicator reduction, expose pointwise scalar multiplication of the source representative.",
    ),
    Rule(
        "ambient_zero_extension_trans_reduce_both_negative_indicators",
        "  · by_cases hxZ : x ∈ QYM.FullCertification.P2IntrinsicTruncatedQuotientExtension.XSet Z\n"
        "    · simp only [hx, hxZ, Set.indicator_of_mem,\n"
        "        Set.indicator_of_notMem]\n"
        "    · rfl\n",
        "  · by_cases hxZ : x ∈ QYM.FullCertification.P2IntrinsicTruncatedQuotientExtension.XSet Z\n"
        "    · simp only [hx, hxZ, Set.indicator_of_mem,\n"
        "        Set.indicator_of_notMem]\n"
        "    · simp only [hx, hxZ, Set.indicator_of_notMem]\n",
        (Header(50865, 6, "Tactic `rfl` failed: The left-hand side"),),
        "The doubly negative branch is propositionally, not definitionally, reduced by both indicator lemmas.",
    ),
    Rule(
        "inner_indicator_right_reduce_negative_branch",
        "  by_cases hx : x ∈ s\n"
        "  · simp only [hx, Set.indicator_of_mem]\n"
        "  · rfl\n"
        "\n"
        "/-- Restriction and extension by zero are adjoint.",
        "  by_cases hx : x ∈ s\n"
        "  · simp only [hx, Set.indicator_of_mem]\n"
        "  · simp only [hx, Set.indicator_of_notMem, inner_zero_right]\n"
        "\n"
        "/-- Restriction and extension by zero are adjoint.",
        (Header(50886, 4, "Tactic `rfl` failed: The left-hand side"),),
        "Reduce both negative indicators and the resulting zero right argument of the inner product.",
    ),
    Rule(
        "complex_bounded_resolvent_bundle_before_function_coercion",
        "    ¬ IsCompactOperator\n"
        "      (resolvent (T.restrictScalars ℝ) r :\n"
        "        QYM.FullCertification.P3ActualStageL2SectionsExtension.ActualStageInverseEtaL2Section Y →\n"
        "          QYM.FullCertification.P3ActualStageL2SectionsExtension.ActualStageInverseEtaL2Section Y) := by\n",
        "    ¬ IsCompactOperator\n"
        "      ((resolvent (T.restrictScalars ℝ) r :\n"
        "          QYM.FullCertification.P3ActualStageL2SectionsExtension.ActualStageInverseEtaL2Section Y →L[ℝ]\n"
        "            QYM.FullCertification.P3ActualStageL2SectionsExtension.ActualStageInverseEtaL2Section Y) :\n"
        "        QYM.FullCertification.P3ActualStageL2SectionsExtension.ActualStageInverseEtaL2Section Y →\n"
        "          QYM.FullCertification.P3ActualStageL2SectionsExtension.ActualStageInverseEtaL2Section Y) := by\n",
        (Header(55093, 7, "failed to synthesize instance of type class", "lean.synthInstanceFailed"),),
        "Pin the resolvent in the real continuous-linear-map algebra before coercing it to a function.",
    ),
    Rule(
        "global_projection_absorb_left_unfold_outer_before_inner",
        "  rw [houter, hinner, hdirect]\n"
        "  by_cases hxm : x ∈ naturalStageSet m\n"
        "  · have hxn : x ∈ naturalStageSet n :=\n"
        "      naturalStageSet_monotone hmn hxm\n"
        "    simp only [globalStageProjectionRepresentative, hxm, hxn,\n"
        "      Set.indicator_of_mem]\n"
        "  · simp only [globalStageProjectionRepresentative, hxm,\n"
        "      Set.indicator_of_notMem]\n",
        "  rw [houter, hdirect]\n"
        "  by_cases hxm : x ∈ naturalStageSet m\n"
        "  · have hxn : x ∈ naturalStageSet n :=\n"
        "      naturalStageSet_monotone hmn hxm\n"
        "    rw [globalStageProjectionRepresentative,\n"
        "      Set.indicator_of_mem hxm, hinner,\n"
        "      globalStageProjectionRepresentative,\n"
        "      Set.indicator_of_mem hxn]\n"
        "  · rw [globalStageProjectionRepresentative,\n"
        "      Set.indicator_of_notMem hxm, Set.indicator_of_notMem hxm]\n",
        (Header(57132, 14, "Tactic `rewrite` failed: Did not find an occurrence of the pattern"),),
        "Expose the outer indicator before rewriting the larger projection representative at the point.",
    ),
    Rule(
        "global_projection_absorb_right_use_only_needed_inner_equality",
        "  rw [houter, hinner]\n"
        "  by_cases hxm : x ∈ naturalStageSet m\n"
        "  · have hxn : x ∈ naturalStageSet n :=\n"
        "      naturalStageSet_monotone hmn hxm\n"
        "    simp only [globalStageProjectionRepresentative, hxm, hxn,\n"
        "      Set.indicator_of_mem]\n"
        "  · by_cases hxn : x ∈ naturalStageSet n\n"
        "    · simp only [globalStageProjectionRepresentative, hxm, hxn,\n"
        "        Set.indicator_of_mem, Set.indicator_of_notMem]\n"
        "    · simp only [globalStageProjectionRepresentative, hxm, hxn,\n"
        "        Set.indicator_of_notMem]\n",
        "  rw [houter]\n"
        "  by_cases hxn : x ∈ naturalStageSet n\n"
        "  · rw [globalStageProjectionRepresentative,\n"
        "      Set.indicator_of_mem hxn]\n"
        "  · have hxm : x ∉ naturalStageSet m :=\n"
        "      fun hx => hxn (naturalStageSet_monotone hmn hx)\n"
        "    rw [globalStageProjectionRepresentative,\n"
        "      Set.indicator_of_notMem hxn, hinner,\n"
        "      globalStageProjectionRepresentative,\n"
        "      Set.indicator_of_notMem hxm]\n",
        (
            Header(57154, 2, "unsolved goals"),
            Header(57159, 4, "unsolved goals"),
            Header(57161, 4, "unsolved goals"),
        ),
        "The inner representative equality is needed only when the larger-stage indicator vanishes.",
    ),
    Rule(
        "global_projection_reverse_comp_remove_third_stale_apply",
        "  rw [ContinuousLinearMap.comp_apply,\n"
        "    globalStageProjectionCLM_apply,\n"
        "    globalStageProjectionCLM_apply,\n"
        "    globalStageProjectionCLM_apply,\n"
        "    globalStageProjection_absorb_right hmn]\n",
        "  rw [ContinuousLinearMap.comp_apply,\n"
        "    globalStageProjectionCLM_apply,\n"
        "    globalStageProjectionCLM_apply,\n"
        "    globalStageProjection_absorb_right hmn]\n",
        (Header(57187, 4, "Tactic `rewrite` failed: Did not find an occurrence of the pattern"),),
        "Two coercion rewrites already expose both raw projections consumed by the absorption theorem.",
    ),
    Rule(
        "global_projection_error_bound_unfold_natural_stage_set",
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
        (
            Header(57279, 2, "unsolved goals"),
            Header(57282, 2, "unsolved goals"),
        ),
        "Unfold the named stage set so membership simplifies the underlying XSet indicator.",
    ),
    Rule(
        "global_projection_error_eventually_zero_unfold_natural_stage_set",
        "  simp [globalStageProjectionErrorDensity,\n"
        "    globalStageProjectionRepresentative, hn]\n"
        "\n"
        "/-- Pointwise convergence of the square-error densities to zero. -/",
        "  simp [globalStageProjectionErrorDensity, naturalStageSet,\n"
        "    globalStageProjectionRepresentative, hn]\n"
        "\n"
        "/-- Pointwise convergence of the square-error densities to zero. -/",
        (Header(57304, 66, "unsolved goals"),),
        "Expose naturalStageSet as the exact XSet used by the indicator before reducing the error to zero.",
    ),
    Rule(
        "global_projection_error_tendsto_unfold_natural_stage_set",
        "  simp [globalStageProjectionErrorDensity,\n"
        "    globalStageProjectionRepresentative, hx]\n"
        "\n"
        "/-- Dominated convergence for the integrals of the actual cutoff error",
        "  simp [globalStageProjectionErrorDensity, naturalStageSet,\n"
        "    globalStageProjectionRepresentative, hx]\n"
        "\n"
        "/-- Dominated convergence for the integrals of the actual cutoff error",
        (Header(57313, 21, "unsolved goals"),),
        "Expose naturalStageSet so the eventual membership proof reduces the underlying indicator.",
    ),
    Rule(
        "cutoff_escape_kernel_expose_bundled_applications",
        "  ext u\n"
        "  constructor\n"
        "  · intro hu\n"
        "    rw [LinearMap.mem_ker,\n"
        "      actualCutoffEscapeHamiltonian_eq_zero_iff] at hu\n"
        "    exact ⟨u, hu⟩\n"
        "  · rintro ⟨v, rfl⟩\n"
        "    rw [LinearMap.mem_ker,\n"
        "      actualCutoffEscapeHamiltonian_eq_zero_iff,\n"
        "      QYM.FullCertification.P14ActualGlobalL2ProjectionConvergenceExtension.globalStageProjectionCLM_apply,\n"
        "      QYM.FullCertification.P14ActualGlobalL2ProjectionConvergenceExtension.globalStageProjectionCLM_apply,\n"
        "      QYM.FullCertification.P14ActualGlobalL2ProjectionConvergenceExtension.globalStageProjection_idempotent]\n",
        "  ext u\n"
        "  constructor\n"
        "  · intro hu\n"
        "    rw [LinearMap.mem_ker] at hu\n"
        "    change actualCutoffEscapeHamiltonian n u = 0 at hu\n"
        "    rw [actualCutoffEscapeHamiltonian_eq_zero_iff] at hu\n"
        "    exact ⟨u, hu⟩\n"
        "  · rintro ⟨v, rfl⟩\n"
        "    rw [LinearMap.mem_ker]\n"
        "    change actualCutoffEscapeHamiltonian n\n"
        "      (QYM.FullCertification.P14ActualGlobalL2ProjectionConvergenceExtension.globalStageProjectionCLM n v) = 0\n"
        "    rw [actualCutoffEscapeHamiltonian_eq_zero_iff,\n"
        "      QYM.FullCertification.P14ActualGlobalL2ProjectionConvergenceExtension.globalStageProjectionCLM_apply,\n"
        "      QYM.FullCertification.P14ActualGlobalL2ProjectionConvergenceExtension.globalStageProjectionCLM_apply,\n"
        "      QYM.FullCertification.P14ActualGlobalL2ProjectionConvergenceExtension.globalStageProjection_idempotent]\n",
        (
            Header(59585, 6, "Tactic `rewrite` failed: Did not find an occurrence of the pattern"),
            Header(59589, 6, "Tactic `rewrite` failed: Did not find an occurrence of the pattern"),
        ),
        "Expose the coerced escape-Hamiltonian applications before invoking its equality characterization.",
    ),
    Rule(
        "cutoff_moving_offground_expose_bundled_applications",
        "  ext u\n"
        "  constructor\n"
        "  · rintro ⟨v, rfl⟩\n"
        "    rw [LinearMap.mem_ker,\n"
        "      actualCutoffEscapeHamiltonian_apply, map_sub]\n"
        "    have hIdempotent :\n"
        "        QYM.FullCertification.P14ActualGlobalL2ProjectionConvergenceExtension.globalStageProjectionCLM n\n"
        "            (QYM.FullCertification.P14ActualGlobalL2ProjectionConvergenceExtension.globalStageProjectionCLM n v) =\n"
        "          QYM.FullCertification.P14ActualGlobalL2ProjectionConvergenceExtension.globalStageProjectionCLM n v := by\n"
        "      rw [QYM.FullCertification.P14ActualGlobalL2ProjectionConvergenceExtension.globalStageProjectionCLM_apply,\n"
        "        QYM.FullCertification.P14ActualGlobalL2ProjectionConvergenceExtension.globalStageProjectionCLM_apply,\n"
        "        QYM.FullCertification.P14ActualGlobalL2ProjectionConvergenceExtension.globalStageProjection_idempotent]\n"
        "    rw [hIdempotent, sub_self]\n"
        "  · intro hu\n"
        "    rw [LinearMap.mem_ker] at hu\n"
        "    refine ⟨u, ?_⟩\n"
        "    rw [actualCutoffEscapeHamiltonian_apply, hu, sub_zero]\n",
        "  ext u\n"
        "  constructor\n"
        "  · rintro ⟨v, rfl⟩\n"
        "    rw [LinearMap.mem_ker]\n"
        "    change QYM.FullCertification.P14ActualGlobalL2ProjectionConvergenceExtension.globalStageProjectionCLM n\n"
        "      (actualCutoffEscapeHamiltonian n v) = 0\n"
        "    rw [actualCutoffEscapeHamiltonian_apply, map_sub]\n"
        "    have hIdempotent :\n"
        "        QYM.FullCertification.P14ActualGlobalL2ProjectionConvergenceExtension.globalStageProjectionCLM n\n"
        "            (QYM.FullCertification.P14ActualGlobalL2ProjectionConvergenceExtension.globalStageProjectionCLM n v) =\n"
        "          QYM.FullCertification.P14ActualGlobalL2ProjectionConvergenceExtension.globalStageProjectionCLM n v := by\n"
        "      rw [QYM.FullCertification.P14ActualGlobalL2ProjectionConvergenceExtension.globalStageProjectionCLM_apply,\n"
        "        QYM.FullCertification.P14ActualGlobalL2ProjectionConvergenceExtension.globalStageProjectionCLM_apply,\n"
        "        QYM.FullCertification.P14ActualGlobalL2ProjectionConvergenceExtension.globalStageProjection_idempotent]\n"
        "    rw [hIdempotent, sub_self]\n"
        "  · intro hu\n"
        "    rw [LinearMap.mem_ker] at hu\n"
        "    refine ⟨u, ?_⟩\n"
        "    change actualCutoffEscapeHamiltonian n u = u\n"
        "    rw [actualCutoffEscapeHamiltonian_apply, hu, sub_zero]\n",
        (
            Header(59606, 6, "Tactic `rewrite` failed: Did not find an occurrence of the pattern"),
            Header(59618, 8, "Tactic `rewrite` failed: Did not find an occurrence of the pattern"),
        ),
        "Expose both bundled operator applications before map and kernel rewrites.",
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


def check_shape(
    actual: dict[str, object],
    wanted: tuple[str, str, int, int],
    *,
    allow_unsealed: bool,
) -> None:
    if wanted[0] != "__TO_SEAL__" or not allow_unsealed:
        for key, value in zip(("sha256", "git_blob", "bytes", "lf"), wanted, strict=True):
            if actual[key] != value:
                raise RuntimeError(f"{key}: {actual[key]} != {value}")
    if actual["cr"] or actual["nul"] or actual["bom"] or not actual["terminal_lf"]:
        raise RuntimeError(f"text hygiene failure: {actual}")


def verify_authority(
    log_raw: bytes, headers_raw: bytes, diagnostics_raw: bytes
) -> list[dict[str, object]]:
    if sha256(log_raw) != LOG_SHA256:
        raise RuntimeError("Probe9 log identity mismatch")
    if sha256(headers_raw) != HEADERS_SHA256:
        raise RuntimeError("Probe9 error-header identity mismatch")
    if sha256(diagnostics_raw) != DIAGNOSTICS_SHA256:
        raise RuntimeError("Probe9 diagnostics identity mismatch")
    log_text = log_raw.decode("utf-8", errors="strict")
    headers = headers_raw.decode("utf-8", errors="strict").splitlines()
    log_headers = [
        line for line in log_text.splitlines()
        if re.match(
            r"^PrimalitySheafVerification/QYM\.lean:\d+:\d+: error(?:\([^)]*\))?: ",
            line,
        )
    ]
    if headers != log_headers or len(headers) != 287:
        raise RuntimeError("Probe9 error-header reconstruction mismatch")
    warning_count = len(re.findall(
        r"^PrimalitySheafVerification/QYM\.lean:\d+:\d+: warning(?:\([^)]*\))?: ",
        log_text,
        re.MULTILINE,
    ))
    if warning_count != 361:
        raise RuntimeError(f"Probe9 warning count {warning_count} != 361")
    diagnostics = [json.loads(line) for line in diagnostics_raw.decode("utf-8").splitlines()]
    error_rows = [row for row in diagnostics if row.get("severity") == "error"]
    warning_rows = [row for row in diagnostics if row.get("severity") == "warning"]
    if len(error_rows) != 287 or len(warning_rows) != 361:
        raise RuntimeError("Probe9 diagnostics severity counts mismatch")

    verified: list[dict[str, object]] = []
    for rule in RULES:
        for header in rule.headers:
            rows = [
                row for row in error_rows
                if row.get("line") == header.line
                and row.get("column") == header.column
                and row.get("message") == header.message
                and row.get("code") == header.code
            ]
            if len(rows) != 1:
                raise RuntimeError(
                    f"{rule.label}: diagnostic count {len(rows)}, expected 1"
                )
            verified.append({
                "rule": rule.label,
                "line": header.line,
                "column": header.column,
                "message": header.message,
                "code": header.code,
                "count": 1,
            })
    return verified


def apply_rules(text: str, inverse: bool = False) -> tuple[str, list[dict[str, object]]]:
    audit: list[dict[str, object]] = []
    selected = tuple(reversed(RULES)) if inverse else RULES
    for rule in selected:
        old, new = (rule.new, rule.old) if inverse else (rule.old, rule.new)
        count = text.count(old)
        if count != rule.occurrences:
            raise RuntimeError(
                f"{rule.label}: exact anchor count {count}, expected {rule.occurrences}"
            )
        text = text.replace(old, new)
        audit.append({
            "label": rule.label,
            "direction": "inverse" if inverse else "forward",
            "occurrences": count,
            "direct_headers": [header.__dict__ for header in rule.headers],
            "rationale": rule.rationale,
        })
    return text, audit


# Compatibility alias for tranche integrators.
transform = apply_rules


def spans(text: str, needle: str) -> list[tuple[int, int]]:
    found: list[tuple[int, int]] = []
    start = 0
    while True:
        offset = text.find(needle, start)
        if offset < 0:
            return found
        found.append((offset, offset + len(needle)))
        start = offset + 1


def load_helper(path: Path) -> ModuleType:
    module_name = "_qym_foreign_" + hashlib.sha256(str(path).encode()).hexdigest()
    spec = importlib.util.spec_from_file_location(module_name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot import helper: {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[module_name] = module
    spec.loader.exec_module(module)
    return module


def audit_foreign_spans(
    base: str, foreign_helpers: list[Path], inverse: bool = False
) -> dict[str, object]:
    by_name = {path.name: path for path in foreign_helpers}
    if set(by_name) != set(ACTIVE_FOREIGN_HELPER_SHA256):
        raise RuntimeError("foreign helper set is not the exact active exclusion set")
    own = [
        (start, end, rule.label)
        for rule in RULES
        for start, end in spans(base, rule.new if inverse else rule.old)
    ]
    if len(own) != sum(rule.occurrences for rule in RULES):
        raise RuntimeError("own exact-P9 span inventory mismatch")

    identities: dict[str, str] = {}
    overlaps: list[dict[str, object]] = []
    exact_equalities = 0
    foreign_families = 0
    own_anchors = {value for rule in RULES for value in (rule.old, rule.new)}
    for name, expected_sha in ACTIVE_FOREIGN_HELPER_SHA256.items():
        path = by_name[name]
        digest = sha256(path.read_bytes())
        if digest != expected_sha:
            raise RuntimeError(f"foreign helper identity mismatch: {name}")
        identities[name] = digest
        module = load_helper(path)
        foreign_rules = getattr(module, "RULES", None)
        if foreign_rules is None:
            raise RuntimeError(f"foreign helper has no RULES: {name}")
        for foreign_rule in foreign_rules:
            foreign_families += 1
            old = getattr(foreign_rule, "old")
            new = getattr(foreign_rule, "new")
            exact_equalities += int(old in own_anchors) + int(new in own_anchors)
            matches = spans(base, old)
            expected_count = getattr(foreign_rule, "occurrences", 1)
            if len(matches) != expected_count:
                raise RuntimeError(
                    f"foreign exact-P9 anchor count mismatch: {name}:"
                    f"{getattr(foreign_rule, 'label')}:{len(matches)}!={expected_count}"
                )
            for fstart, fend in matches:
                for ostart, oend, own_label in own:
                    if max(fstart, ostart) < min(fend, oend):
                        overlaps.append({
                            "own": own_label,
                            "foreign_helper": name,
                            "foreign_rule": getattr(foreign_rule, "label"),
                        })
    if exact_equalities or overlaps:
        raise RuntimeError(
            f"active-helper collision: equalities={exact_equalities}, overlaps={overlaps}"
        )
    return {
        "foreign_helper_sha256": identities,
        "foreign_rule_families_checked": foreign_families,
        "own_spans_checked": len(own),
        "exact_anchor_equalities": exact_equalities,
        "span_overlaps": overlaps,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--probe9-log", type=Path, required=True)
    parser.add_argument("--probe9-error-headers", type=Path, required=True)
    parser.add_argument("--probe9-diagnostics", type=Path, required=True)
    parser.add_argument("--foreign-helper", type=Path, action="append", required=True)
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
    diagnostic_map = verify_authority(
        args.probe9_log.read_bytes(),
        args.probe9_error_headers.read_bytes(),
        args.probe9_diagnostics.read_bytes(),
    )
    source_text = source.decode("utf-8", errors="strict")
    collision_audit = audit_foreign_spans(
        source_text, args.foreign_helper, inverse=inverse
    )
    before_trust = trust(source_text)
    result_text, rule_audit = apply_rules(source_text, inverse)
    result = result_text.encode("utf-8")
    result_shape = shape(result)
    check_shape(
        result_shape,
        expected(inverse, True),
        allow_unsealed=args.bootstrap_seal and not inverse,
    )
    after_trust = trust(result_text)
    if before_trust != after_trust or any(after_trust.values()):
        raise RuntimeError(f"trust0 failure: {before_trust} -> {after_trust}")
    restored_text, _ = apply_rules(result_text, not inverse)
    if restored_text.encode("utf-8") != source:
        raise RuntimeError("opposite transform did not restore source byte-for-byte")
    if args.output.exists() or args.audit.exists():
        raise RuntimeError("refusing to overwrite output or audit")

    record = {
        "schema": SCHEMA,
        "status": "STATIC_PASS_EXACT_PROBE9_AUTHORITY_NOT_LEAN_EXECUTED",
        "activation": False,
        "promotion": False,
        "mode": args.mode,
        "authority": {
            "probe9_run_id": 31971447929,
            "probe9_trigger_sha": "3b5e67d81c4d8979f2c4b57c9f2b7839b0806388",
            "probe9_result_source": "PROBE_RESULT.json",
            "candidate_sha256": INPUT_SHA256,
            "candidate_git_blob": INPUT_GIT_BLOB,
            "log_sha256": LOG_SHA256,
            "error_headers_sha256": HEADERS_SHA256,
            "diagnostics_sha256": DIAGNOSTICS_SHA256,
            "errors": 287,
            "warnings": 361,
            "panic": 0,
            "exit": 1,
        },
        "scope": {
            "candidate_lines": [50000, 61671],
            "direct_producer_roots_only": True,
            "cascade_lines_modified": False,
            "excluded_structural_inverse_eta_base_cluster": [50000, 51801],
            "excluded_active_probe9_spans_by_exact_input": True,
            "excluded_probe10_midlate_spans_by_collision_audit": True,
            "quarantined_not_static_claims": [55005, 55820, 58786, 61203],
        },
        "source": source_shape,
        "result": result_shape,
        "repair_families": len(RULES),
        "repair_occurrences": sum(item["occurrences"] for item in rule_audit),
        "direct_diagnostics": len(diagnostic_map),
        "diagnostic_map": diagnostic_map,
        "rules": rule_audit,
        "selected_exact_probe9_lines": sorted(
            {header.line for rule in RULES for header in rule.headers}
        ),
        "foreign_anchor_collision_audit": collision_audit,
        "inverse_byte_equal": True,
        "trust": after_trust,
        "static_evidence": {
            "indicator_pointwise_add_requires_pi_add_apply": True,
            "indicator_pointwise_smul_requires_pi_smul_apply": True,
            "resolvent_clm_ascription_matches_active_sibling_fixes": [55079, 55108],
            "natural_stage_set_definition_is_indicator_set": True,
            "operator_coercion_is_visible_in_probe9_goals": [59585, 59589, 59606, 59618],
        },
        "execution": {
            "lean": False,
            "lake": False,
            "git_mutation": False,
            "network": False,
            "remote": False,
            "repository_source_mutation": False,
        },
    }
    args.output.write_bytes(result)
    args.audit.write_text(
        json.dumps(record, indent=2) + "\n", encoding="utf-8", newline="\n"
    )
    print(json.dumps(record, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
