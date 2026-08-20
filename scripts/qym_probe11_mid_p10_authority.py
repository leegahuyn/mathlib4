#!/usr/bin/env python3
"""Exact-P10 conditional repairs for thirteen independent QYM mid-file roots.

This byte-locked, exact-counted, reversible static transformer validates the
terminal Probe10 candidate and diagnostic authorities, audits span collisions
against the four active Probe10 component helpers, and emits a candidate only
under ``work/``.  It never invokes Lean/Lake/Git/the network and never mutates
a repository source.  Its output is activation-disabled pending a later
integrated CI probe.
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

SCHEMA = "qym-probe11-mid-conditional-static-v2-exact-probe10"
INPUT_SHA256 = "ef19b4f666bd7238164aec7795e10c3f802d9a3e49e5d5f617cc09d4cbe617dc"
INPUT_GIT_BLOB = "496c24e5a90d1f72c66bb03fcc9d3565a06f4b2e"
INPUT_BYTES = 2_923_612
INPUT_LF = 61_783
LOG_SHA256 = "0fa01861e0984e1e45107a46789d894f33d2bbd4a035d9dbaa29060956ab3ad2"
HEADERS_SHA256 = "b1130e19aa9ca16b044eeab07ebf762c0cb2bdfe46c0b7d242ef68b0c151a7a5"
DIAGNOSTICS_SHA256 = "b51f3cc940634dc1eba28003770ae750f8621c4452483f27fdf464188591c43a"

# Sealed after a deterministic bootstrap projection, then enforced in both
# directions.  Empty/zero placeholders are accepted only with --bootstrap-seal.
OUTPUT_SHA256 = "7a04c7758de3c47c7cc74c4359e2bee6b0364d2170c88fa022399bb48789b0b5"
OUTPUT_GIT_BLOB = "add4d5117086a8d597acb65ff70b02f7956de7b6"
OUTPUT_BYTES = 2_924_402
OUTPUT_LF = 61_800

PROBE10_HELPER_SHA256 = {
    "qym_probe10_earlytail_static.py":
        "5d7c848db8b8ec238bbdaad29bc5532ae0020f134846d16be064a78372c58434",
    "qym_probe10_midlate_static.py":
        "42d8f76c68b19aac520d15659c71d02db2e1beb397cfe0865bcdaf436e885be0",
    "qym_probe10_late_static.py":
        "d1c9aef94af3efac77ab5b9b87b2851adbc3eac3fcf7f18e5cc9695a61b7bccd",
    "qym_probe10_extendofnorm_instances.py":
        "b7942ba8d0ae94dd2827f5a59560a81a291482880c8716df299cc13dbac246bb",
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
        "actual_fixed_phase_stored_trace_extension_core_local_instances",
        "@[simp]\n"
        "theorem actualFixedPhaseStoredTraceExtension_core\n"
        "    (n : ℤ) (Y : ℝ)\n"
        "    (hBound : ActualFixedPhaseStoredTraceBounded n Y)\n"
        "    (u : InverseEtaFixedPhaseCore n) :\n"
        "    actualFixedPhaseStoredTraceExtension n Y (coreMap n u) =\n"
        "      actualFixedPhaseThreeCuspTraceToL2Linear n Y u := by\n"
        "  rcases hBound with ⟨C, hC⟩\n"
        "  simpa [actualFixedPhaseStoredTraceExtension] using\n"
        "    (LinearMap.extendOfNorm_eq\n"
        "      (f := actualFixedPhaseThreeCuspTraceToL2Linear n Y)\n"
        "      (e := coreMap n)\n"
        "      (denseRange_coreMap n) ⟨C, hC⟩ u)\n",
        "@[simp]\n"
        "theorem actualFixedPhaseStoredTraceExtension_core\n"
        "    (n : ℤ) (Y : ℝ)\n"
        "    (hBound : ActualFixedPhaseStoredTraceBounded n Y)\n"
        "    (u : InverseEtaFixedPhaseCore n) :\n"
        "    actualFixedPhaseStoredTraceExtension n Y (coreMap n u) =\n"
        "      actualFixedPhaseThreeCuspTraceToL2Linear n Y u := by\n"
        "  letI : Module ℂ (InverseEtaFixedPhaseCore n) :=\n"
        "    DefinitionOneSobolev.FixedPhaseGraphCompletion.fixedPhaseGraphCoreModule n\n"
        "  letI : AddCommGroup (InverseEtaFixedPhaseCore n) :=\n"
        "    DefinitionOneSobolev.FixedPhaseGraphCompletion.fixedPhaseGraphCoreAddCommGroup n\n"
        "  rcases hBound with ⟨C, hC⟩\n"
        "  exact LinearMap.extendOfNorm_eq (denseRange_coreMap n) ⟨C, hC⟩ u\n",
        (Header(
            36655,
            0,
            "(deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached",
        ),),
        "Install the core Module/AddCommGroup instances locally and use the exact extendOfNorm_eq API, matching the exit-zero precedent.",
    ),
    Rule(
        "actual_fixed_phase_stored_trace_extension_norm_le_local_instances",
        "theorem actualFixedPhaseStoredTraceExtension_norm_le\n"
        "    (n : ℤ) (Y : ℝ) (C : ℝ)\n"
        "    (hC : ∀ u : InverseEtaFixedPhaseCore n,\n"
        "      ‖actualFixedPhaseThreeCuspTraceToL2Linear n Y u‖ ≤\n"
        "        C * ‖coreMap n u‖)\n"
        "    (x : GraphSobolevCompletion n) :\n"
        "    ‖actualFixedPhaseStoredTraceExtension n Y x‖ ≤ C * ‖x‖ := by\n"
        "  simpa [actualFixedPhaseStoredTraceExtension] using\n"
        "    (LinearMap.norm_extendOfNorm_apply_le\n"
        "      (f := actualFixedPhaseThreeCuspTraceToL2Linear n Y)\n"
        "      (e := coreMap n)\n"
        "      (denseRange_coreMap n) C hC x)\n",
        "theorem actualFixedPhaseStoredTraceExtension_norm_le\n"
        "    (n : ℤ) (Y : ℝ) (C : ℝ)\n"
        "    (hC : ∀ u : InverseEtaFixedPhaseCore n,\n"
        "      ‖actualFixedPhaseThreeCuspTraceToL2Linear n Y u‖ ≤\n"
        "        C * ‖coreMap n u‖)\n"
        "    (x : GraphSobolevCompletion n) :\n"
        "    ‖actualFixedPhaseStoredTraceExtension n Y x‖ ≤ C * ‖x‖ := by\n"
        "  letI : Module ℂ (InverseEtaFixedPhaseCore n) :=\n"
        "    DefinitionOneSobolev.FixedPhaseGraphCompletion.fixedPhaseGraphCoreModule n\n"
        "  letI : AddCommGroup (InverseEtaFixedPhaseCore n) :=\n"
        "    DefinitionOneSobolev.FixedPhaseGraphCompletion.fixedPhaseGraphCoreAddCommGroup n\n"
        "  exact LinearMap.norm_extendOfNorm_apply_le\n"
        "    (denseRange_coreMap n) C hC x\n",
        (Header(
            36682,
            6,
            "(deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached",
        ),),
        "Install the missing local algebra instances and call norm_extendOfNorm_apply_le with its exact positional signature.",
    ),
    Rule(
        "actual_fixed_phase_stored_trace_extension_unique_local_instances",
        "theorem actualFixedPhaseStoredTraceExtension_unique\n"
        "    (n : ℤ) (Y : ℝ)\n"
        "    (hBound : ActualFixedPhaseStoredTraceBounded n Y)\n"
        "    (T : GraphSobolevCompletion n →L[ℂ]\n"
        "      ActualFixedPhaseThreeCuspBoundaryL2)\n"
        "    (hT : ExtendsActualFixedPhaseStoredTrace n Y T) :\n"
        "    actualFixedPhaseStoredTraceExtension n Y = T := by\n"
        "  rcases hBound with ⟨C, hC⟩\n"
        "  have hComp : T.toLinearMap.comp (coreMap n) =\n"
        "      actualFixedPhaseThreeCuspTraceToL2Linear n Y := by\n"
        "    ext u\n"
        "    exact hT u\n"
        "  simpa [actualFixedPhaseStoredTraceExtension] using\n"
        "    (LinearMap.extendOfNorm_unique\n"
        "      (f := actualFixedPhaseThreeCuspTraceToL2Linear n Y)\n"
        "      (e := coreMap n)\n"
        "      (denseRange_coreMap n) C hC T hComp)\n",
        "theorem actualFixedPhaseStoredTraceExtension_unique\n"
        "    (n : ℤ) (Y : ℝ)\n"
        "    (hBound : ActualFixedPhaseStoredTraceBounded n Y)\n"
        "    (T : GraphSobolevCompletion n →L[ℂ]\n"
        "      ActualFixedPhaseThreeCuspBoundaryL2)\n"
        "    (hT : ExtendsActualFixedPhaseStoredTrace n Y T) :\n"
        "    actualFixedPhaseStoredTraceExtension n Y = T := by\n"
        "  letI : Module ℂ (InverseEtaFixedPhaseCore n) :=\n"
        "    DefinitionOneSobolev.FixedPhaseGraphCompletion.fixedPhaseGraphCoreModule n\n"
        "  letI : AddCommGroup (InverseEtaFixedPhaseCore n) :=\n"
        "    DefinitionOneSobolev.FixedPhaseGraphCompletion.fixedPhaseGraphCoreAddCommGroup n\n"
        "  rcases hBound with ⟨C, hC⟩\n"
        "  have hComp : T.toLinearMap.comp (coreMap n) =\n"
        "      actualFixedPhaseThreeCuspTraceToL2Linear n Y := by\n"
        "    ext u\n"
        "    exact hT u\n"
        "  exact LinearMap.extendOfNorm_unique\n"
        "    (denseRange_coreMap n) C hC T hComp\n",
        (Header(
            36702,
            0,
            "(deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached",
        ),),
        "Install the missing local algebra instances and use the exact extendOfNorm_unique API after proving the composition identity.",
    ),
    Rule(
        "regular_stabilizer_map_bot_use_iff_as_term",
        "  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj,\n"
        "    Subgroup.map_eq_bot_iff_of_injective (MulAut.conj g).injective]\n",
        "  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj]\n"
        "  exact Subgroup.map_eq_bot_iff_of_injective\n"
        "    (MulAut.conj g).injective\n",
        (Header(37465, 4, "Tactic `rewrite` failed: Did not find an occurrence of the pattern"),),
        "After the stabilizer rewrite, consume the map-eq-bottom iff directly instead of asking rw to find one side inside an already-formed iff.",
    ),
    Rule(
        "literal_cusp_union_close_selected_curve_defeq",
        "  unfold gammaTwoCuspClassHorocycleBoundary activeTileCuspPart\n"
        "  rw [Set.inter_iUnion]\n",
        "  unfold gammaTwoCuspClassHorocycleBoundary activeTileCuspPart\n"
        "  rw [Set.inter_iUnion]\n"
        "  rfl\n",
        (Header(38459, 36, "unsolved goals"),),
        "Close the residual equality by delta-reducing the selected-horocycle curve to the same coset translate already displayed on the left.",
    ),
    Rule(
        "canonical_horocycle_normsq_expose_coordinates",
        "  · rw [Complex.normSq_apply]\n"
        "    simp only [canonicalHorocycleBase_re,\n"
        "      canonicalHorocycleBase_im, zero_mul, zero_add]\n"
        "    nlinarith [one_le_gammaTwoCuspLevel Y]\n",
        "  · rw [Complex.normSq_apply]\n"
        "    change 1 ≤ 0 * 0 +\n"
        "      gammaTwoCuspLevel Y * gammaTwoCuspLevel Y\n"
        "    nlinarith [one_le_gammaTwoCuspLevel Y]\n",
        (Header(38486, 4, "`simp` made no progress"),),
        "Expose the two literal coordinates with change; the existing nonlinear lower-bound argument then applies without fragile projection simp lemmas.",
    ),
    Rule(
        "fd_normsq_bridge_use_coerced_complex_coordinates",
        "  have hnorm :\n"
        "      1 ≤ z.re * z.re + z.im * z.im := by\n"
        "    simpa only [Complex.normSq_apply] using hz'.1\n",
        "  have hnorm :\n"
        "      1 ≤ z.re * z.re + z.im * z.im := by\n"
        "    change 1 ≤ (z : ℂ).re * (z : ℂ).re +\n"
        "      (z : ℂ).im * (z : ℂ).im\n"
        "    simpa only [Complex.normSq_apply] using hz'.1\n",
        (Header(38869, 4, "Type mismatch: After simplification, term"),),
        "State the local goal with the coerced Complex projections that Complex.normSq_apply actually produces.",
    ),
    Rule(
        "effective_union_witness_change_to_native_gamma_action",
        "  simpa only [gammaTwoEffectiveElement_smul] using hgammaU\n",
        "  change (gamma : SL(2, ℤ)) • u = z\n"
        "  exact hgammaU\n",
        (Header(39022, 2, "Type mismatch: After simplification, term"),),
        "Expose the native special-linear action expected by the stored equality instead of simplifying it back to the subgroup action.",
    ),
    Rule(
        "edge_endpoint_circular_arc_finish_negation_arithmetic",
        "  cases e <;>\n"
        "    simp [edgeParameterTransport, edgeEndpointSet,\n"
        "      Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.GammaTwoActualPolygonEdge.paired_second,\n"
        "      Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.modularTileEdgeEndpoints,\n"
        "      Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.GammaTwoModularTileEdge.parameterSign,\n"
        "      Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.GammaTwoModularTileEdge.paired]\n",
        "  cases e <;>\n"
        "    simp [edgeParameterTransport, edgeEndpointSet,\n"
        "      Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.GammaTwoActualPolygonEdge.paired_second,\n"
        "      Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.modularTileEdgeEndpoints,\n"
        "      Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.GammaTwoModularTileEdge.parameterSign,\n"
        "      Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.GammaTwoModularTileEdge.paired]\n"
        "  constructor\n"
        "  · rintro (h | h)\n"
        "    · exact Or.inr h\n"
        "    · exact Or.inl (by linarith)\n"
        "  · rintro (h | h)\n"
        "    · exact Or.inr (by linarith)\n"
        "    · exact Or.inl h\n",
        (Header(39507, 31, "unsolved goals"),),
        "The constructor split leaves only the circular-arc equivalence; discharge its two sign reversals explicitly.",
    ),
    Rule(
        "twisted_difference_zero_split_distance_and_use_increment_zero",
        "    widthTwoTwistedDifferenceQuotient tau (0 : ℝ → ℂ) = 0 := by\n"
        "  funext p\n"
        "  simp [widthTwoTwistedDifferenceQuotient]\n",
        "    widthTwoTwistedDifferenceQuotient tau (0 : ℝ → ℂ) = 0 := by\n"
        "  funext p\n"
        "  by_cases hp : widthTwoCircularDistance p.1 p.2 = 0\n"
        "  · simp [widthTwoTwistedDifferenceQuotient, hp]\n"
        "  · simp [widthTwoTwistedDifferenceQuotient, hp,\n"
        "      widthTwoTwistedIncrement_zero]\n",
        (Header(40570, 61, "unsolved goals"),),
        "Split the defining distance test first, then invoke the producer theorem for the zero twisted increment in the nonzero branch.",
    ),
    Rule(
        "twisted_difference_add_normalize_commutative_ring",
        "  · simp only [widthTwoTwistedDifferenceQuotient, hp, if_false,\n"
        "      Pi.add_apply, widthTwoTwistedIncrement_add]\n"
        "    ring\n",
        "  · simp only [widthTwoTwistedDifferenceQuotient, hp, if_false,\n"
        "      Pi.add_apply, widthTwoTwistedIncrement_add]\n"
        "    ring_nf\n",
        (Header(40582, 2, "unsolved goals"),),
        "Use the compiler-suggested ring normalizer after the quotient and pointwise-add producers have been exposed.",
    ),
    Rule(
        "twisted_difference_smul_normalize_commutative_ring",
        "  · simp only [widthTwoTwistedDifferenceQuotient, hp, if_false,\n"
        "      Pi.smul_apply, smul_eq_mul, widthTwoTwistedIncrement_smul]\n"
        "    ring\n",
        "  · simp only [widthTwoTwistedDifferenceQuotient, hp, if_false,\n"
        "      Pi.smul_apply, smul_eq_mul, widthTwoTwistedIncrement_smul]\n"
        "    ring_nf\n",
        (Header(40593, 2, "unsolved goals"),),
        "Use the compiler-suggested ring normalizer after the quotient and pointwise-smul producers have been exposed.",
    ),
    Rule(
        "eta_continuousAt_comp_current_signature",
        "      (ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet\n"
        "        (actualFixedPhaseCuspHorocyclePoint kappa Y x).2).continuousAt.comp x\n"
        "          hcoe.continuousAt\n",
        "      (ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet\n"
        "        (actualFixedPhaseCuspHorocyclePoint kappa Y x).2).continuousAt.comp\n"
        "          hcoe.continuousAt\n",
        (Header(41229, 76, "Application type mismatch: The argument"),),
        "Use the current ContinuousAt.comp signature, whose inner continuity proof is the next argument and which no longer takes the point explicitly.",
    ),
)


def sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def git_blob(raw: bytes) -> str:
    prefix = f"blob {len(raw)}\0".encode("ascii")
    return hashlib.sha1(prefix + raw).hexdigest()


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
        "maxHeartbeats_zero": len(
            re.findall(r"set_option\s+maxHeartbeats\s+0\b", text)
        ),
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


def check_shape(
    actual: dict[str, object], expected: dict[str, object], *, unsealed: bool = False
) -> None:
    if unsealed:
        structural = {k: expected[k] for k in ("cr", "nul", "bom", "terminal_lf")}
        for key, value in structural.items():
            if actual[key] != value:
                raise RuntimeError(f"unsealed structural shape mismatch: {key}")
        return
    if actual != expected:
        raise RuntimeError(f"shape mismatch: {actual} != {expected}")


def parse_diagnostics(raw: bytes) -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    for line in raw.decode("utf-8", errors="strict").splitlines():
        rows.append(json.loads(line))
    return rows


def verify_authority(
    log_raw: bytes, header_raw: bytes, diagnostics_raw: bytes
) -> list[dict[str, object]]:
    if sha256(log_raw) != LOG_SHA256:
        raise RuntimeError("Probe10 log identity mismatch")
    if sha256(header_raw) != HEADERS_SHA256:
        raise RuntimeError("Probe10 error-header identity mismatch")
    if sha256(diagnostics_raw) != DIAGNOSTICS_SHA256:
        raise RuntimeError("Probe10 diagnostics identity mismatch")

    header_lines = header_raw.decode("utf-8", errors="strict").splitlines()
    rows = parse_diagnostics(diagnostics_raw)
    if len(header_lines) != 255:
        raise RuntimeError(f"expected 255 exact error headers, got {len(header_lines)}")
    if sum(row.get("severity") == "error" for row in rows) != 255:
        raise RuntimeError("diagnostic error count is not 255")
    if sum(row.get("severity") == "warning" for row in rows) != 343:
        raise RuntimeError("diagnostic warning count is not 343")

    verified: list[dict[str, object]] = []
    for rule in RULES:
        for header in rule.headers:
            code = f"\\({re.escape(header.code)}\\)" if header.code else ""
            pattern = re.compile(
                rf"^PrimalitySheafVerification/QYM\.lean:{header.line}:"
                rf"{header.column}: error{code}: {re.escape(header.message)}"
            )
            matches = [line for line in header_lines if pattern.match(line)]
            diag_matches = [
                row for row in rows
                if row.get("severity") == "error"
                and row.get("line") == header.line
                and row.get("column") == header.column
                and row.get("code") == header.code
                and str(row.get("message", "")).startswith(header.message)
            ]
            if len(matches) != 1 or len(diag_matches) != 1:
                raise RuntimeError(
                    f"{rule.label}: authority mapping mismatch at "
                    f"{header.line}:{header.column}"
                )
            verified.append({
                "rule": rule.label,
                "line": header.line,
                "column": header.column,
                "code": header.code,
                "message": header.message,
                "kind": "direct",
            })
    return verified


def spans(text: str, needle: str) -> list[tuple[int, int]]:
    result: list[tuple[int, int]] = []
    start = 0
    while True:
        offset = text.find(needle, start)
        if offset < 0:
            return result
        result.append((offset, offset + len(needle)))
        start = offset + 1


def load_helper(path: Path) -> ModuleType:
    name = "_qym_probe11_foreign_" + hashlib.sha256(
        str(path.resolve()).encode("utf-8")
    ).hexdigest()
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot import helper: {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def audit_probe10_collisions(
    base: str, helper_paths: list[Path], *, inverse: bool
) -> dict[str, object]:
    by_name = {path.name: path for path in helper_paths}
    if set(by_name) != set(PROBE10_HELPER_SHA256):
        raise RuntimeError("foreign helper set is not the exact four Probe10 components")

    own_needle = {rule.label: (rule.new if inverse else rule.old) for rule in RULES}
    own_spans: list[tuple[int, int, str]] = []
    for label, needle in own_needle.items():
        found = spans(base, needle)
        if len(found) != 1:
            raise RuntimeError(f"own span count mismatch during collision audit: {label}")
        own_spans.extend((start, end, label) for start, end in found)

    identities: dict[str, str] = {}
    overlaps: list[dict[str, object]] = []
    exact_anchor_equalities: list[dict[str, str]] = []
    foreign_families = 0
    for name, expected_sha in PROBE10_HELPER_SHA256.items():
        path = by_name[name]
        digest = sha256(path.read_bytes())
        if digest != expected_sha:
            raise RuntimeError(f"Probe10 helper identity mismatch: {name}")
        identities[name] = digest
        module = load_helper(path)
        foreign_rules = getattr(module, "RULES", None)
        if foreign_rules is None:
            raise RuntimeError(f"Probe10 helper has no RULES: {name}")
        for foreign in foreign_rules:
            foreign_families += 1
            old = getattr(foreign, "old")
            new = getattr(foreign, "new")
            foreign_label = getattr(foreign, "label")
            expected_count = getattr(foreign, "occurrences", 1)
            # Exact Probe10 already has every component's forward replacement
            # active.  Those new anchors must remain exact in both directions;
            # only the Probe11 anchor direction changes.
            active = new
            found = spans(base, active)
            if len(found) != expected_count:
                raise RuntimeError(
                    f"Probe10 active span count mismatch: {name}:{foreign_label}:"
                    f" {len(found)} != {expected_count}"
                )
            for own in RULES:
                for own_variant_name, own_variant in (("old", own.old), ("new", own.new)):
                    for foreign_variant_name, foreign_variant in (("old", old), ("new", new)):
                        if own_variant == foreign_variant:
                            exact_anchor_equalities.append({
                                "own": own.label,
                                "own_variant": own_variant_name,
                                "foreign_helper": name,
                                "foreign_rule": foreign_label,
                                "foreign_variant": foreign_variant_name,
                            })
            for fstart, fend in found:
                for ostart, oend, own_label in own_spans:
                    if max(fstart, ostart) < min(fend, oend):
                        overlaps.append({
                            "own": own_label,
                            "foreign_helper": name,
                            "foreign_rule": foreign_label,
                            "own_span": [ostart, oend],
                            "foreign_span": [fstart, fend],
                        })
    if exact_anchor_equalities or overlaps:
        raise RuntimeError(
            f"Probe10 collision: equalities={exact_anchor_equalities}, "
            f"overlaps={overlaps}"
        )
    return {
        "helper_sha256": identities,
        "foreign_rule_families_checked": foreign_families,
        "own_spans_checked": len(own_spans),
        "exact_anchor_equalities": exact_anchor_equalities,
        "span_overlaps": overlaps,
    }


def apply_rules(
    text: str, inverse: bool = False
) -> tuple[str, list[dict[str, object]]]:
    audits: list[dict[str, object]] = []
    ordered = tuple(reversed(RULES)) if inverse else RULES
    for rule in ordered:
        old, new = (rule.new, rule.old) if inverse else (rule.old, rule.new)
        count = text.count(old)
        if count != rule.occurrences:
            raise RuntimeError(
                f"{rule.label}: exact anchor count {count}, expected {rule.occurrences}"
            )
        text = text.replace(old, new)
        audits.append({
            "label": rule.label,
            "direction": "inverse" if inverse else "forward",
            "occurrences": count,
            "headers": [header.__dict__ for header in rule.headers],
            "rationale": rule.rationale,
        })
    return text, audits


transform = apply_rules


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--probe10-log", type=Path, required=True)
    parser.add_argument("--probe10-error-headers", type=Path, required=True)
    parser.add_argument("--probe10-diagnostics", type=Path, required=True)
    parser.add_argument("--probe10-helper", type=Path, action="append", required=True)
    parser.add_argument("--audit", type=Path, required=True)
    parser.add_argument("--mode", choices=("forward", "inverse"), default="forward")
    parser.add_argument("--bootstrap-seal", action="store_true")
    args = parser.parse_args()
    inverse = args.mode == "inverse"

    source = args.input.read_bytes()
    source_shape = shape(source)
    check_shape(
        source_shape,
        output_expected() if inverse else input_expected(),
        unsealed=args.bootstrap_seal and inverse,
    )
    diagnostics = verify_authority(
        args.probe10_log.read_bytes(),
        args.probe10_error_headers.read_bytes(),
        args.probe10_diagnostics.read_bytes(),
    )
    source_text = source.decode("utf-8", errors="strict")
    collision = audit_probe10_collisions(
        source_text, args.probe10_helper, inverse=inverse
    )
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
    restored_text, _ = apply_rules(result_text, inverse=not inverse)
    if restored_text.encode("utf-8") != source:
        raise RuntimeError("opposite transform did not restore source byte-for-byte")
    if args.output.exists() or args.audit.exists():
        raise RuntimeError("refusing to overwrite output or audit")

    record = {
        "schema": SCHEMA,
        "status": "STATIC_PASS_EXACT_PROBE10_AUTHORITY_NOT_LEAN_EXECUTED",
        "activation": False,
        "promotion": False,
        "mode": args.mode,
        "authority": {
            "probe10_run_id": 31973408809,
            "probe10_job_id": 95229227905,
            "probe10_head_sha": "0957f9b925663bc78b76c7207084fb6199eb60de",
            "probe10_trigger_sha": "0957f9b925663bc78b76c7207084fb6199eb60de",
            "probe10_result_sha256": "0a908f0ae2bae582285d3d48c5ccb30829c2225af2b397b5ffd1a499798d279d",
            "artifact_id": 9270510078,
            "artifact_name": "qym-repair-probe10-integrated-0957f9b925663bc78b76c7207084fb6199eb60de-attempt1",
            "artifact_api_size": 10487379,
            "artifact_zip_sha256": "0b2e4c1ba61974967f3a79bc1d32f7480fa1bdc484cfe82d763b5ee03bf4f101",
            "artifact_digest": "sha256:0b2e4c1ba61974967f3a79bc1d32f7480fa1bdc484cfe82d763b5ee03bf4f101",
            "candidate_sha256": INPUT_SHA256,
            "candidate_git_blob": INPUT_GIT_BLOB,
            "candidate_bytes": INPUT_BYTES,
            "candidate_lf": INPUT_LF,
            "log_sha256": LOG_SHA256,
            "error_headers_sha256": HEADERS_SHA256,
            "diagnostics_sha256": DIAGNOSTICS_SHA256,
            "errors": 255,
            "warnings": 343,
            "panic": 0,
            "exit": 1,
        },
        "scope": {
            "candidate_lines": [30000, 49999],
            "direct_producer_api_parser_roots_only": True,
            "cascade_lines_modified": False,
            "excluded_probe10_helpers": PROBE10_HELPER_SHA256,
            "probe10_active_forward_spans_excluded": True,
            "probe10_active_span_anchor_and_overlap_with_probe11": False,
            "downstream_cascades_modified": False,
            "extend_of_norm_cluster_downstream_cascade_lines_excluded": [
                36687, 36762, 36821, 37041, 37054, 37090, 37137, 37178,
                37225, 37252,
            ],
            "new_roots_added": 3,
            "surviving_reanchored_roots": 10,
        },
        "source": source_shape,
        "result": result_shape,
        "repair_families": len(RULES),
        "repair_occurrences": sum(item["occurrences"] for item in rule_audit),
        "direct_diagnostics": len(diagnostics),
        "diagnostic_map": diagnostics,
        "rules": rule_audit,
        "selected_exact_probe10_lines": sorted(
            {header.line for rule in RULES for header in rule.headers}
        ),
        "probe10_collision_audit": collision,
        "inverse_byte_equal": True,
        "trust": after_trust,
        "static_evidence": {
            "compiler_suggested_ring_nf_lines": [40570, 40582, 40593],
            "continuousAt_comp_argument_error_identifies_current_signature": True,
            "coercion_only_mismatches_exposed_with_change": [38486, 38869, 39022],
            "extend_of_norm_exact_api_precedent": {
                "path": "work/fa-e4-strategy-a2-calc-consolidation/Mock2_FunctionalAnalysis-candidate.lean",
                "lines": [36570, 36588],
                "exit": 0,
                "local_instances": ["Module", "AddCommGroup"],
                "apis": [
                    "LinearMap.extendOfNorm_eq",
                    "LinearMap.norm_extendOfNorm_apply_le",
                    "LinearMap.extendOfNorm_unique",
                ],
            },
        },
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
    args.audit.write_text(
        json.dumps(record, indent=2) + "\n", encoding="utf-8", newline="\n"
    )
    print(json.dumps(record, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

