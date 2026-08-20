#!/usr/bin/env python3
"""Activation-disabled exact-P14 reanchor of the frozen cc579 QYM repairs.

The four producer/cascade diagnostics survive exact terminal Probe14 uniformly.
Their overlaps with the consumed Probe12 NEW anchors remain declared exactly,
and all active Probe14 components are checked in their already-applied state.

No Lean/Lake/install/Git/network/remote/canonical-source action is performed.
Activation is deferred until an exact terminal Probe15 package exists.
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

SCHEMA = "qym-probe15-contdiff-exact-p14-reanchored-v1"
ACTIVATION = False

INPUT_SHA256 = "e8ac0ba15f35c88792552a0d55d789c222d360a10d30c3cedb0ce0a8dfb879b7"
INPUT_GIT_BLOB = "49b71abd253e0b1292ecacd9ebc984fa9ea3d9de"
INPUT_BYTES = 2_940_390
INPUT_LF = 62_158
LOG_SHA256 = "250bbac608414a347525dffcdd2c54efba07ba1aac1f4b5e6a26cfe5109d5efa"
HEADERS_SHA256 = "42934d8e7289d6b30dba316139441719b748df8b31b19efc1def3e10af9b9dfc"
DIAGNOSTICS_SHA256 = "4eba0f0371689b45b0e5a554e14f788cc128f51ff9a015fe5ba2b738773e9e94"

OUTPUT_SHA256 = "29c4ff78d67059eaebd6acc2990b9130225728f84d7c33b339ca1fc6180abbfb"
OUTPUT_GIT_BLOB = "e4566869097f785ed1f91c63ceee1756c2e93fee"
OUTPUT_BYTES = 2_940_490
OUTPUT_LF = 62_161

MATHLIB_CONTDIFF_OPERATIONS_SHA256 = (
    "3ba61e517d6162ed2fd043f1deb48d80567c2470991d9b3ae99e7be1176eb1c2"
)
FA_DEPENDENCY_SHA256 = (
    "1c3d12594a3e8b14f9cf7b7294da7c29221758c72d00a596215198f7623fad8c"
)


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
    kind: str = "direct"


@dataclass(frozen=True)
class Rule:
    label: str
    old: str
    new: str
    headers: tuple[Header, ...]
    rationale: str
    evidence: str
    consumed_rule: str
    occurrences: int = 1


RULES: tuple[Rule, ...] = (
    Rule(
        "cusp_trace_covariance_normalize_nil_target_index",
        "  rw [actualFixedPhaseNamedCuspTraceRepresentative,\n"
        "    actualFixedPhaseCuspHorocyclePoint_add_two]\n"
        "  change\n"
        "    ((u : SmoothQuotientCompactFunction) : ℍ → ℂ)\n"
        "        ((((actualFixedPhaseCuspDeckTranslation kappa : GammaTwo) :\n"
        "          SL(2, ℤ))) •\n"
        "          actualFixedPhaseCuspHorocyclePoint kappa Y x) =\n"
        "      (inverseEtaPaperOrbitMultiplier GammaTwo n).factor\n"
        "          (actualFixedPhaseCuspDeckTranslation kappa)\n"
        "          (actualFixedPhaseCuspHorocyclePoint kappa Y x) *\n"
        "        ((u : SmoothQuotientCompactFunction) : ℍ → ℂ)\n"
        "          (actualFixedPhaseCuspHorocyclePoint kappa Y x)\n"
        "  simpa only [FixedPhaseDifferentialWord.targetIndex_nil,\n"
        "    FixedPhaseDifferentialWord.eval_nil_apply,\n"
        "    InverseEtaFixedPhaseCore.toSmoothQuotientCompactFunction] using\n"
        "    (u.2 FixedPhaseDifferentialWord.nil)\n"
        "      (actualFixedPhaseCuspDeckTranslation kappa)\n"
        "      (actualFixedPhaseCuspHorocyclePoint kappa Y x)\n",
        "  rw [actualFixedPhaseNamedCuspTraceRepresentative,\n"
        "    actualFixedPhaseCuspHorocyclePoint_add_two]\n"
        "  change\n"
        "    ((u : SmoothQuotientCompactFunction) : ℍ → ℂ)\n"
        "        ((((actualFixedPhaseCuspDeckTranslation kappa : GammaTwo) :\n"
        "          SL(2, ℤ))) •\n"
        "          actualFixedPhaseCuspHorocyclePoint kappa Y x) =\n"
        "      (inverseEtaPaperOrbitMultiplier GammaTwo n).factor\n"
        "          (actualFixedPhaseCuspDeckTranslation kappa)\n"
        "          (actualFixedPhaseCuspHorocyclePoint kappa Y x) *\n"
        "        ((u : SmoothQuotientCompactFunction) : ℍ → ℂ)\n"
        "          (actualFixedPhaseCuspHorocyclePoint kappa Y x)\n"
        "  have hcov :=\n"
        "    (u.2 FixedPhaseDifferentialWord.nil)\n"
        "      (actualFixedPhaseCuspDeckTranslation kappa)\n"
        "      (actualFixedPhaseCuspHorocyclePoint kappa Y x)\n"
        "  simpa [FixedPhaseDifferentialWord.targetIndex,\n"
        "    FixedPhaseDifferentialWord.eval_nil_apply,\n"
        "    InverseEtaFixedPhaseCore.toSmoothQuotientCompactFunction] using hcov\n",
        (Header(41426, 2, "Type mismatch: After simplification, term"),),
        "Name the stored covariance and unfold targetIndex instead of relying on the failed restricted simplifier normalization.",
        "The FA dependency's diagnostic-free nil-word covariance uses an ordinary simpa at lines 17653-17672; targetIndex is definitionally n + displacement.",
        "cusp_trace_covariance_expose_sl2_action",
    ),
    Rule(
        "cusp_curve_contdiff_real_scalar_complex_quotient",
        "  simp only [actualFixedPhaseCuspHorocyclePoint,\n"
        "    actualFixedPhaseHorizontalHorocyclePoint,\n"
        "    UpperHalfPlane.coe_specialLinearGroup_apply]\n"
        "  apply ContDiff.div\n"
        "  · fun_prop\n"
        "  · fun_prop\n"
        "  · exact hden\n",
        "  simp only [actualFixedPhaseCuspHorocyclePoint,\n"
        "    actualFixedPhaseHorizontalHorocyclePoint,\n"
        "    UpperHalfPlane.coe_specialLinearGroup_apply]\n"
        "  rw [div_eq_mul_inv]\n"
        "  apply ContDiff.mul\n"
        "  · fun_prop\n"
        "  · apply ContDiff.inv\n"
        "    · fun_prop\n"
        "    · exact hden\n",
        (Header(41483, 2, "Tactic `apply` failed: could not unify the conclusion of `@ContDiff.div`"),),
        "Rewrite division as multiplication by inverse so the real-smooth domain and complex NormedAlgebra codomain use the correct APIs.",
        "Pinned Mathlib Operations.lean lines 430-463 and 782-813: ContDiff.mul targets a NormedAlgebra and ContDiff.inv targets a NormedField/NormedAlgebra; ContDiff.div remains restricted to E→scalar.",
        "cusp_curve_contdiff_apply_division_producer",
    ),
    Rule(
        "cusp_trace_contdiff_reduce_upperlift_composition",
        "  change ContDiff ℝ ∞\n"
        "    (fun x : ℝ =>\n"
        "      (u : SmoothQuotientCompactFunction)\n"
        "        (actualFixedPhaseCuspHorocyclePoint kappa Y x))\n"
        "  exact hcomp\n",
        "  change ContDiff ℝ ∞\n"
        "    (fun x : ℝ =>\n"
        "      (u : SmoothQuotientCompactFunction)\n"
        "        (actualFixedPhaseCuspHorocyclePoint kappa Y x))\n"
        "  simpa only [Function.comp_apply, upperLift_apply] using hcomp\n",
        (Header(41507, 2, "Type mismatch"),),
        "Beta-reduce the composition and apply the exact upperLift-on-upper-half-plane coercion theorem.",
        "The diagnostic differs only between upperLift u ∘ coe(curve) and direct u(curve); upperLift_apply is the exact dependency theorem.",
        "cusp_trace_contdiff_change_coercion_function",
    ),
    Rule(
        "smooth_boundary_use_current_hhalf_namespace",
        "theorem actualFixedPhaseNamedCuspAmbientCoordinate_contDiff\n"
        "    (kappa : Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.GammaTwoCusp) (Y : ℝ) :\n"
        "    ContDiff ℝ ∞\n"
        "      (actualFixedPhaseNamedCuspAmbientCoordinate kappa Y) := by\n"
        "  change ContDiff ℝ ∞\n"
        "    (fun x : ℝ =>\n"
        "      ((QYM.FullCertification.P2ActualFixedPhaseCuspTraceGraphExtension.actualFixedPhaseCuspHorocyclePoint\n"
        "        kappa Y x : ℍ) : ℂ))\n"
        "  exact\n"
        "    QYM.FullCertification.P2ActualFixedPhaseCuspTraceGraphExtension.actualFixedPhaseCuspHorocyclePoint_coe_contDiff\n"
        "      kappa Y\n",
        "theorem actualFixedPhaseNamedCuspAmbientCoordinate_contDiff\n"
        "    (kappa : Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.GammaTwoCusp) (Y : ℝ) :\n"
        "    ContDiff ℝ ∞\n"
        "      (actualFixedPhaseNamedCuspAmbientCoordinate kappa Y) := by\n"
        "  change ContDiff ℝ ∞\n"
        "    (fun x : ℝ =>\n"
        "      ((QYM.FullCertification.P2ActualFixedPhaseCuspTraceGraphExtension.actualFixedPhaseCuspHorocyclePoint\n"
        "        kappa Y x : ℍ) : ℂ))\n"
        "  exact\n"
        "    QYM.FullCertification.P2ClassicalHhalfTraceExtension.actualFixedPhaseCuspHorocyclePoint_coe_contDiff\n"
        "      kappa Y\n",
        (
            Header(
                42416,
                4,
                "Unknown identifier `QYM.FullCertification.P2ActualFixedPhaseCuspTraceGraphExtension.actualFixedPhaseCuspHorocyclePoint_coe_contDiff`",
                "lean.unknownIdentifier",
                "cascade",
            ),
        ),
        "Qualify the producer theorem by the namespace in which it is actually declared.",
        "Exact P13 opens namespace P2ClassicalHhalfTraceExtension at line 40507 and declares the producer at lines 41454-41475.",
        "smooth_boundary_reuse_certified_cusp_curve_contdiff",
    ),
)


OWNER_NAME = "p12_36k42k"
OWNER_HELPER = (
    "qym-probe12-36k42k-p11-reanchored/"
    "qym_probe12_36k42k_p11_reanchored.py"
)
OWNER_SHA256 = "5bd02f57232ac30c336b3e13574b7cba4dc4b0998f159e3fdebd41ed6354a365"

P14_HELPERS: tuple[tuple[str, str, str], ...] = (
    ("frontier", "qym-probe14-frontier-p13-conditional/qym_probe14_frontier_p13_conditional.py", "1118d53e64698cfe4d41da84d0a4450ad80efb4a0409b1eace0992abdfe20929"),
    ("prep", "qym-probe14-30k47k-p13-reanchored/qym_probe14_30k47k_p13_reanchored.py", "671f909e011eb3a18e402c33bd4df30bcc7aa098bf928ecbf629aa8a09028686"),
    ("tail", "qym-probe14-tail-prep-p13-static/qym_probe14_tail_prep_p13_static.py", "acd2cefb1db2b250558a362777b5e31c26fdb4dcfb23a29b4ff81f1a4c835412"),
    ("producer", "qym-probe14-producer-timeouts-p13-static/qym_probe14_producer_timeouts_p13_static.py", "65a610e3dd278f084fb5f24285143f798685fd858efa9d8c92a589442a725cc0"),
    ("gl", "qym-probe14-gl-action-p13-sequenced/qym_probe14_gl_action_p13_sequenced.py", "8a152cc89f8994eb5ab41adc21f17821e193056ae60e5e1bdc7aed75f669943e"),
)


def shape(raw: bytes) -> dict[str, object]:
    raw.decode("utf-8", errors="strict")
    return {
        "sha256": sha256(raw), "git_blob": git_blob(raw), "bytes": len(raw),
        "lf": raw.count(b"\n"), "cr": b"\r" in raw, "nul": b"\0" in raw,
        "bom": raw.startswith(b"\xef\xbb\xbf"), "terminal_lf": raw.endswith(b"\n"),
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


def expected_input() -> dict[str, object]:
    return {"sha256": INPUT_SHA256, "git_blob": INPUT_GIT_BLOB,
            "bytes": INPUT_BYTES, "lf": INPUT_LF, "cr": False, "nul": False,
            "bom": False, "terminal_lf": True}


def expected_output() -> dict[str, object]:
    return {"sha256": OUTPUT_SHA256, "git_blob": OUTPUT_GIT_BLOB,
            "bytes": OUTPUT_BYTES, "lf": OUTPUT_LF, "cr": False, "nul": False,
            "bom": False, "terminal_lf": True}


def unsealed() -> bool:
    return not OUTPUT_SHA256 and not OUTPUT_GIT_BLOB and OUTPUT_BYTES == 0 and OUTPUT_LF == 0


def check_shape(actual: dict[str, object], expected: dict[str, object], bootstrap: bool) -> None:
    keys = ("cr", "nul", "bom", "terminal_lf") if bootstrap else tuple(expected)
    if any(actual[key] != expected[key] for key in keys):
        raise RuntimeError(f"shape mismatch: {actual} != {expected}")


def spans(text: str, needle: str) -> list[tuple[int, int]]:
    out: list[tuple[int, int]] = []
    start = 0
    while True:
        found = text.find(needle, start)
        if found < 0:
            return out
        out.append((found, found + len(needle)))
        start = found + 1


def load_module(name: str, relative: str, wanted_sha: str) -> ModuleType:
    path = Path(__file__).resolve().parent.parent / relative
    raw = path.read_bytes()
    if sha256(raw) != wanted_sha:
        raise RuntimeError(f"helper identity mismatch: {name}")
    module_name = "_qym_probe15_contdiff_p14_" + name
    spec = importlib.util.spec_from_file_location(module_name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot import helper: {name}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[module_name] = module
    spec.loader.exec_module(module)
    return module


def verify_authority(log: bytes, headers: bytes, diagnostics: bytes) -> list[dict[str, object]]:
    for label, raw, wanted in (("log", log, LOG_SHA256), ("headers", headers, HEADERS_SHA256),
                               ("diagnostics", diagnostics, DIAGNOSTICS_SHA256)):
        if sha256(raw) != wanted:
            raise RuntimeError(f"Probe14 {label} identity mismatch")
    hs = headers.decode("utf-8").splitlines()
    rows = [json.loads(line) for line in diagnostics.decode("utf-8").splitlines()]
    if len(hs) != 124 or sum(row.get("severity") == "error" for row in rows) != 124:
        raise RuntimeError("Probe14 error count mismatch")
    mapped: list[dict[str, object]] = []
    for rule in RULES:
        for header in rule.headers:
            prefix = (f"PrimalitySheafVerification/QYM.lean:{header.line}:{header.column}: error"
                      + (f"({header.code})" if header.code else "") + f": {header.message}")
            hm = [line for line in hs if line.startswith(prefix)]
            dm = [row for row in rows if row.get("severity") == "error"
                  and row.get("line") == header.line and row.get("column") == header.column
                  and row.get("code") == header.code
                  and str(row.get("message", "")).startswith(header.message)]
            if len(hm) != 1 or len(dm) != 1:
                raise RuntimeError(f"diagnostic mismatch: {rule.label}")
            mapped.append({"rule": rule.label, **header.__dict__})
    return mapped


def transform(text: str, inverse: bool = False) -> tuple[str, list[dict[str, object]]]:
    records: list[dict[str, object]] = []
    for rule in (tuple(reversed(RULES)) if inverse else RULES):
        old, new = (rule.new, rule.old) if inverse else (rule.old, rule.new)
        count = text.count(old)
        if count != rule.occurrences:
            raise RuntimeError(f"anchor count: {rule.label}: {count}")
        if text.count(new) != old.count(new) * count:
            raise RuntimeError(f"destination collision: {rule.label}")
        text = text.replace(old, new)
        records.append({"label": rule.label, "direction": "inverse" if inverse else "forward",
                        "occurrences": count, "headers": [h.__dict__ for h in rule.headers],
                        "rationale": rule.rationale, "evidence": rule.evidence,
                        "consumed_owner": OWNER_NAME, "consumed_rule": rule.consumed_rule,
                        "consumed_relation": "own_old_equals_consumed_new"})
    return text, records


apply_rules = transform


def collision_audit(base: str) -> dict[str, object]:
    own: list[tuple[int, int, str, int]] = []
    for rule in RULES:
        found = spans(base, rule.old)
        if len(found) != 1 or base.count(rule.new) != rule.old.count(rule.new):
            raise RuntimeError(f"active anchor mismatch: {rule.label}")
        start, end = found[0]
        own.append((start, end, rule.label, base.count("\n", 0, start) + 1))
    ordered = sorted(own)
    if any(a[1] > b[0] for a, b in zip(ordered, ordered[1:])):
        raise RuntimeError("own overlap")

    owner = load_module(OWNER_NAME, OWNER_HELPER, OWNER_SHA256)
    owner_rules = {rule.label: rule for rule in owner.RULES}
    declared: list[dict[str, object]] = []
    for start, end, label, line in own:
        rule = next(item for item in RULES if item.label == label)
        foreign = owner_rules.get(rule.consumed_rule)
        if foreign is None or rule.old != foreign.new or spans(base, foreign.new) != [(start, end)]:
            raise RuntimeError(f"consumed NEW anchor mismatch: {label}")
        declared.append({"own_rule": label, "own_line": line, "foreign_owner": OWNER_NAME,
                         "foreign_rule": foreign.label, "foreign_variant": "new",
                         "relation": "own_old_equals_consumed_new"})

    p14_identities: dict[str, str] = {}
    p14_overlaps: list[dict[str, object]] = []
    pairwise: list[dict[str, object]] = []
    own_forward, _ = transform(base, False)
    for name, relative, wanted_sha in P14_HELPERS:
        module = load_module("p14_" + name, relative, wanted_sha)
        p14_identities[name] = wanted_sha
        for foreign in module.RULES:
            for variant, anchor in (("old", foreign.old), ("new", foreign.new)):
                for fs, fe in spans(base, anchor):
                    for os, oe, label, _ in own:
                        if max(fs, os) < min(fe, oe):
                            p14_overlaps.append({"own": label, "helper": name,
                                                 "foreign": foreign.label, "variant": variant})
        foreign_inverse, _ = module.transform(base, True)
        foreign_restored, _ = module.transform(foreign_inverse, False)
        if foreign_restored != base:
            raise RuntimeError(f"P14 applied-state inverse mismatch: {name}")
        foreign_inverse_then_own, _ = transform(foreign_inverse, False)
        own_then_foreign_inverse, _ = module.transform(own_forward, True)
        if foreign_inverse_then_own != own_then_foreign_inverse:
            raise RuntimeError(f"P14 pairwise order mismatch: {name}")
        pairwise.append({"helper": name, "already_applied": True,
                         "inverse_forward_exact_p14": True,
                         "inverse_commutes_with_own_forward": True})
    if p14_overlaps:
        raise RuntimeError(f"P14 collision: {p14_overlaps}")
    return {"declared_consumed_new_anchor_overlaps": declared,
            "declared_overlap_count": len(declared), "undeclared_overlap_count": 0,
            "probe14_helper_sha256": p14_identities, "probe14_overlap_count": 0,
            "own_overlap_count": 0, "probe14_pairwise_applied_state": pairwise}


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--probe14-log", type=Path, required=True)
    parser.add_argument("--probe14-error-headers", type=Path, required=True)
    parser.add_argument("--probe14-diagnostics", type=Path, required=True)
    parser.add_argument("--audit", type=Path, required=True)
    parser.add_argument("--mode", choices=("forward", "inverse"), default="forward")
    parser.add_argument("--bootstrap-seal", action="store_true")
    args = parser.parse_args()
    inverse = args.mode == "inverse"
    if args.bootstrap_seal != unsealed():
        raise RuntimeError("bootstrap/seal state mismatch")
    raw = args.input.read_bytes()
    check_shape(shape(raw), expected_output() if inverse else expected_input(), args.bootstrap_seal)
    mapped = verify_authority(args.probe14_log.read_bytes(),
                              args.probe14_error_headers.read_bytes(),
                              args.probe14_diagnostics.read_bytes())
    text = raw.decode("utf-8")
    base = text if not inverse else transform(text, True)[0]
    collisions = collision_audit(base)
    before = trust(text)
    result_text, records = transform(text, inverse)
    result = result_text.encode()
    check_shape(shape(result), expected_input() if inverse else expected_output(), args.bootstrap_seal)
    after = trust(result_text)
    if before != after or any(after.values()):
        raise RuntimeError(f"trust0 failure: {before} -> {after}")
    restored, _ = transform(result_text, not inverse)
    if restored.encode() != raw:
        raise RuntimeError("byte-exact inverse failure")
    if args.output.exists() or args.audit.exists():
        raise RuntimeError("refusing overwrite")
    record = {
        "schema": SCHEMA,
        "status": "STATIC_PASS_EXACT_P14_ACTIVATION_DISABLED",
        "activation": ACTIVATION, "promotion": False, "mode": args.mode,
        "authority": {"run_id": 31987036649, "job_id": 95263720714,
                      "artifact_id": 9274246215,
                      "candidate_sha256": INPUT_SHA256, "candidate_git_blob": INPUT_GIT_BLOB,
                      "log_sha256": LOG_SHA256, "headers_sha256": HEADERS_SHA256,
                      "diagnostics_sha256": DIAGNOSTICS_SHA256,
                      "errors": 124, "warnings": 349, "panic": 0, "exit": 1},
        "api_audit": {"mathlib_contdiff_operations_sha256": MATHLIB_CONTDIFF_OPERATIONS_SHA256,
                      "fa_dependency_sha256": FA_DEPENDENCY_SHA256,
                      "contDiff_div_codomain_restricted_to_scalar": True,
                      "contDiff_mul_normed_algebra": True,
                      "contDiff_inv_normed_field_algebra": True,
                      "lean_execution_claimed": False},
        "source": shape(raw), "result": shape(result),
        "repair_families": len(RULES), "repair_occurrences": len(records),
        "direct_diagnostics": sum(h.kind == "direct" for r in RULES for h in r.headers),
        "cascade_diagnostics": sum(h.kind == "cascade" for r in RULES for h in r.headers),
        "diagnostic_map": mapped, "rules": records, "collision_audit": collisions,
        "inverse_byte_equal": True, "trust": after,
        "activation_gate": "EXACT_TERMINAL_PROBE15_PACKAGE_AND_WORKFLOW",
        "execution": {"lean": False, "lake": False, "install": False, "git": False,
                      "network": False, "remote": False,
                      "repository_source_mutation": False},
    }
    args.output.write_bytes(result)
    args.audit.write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(json.dumps(record, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
