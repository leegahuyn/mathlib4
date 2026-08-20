#!/usr/bin/env python3
"""Exact-Probe13 sequenced refinement for three SL(2,Z) action diagnostics.

Earlier active helpers replaced untyped action terms by typed
``Homeomorph.smul`` terms, but terminal Probe13 proves that the required
``ContinuousConstSMul SL(2, Z) H`` instance still does not exist.  This helper
is therefore deliberately a *sequenced refinement* of three consumed NEW
anchors.  Each proof exposes the same action through the existing
``SL(2,Z) -> GL(Fin 2,R)`` cast and uses the available GL continuity API.

The three historical overlaps are declared and exact; every other foreign
anchor, including all Probe14 components, must remain collision0.  The helper
is activation-disabled, byte-locked, reversible, trust0, and performs no
Lean/Lake/Git/network/remote or canonical-source operation.
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

SCHEMA = "qym-probe14-gl-action-exact-p13-sequenced-v1"
ACTIVATION = False

INPUT_SHA256 = "92e91734eb4b1d406d854a6021c815636eff6cf0aa2f4924e710249a583ebe3b"
INPUT_GIT_BLOB = "5c895f906b516366653aaf6fc459825e89045076"
INPUT_BYTES = 2_938_395
INPUT_LF = 62_112
LOG_SHA256 = "e2a675d67ef304dbbf6b3800b9e1a8c2fd1183ff16a82eb7f46b5a64fdef0826"
HEADERS_SHA256 = "74e4c1505182503c4acc9dfe6be6a4316e44b821ec7897b377597af12c07bf02"
DIAGNOSTICS_SHA256 = "0dbe572bed4860fd6f843045d3fbc9b11edab1931f63d6b5acb70bfd88d85dcb"

# Sealed after one deterministic bootstrap projection.
OUTPUT_SHA256 = "22bccab685696d63ff4a810301adbdec0957eb7758ad84f0162462279c3a273a"
OUTPUT_GIT_BLOB = "4fd1a285f1ad800f229c067ff9bf0db218d2caed"
OUTPUT_BYTES = 2_938_925
OUTPUT_LF = 62_128


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
    header: Header
    rationale: str
    precedent: str
    consumed_owner: str
    consumed_rule: str
    consumed_relation: str
    occurrences: int = 1


SYNTH_FAILURE = "failed to synthesize instance of type class"

RULES: tuple[Rule, ...] = (
    Rule(
        "selected_horocycle_continuity_explicit_gl_cast",
        "  exact ((Homeomorph.smul (gammaTwoCosetRep q) : ℍ ≃ₜ ℍ).continuous.comp\n"
        "    (QYM.FullCertification.P2ActualFixedPhaseCuspTraceGraphExtension.actualFixedPhaseHorizontalHorocyclePoint_continuous Y))\n",
        "  have hRepContinuous :\n"
        "      Continuous (fun z : ℍ => gammaTwoCosetRep q • z) := by\n"
        "    change Continuous\n"
        "      (fun z : ℍ =>\n"
        "        (gammaTwoCosetRep q : GL (Fin 2) ℝ) • z)\n"
        "    exact continuous_const_smul\n"
        "      (gammaTwoCosetRep q : GL (Fin 2) ℝ)\n"
        "  exact hRepContinuous.comp\n"
        "    (QYM.FullCertification.P2ActualFixedPhaseCuspTraceGraphExtension.actualFixedPhaseHorizontalHorocyclePoint_continuous Y)\n",
        Header(42791, 10, SYNTH_FAILURE, "lean.synthInstanceFailed"),
        "Prove continuity of the selected SL action through its GL cast before composing with the horizontal curve.",
        "Exact P13 lines 48095-48103 use change plus continuous_const_smul for this SL-to-GL upper-half-plane action.",
        "p11_40k",
        "selected_horocycle_continuity_pin_action_homeomorph",
        "own_old_equals_consumed_new",
    ),
    Rule(
        "selected_high_embedding_explicit_gl_homeomorph",
        "  change IsOpenEmbedding\n"
        "    ((Homeomorph.smul (gammaTwoCosetRep q) : ℍ ≃ₜ ℍ) ∘\n"
        "      horizontalHighPoint)\n"
        "  exact\n"
        "    (Homeomorph.smul (gammaTwoCosetRep q) : ℍ ≃ₜ ℍ).isOpenEmbedding.comp\n"
        "      horizontalHighPoint_isOpenEmbedding\n",
        "  change IsOpenEmbedding\n"
        "    ((Homeomorph.smul\n"
        "        (gammaTwoCosetRep q : GL (Fin 2) ℝ) : ℍ ≃ₜ ℍ) ∘\n"
        "      horizontalHighPoint)\n"
        "  exact\n"
        "    (Homeomorph.smul\n"
        "        (gammaTwoCosetRep q : GL (Fin 2) ℝ) : ℍ ≃ₜ ℍ).isOpenEmbedding.comp\n"
        "      horizontalHighPoint_isOpenEmbedding\n",
        Header(46404, 6, SYNTH_FAILURE, "lean.synthInstanceFailed"),
        "Present the selected action homeomorphism at the GL type that owns the continuity instance.",
        "The SL action is definitionally exposed through the same GL cast at exact P13 lines 35770-35774 and 48097-48103.",
        "p11_40k",
        "selected_high_embedding_pin_action_homeomorph",
        "own_old_equals_consumed_new",
    ),
    Rule(
        "selected_high_point_open_neighborhood_explicit_gl_continuity",
        "  have hUOpen : IsOpen U := by\n"
        "    exact isOpen_lt\n"
        "      (gammaTwoModularHeightEnvelope_continuous.comp\n"
        "        ((Homeomorph.smul ((gammaTwoCosetRep q)⁻¹) : ℍ ≃ₜ ℍ).continuous))\n"
        "      continuous_const\n",
        "  have hUOpen : IsOpen U := by\n"
        "    have hInvContinuous :\n"
        "        Continuous (fun z : ℍ => (gammaTwoCosetRep q)⁻¹ • z) := by\n"
        "      change Continuous\n"
        "        (fun z : ℍ =>\n"
        "          (((gammaTwoCosetRep q)⁻¹ : SL(2, ℤ)) :\n"
        "              GL (Fin 2) ℝ) • z)\n"
        "      exact continuous_const_smul\n"
        "        (((gammaTwoCosetRep q)⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ)\n"
        "    exact isOpen_lt\n"
        "      (gammaTwoModularHeightEnvelope_continuous.comp hInvContinuous)\n"
        "      continuous_const\n",
        Header(49516, 10, SYNTH_FAILURE, "lean.synthInstanceFailed"),
        "Prove continuity of the inverse selected action locally through the GL cast.",
        "Exact P13 lines 48095-48103 establish the identical cast-and-continuous_const_smul API pattern.",
        "p12_43k49k",
        "selected_high_point_use_typed_action_and_setof_goal",
        "own_old_strictly_contained_in_consumed_new",
    ),
)


# Historical owners are retained so their three consumed NEW-anchor overlaps
# can be proven exactly.  Every other helper must be disjoint.
FOREIGN_HELPERS: tuple[tuple[str, str, str], ...] = (
    ("p11_40k", "qym-probe11-40k-p10-conditional/qym_probe11_40k_p10_conditional.py", "6765e05b8681e4d7e13bc735c4d37ea038c75423a7d5ebc1ad73b179a99e0052"),
    ("p12_early", "qym-probe12-early-frontier-p11-conditional/qym_probe12_early_frontier_p11_conditional.py", "35b5ccf5f04899c810ca798cbcf700230fdfc4b930d16ab5d9cf646584954215"),
    ("p12_36k42k", "qym-probe12-36k42k-p11-reanchored/qym_probe12_36k42k_p11_reanchored.py", "5bd02f57232ac30c336b3e13574b7cba4dc4b0998f159e3fdebd41ed6354a365"),
    ("p12_43k49k", "qym-probe12-43k49k-p11-conditional/qym_probe12_43k49k_p11_conditional.py", "5070ada686ac425b76403ae53210e586bda305a8a70606d6d3bc6529ff2b2523"),
    ("p12_50k53k", "qym-probe12-50k53k-p11-conditional/qym_probe12_50k53k_p11_conditional.py", "5352b37ec754a5131164e91649b54a277b5d257258bc316f653b6d218bfb63c8"),
    ("p12_52k61k", "qym-probe12-52k61k-p11-conditional/qym_probe12_52k61k_p11_conditional.py", "7066e3297bd171ec58a4547ed426a8d9a6228abf4de78bf3ad203d880ef7f795"),
    ("p13_early", "qym-probe13-early-p12-conditional/qym_probe13_early_p12_conditional.py", "5462da0d1e49fc9f5769eeaf9052515cc905cdd55740dc55c3d930992d878210"),
    ("p13_direct50", "qym-probe13-50k50599-p12-reanchored/qym_probe13_50k50599_p12_reanchored.py", "a2eacbaebd1f3fddcb865a551613ea8ebbcdf12d74869be2b61c663a0891ed50"),
    ("p13_mid", "qym-probe13-highleverage-instances/qym_probe13_highleverage_instances.py", "e29672a27f2e6421426b73350655b3bae5dca187a8ab2fe39ea023cdf19ec47e"),
    ("p13_tail", "qym-probe13-tail-p12-direct/qym_probe13_tail_p12_direct.py", "11f19ecfabdde4da519321e133fd1a2265bedc7784cdd729e8dd05fbf310cc48"),
    ("p14_frontier_conditional", "qym-probe14-frontier-p13-conditional/qym_probe14_frontier_p13_conditional.py", "1118d53e64698cfe4d41da84d0a4450ad80efb4a0409b1eace0992abdfe20929"),
    ("p14_frontier_prep", "qym-probe14-30k47k-p13-reanchored/qym_probe14_30k47k_p13_reanchored.py", "671f909e011eb3a18e402c33bd4df30bcc7aa098bf928ecbf629aa8a09028686"),
    ("p14_tail", "qym-probe14-tail-prep-p13-static/qym_probe14_tail_prep_p13_static.py", "acd2cefb1db2b250558a362777b5e31c26fdb4dcfb23a29b4ff81f1a4c835412"),
    ("p14_producer", "qym-probe14-producer-timeouts-p13-static/qym_probe14_producer_timeouts_p13_static.py", "65a610e3dd278f084fb5f24285143f798685fd858efa9d8c92a589442a725cc0"),
)


PRODUCER_HELPER = "qym-probe14-producer-timeouts-p13-static/qym_probe14_producer_timeouts_p13_static.py"
PRODUCER_HELPER_SHA256 = "65a610e3dd278f084fb5f24285143f798685fd858efa9d8c92a589442a725cc0"

GL_PRECEDENT = (
    "theorem inverseEtaDeckAction_continuous (gamma : Gamma2) :\n"
    "    Continuous (fun tau : H => gamma • tau) := by\n"
    "  change Continuous\n"
    "    (fun tau : H =>\n"
    "      ((((gamma : Gamma2) : SL(2, ℤ)) : GL (Fin 2) ℝ) • tau))\n"
    "  exact\n"
    "    continuous_const_smul\n"
    "      ((((gamma : Gamma2) : SL(2, ℤ)) : GL (Fin 2) ℝ))\n"
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


def expected_input() -> dict[str, object]:
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


def expected_output() -> dict[str, object]:
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


def unsealed() -> bool:
    return not OUTPUT_SHA256 and not OUTPUT_GIT_BLOB and OUTPUT_BYTES == 0 and OUTPUT_LF == 0


def check_shape(actual: dict[str, object], expected: dict[str, object], bootstrap: bool) -> None:
    keys = ("cr", "nul", "bom", "terminal_lf") if bootstrap else tuple(expected)
    if any(actual[key] != expected[key] for key in keys):
        raise RuntimeError(f"shape mismatch: {actual} != {expected}")


def spans(text: str, needle: str) -> list[tuple[int, int]]:
    result: list[tuple[int, int]] = []
    start = 0
    while True:
        found = text.find(needle, start)
        if found < 0:
            return result
        result.append((found, found + len(needle)))
        start = found + 1


def load_module(name: str, relative: str, expected_sha: str) -> ModuleType:
    path = Path(__file__).resolve().parent.parent / relative
    raw = path.read_bytes()
    if sha256(raw) != expected_sha:
        raise RuntimeError(f"foreign helper drift: {name}")
    module_name = "_qym_probe14_gl_" + name
    spec = importlib.util.spec_from_file_location(module_name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot import helper: {name}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[module_name] = module
    spec.loader.exec_module(module)
    return module


def verify_authority(log: bytes, headers: bytes, diagnostics: bytes) -> list[dict[str, object]]:
    for label, raw, expected in (
        ("log", log, LOG_SHA256),
        ("headers", headers, HEADERS_SHA256),
        ("diagnostics", diagnostics, DIAGNOSTICS_SHA256),
    ):
        if sha256(raw) != expected:
            raise RuntimeError(f"Probe13 {label} identity mismatch")
    header_lines = headers.decode("utf-8").splitlines()
    rows = [json.loads(line) for line in diagnostics.decode("utf-8").splitlines()]
    if len(header_lines) != 151 or sum(row.get("severity") == "error" for row in rows) != 151:
        raise RuntimeError("terminal Probe13 error count mismatch")
    mapped: list[dict[str, object]] = []
    for rule in RULES:
        header = rule.header
        prefix = (
            f"PrimalitySheafVerification/QYM.lean:{header.line}:{header.column}: "
            f"error({header.code}): {header.message}"
        )
        hm = [line for line in header_lines if line.startswith(prefix)]
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
            raise RuntimeError(f"diagnostic mismatch: {rule.label}")
        mapped.append({"rule": rule.label, **header.__dict__})
    return mapped


def verify_precedent(text: str) -> dict[str, object]:
    count = text.count(GL_PRECEDENT)
    cast_set_count = text.count("(gammaTwoCosetRep q.1 : GL (Fin 2) ℝ) •")
    if count != 1 or cast_set_count < 1:
        raise RuntimeError(
            f"GL precedent mismatch: continuity={count}, set_action={cast_set_count}"
        )
    return {
        "continuity_block_count": count,
        "typed_gl_set_action_count": cast_set_count,
        "diagnostic_free_lines": ["35770-35774", "48095-48103"],
    }


def transform(text: str, inverse: bool = False) -> tuple[str, list[dict[str, object]]]:
    records: list[dict[str, object]] = []
    ordered = tuple(reversed(RULES)) if inverse else RULES
    for rule in ordered:
        old, new = (rule.new, rule.old) if inverse else (rule.old, rule.new)
        count = text.count(old)
        if count != rule.occurrences:
            raise RuntimeError(f"anchor count: {rule.label}: {count}")
        if text.count(new) != old.count(new) * count:
            raise RuntimeError(f"destination anchor collision: {rule.label}")
        text = text.replace(old, new)
        records.append(
            {
                "label": rule.label,
                "direction": "inverse" if inverse else "forward",
                "occurrences": count,
                "header": rule.header.__dict__,
                "rationale": rule.rationale,
                "precedent": rule.precedent,
                "consumed_owner": rule.consumed_owner,
                "consumed_rule": rule.consumed_rule,
                "consumed_relation": rule.consumed_relation,
            }
        )
    return text, records


apply_rules = transform


def collision_audit(text: str, inverse: bool) -> dict[str, object]:
    own: list[tuple[int, int, str, int]] = []
    for rule in RULES:
        active = rule.new if inverse else rule.old
        inactive = rule.old if inverse else rule.new
        found = spans(text, active)
        embedded_inactive = active.count(inactive) * len(found)
        if len(found) != 1 or text.count(inactive) != embedded_inactive:
            raise RuntimeError(f"active/inactive collision: {rule.label}")
        start, end = found[0]
        own.append((start, end, rule.label, text.count("\n", 0, start) + 1))
    ordered = sorted(own)
    if any(left[1] > right[0] for left, right in zip(ordered, ordered[1:])):
        raise RuntimeError("own rule overlap")

    declared: list[dict[str, object]] = []
    undeclared: list[dict[str, object]] = []
    identities: dict[str, str] = {}
    modules: dict[str, ModuleType] = {}
    for name, relative, expected_sha in FOREIGN_HELPERS:
        module = load_module(name, relative, expected_sha)
        modules[name] = module
        identities[name] = expected_sha
        table = getattr(module, "RULES", None) or getattr(module, "REPAIRS", None)
        if not isinstance(table, tuple):
            raise RuntimeError(f"foreign helper has no tuple table: {name}")
        for foreign in table:
            for variant, anchor in (("old", foreign.old), ("new", foreign.new)):
                for fstart, fend in spans(text, anchor):
                    for ostart, oend, own_label, own_line in own:
                        if max(fstart, ostart) >= min(fend, oend):
                            continue
                        own_rule = next(rule for rule in RULES if rule.label == own_label)
                        expected = (
                            name == own_rule.consumed_owner
                            and foreign.label == own_rule.consumed_rule
                            and variant == "new"
                        )
                        relation = (
                            "own_old_equals_consumed_new"
                            if ostart == fstart and oend == fend
                            else "own_old_strictly_contained_in_consumed_new"
                            if fstart <= ostart and oend <= fend
                            else "other_overlap"
                        )
                        row = {
                            "own_rule": own_label,
                            "own_line": own_line,
                            "foreign_owner": name,
                            "foreign_rule": foreign.label,
                            "foreign_variant": variant,
                            "relation": relation,
                        }
                        if expected and relation == own_rule.consumed_relation:
                            declared.append(row)
                        else:
                            undeclared.append(row)
    expected_declared = {
        (rule.label, rule.consumed_owner, rule.consumed_rule, rule.consumed_relation)
        for rule in RULES
    }
    actual_declared = {
        (
            row["own_rule"],
            row["foreign_owner"],
            row["foreign_rule"],
            row["relation"],
        )
        for row in declared
    }
    if undeclared or actual_declared != expected_declared or len(declared) != len(RULES):
        raise RuntimeError(
            "sequenced collision audit failure: "
            f"declared={declared}, undeclared={undeclared}"
        )
    p14_names = {name for name, _, _ in FOREIGN_HELPERS if name.startswith("p14_")}
    if any(row["foreign_owner"] in p14_names for row in declared):
        raise RuntimeError("Probe14 overlap is forbidden")
    return {
        "foreign_helper_sha256": identities,
        "declared_consumed_new_anchor_overlaps": declared,
        "declared_overlap_count": len(declared),
        "undeclared_overlap_count": 0,
        "probe14_overlap_count": 0,
        "own_overlap_count": 0,
        "modules": modules,
    }


def producer_commutation_audit(text: str) -> dict[str, object]:
    producer = load_module("p14_producer_commutation", PRODUCER_HELPER, PRODUCER_HELPER_SHA256)
    producer_first, _ = producer.transform(text, False)
    producer_then_gl, _ = transform(producer_first, False)
    gl_first, _ = transform(text, False)
    gl_then_producer, _ = producer.transform(gl_first, False)
    if producer_then_gl != gl_then_producer:
        raise RuntimeError("producer/GL forward order does not commute")
    combined = producer_then_gl
    restore_a, _ = transform(combined, True)
    restore_a, _ = producer.transform(restore_a, True)
    restore_b, _ = producer.transform(combined, True)
    restore_b, _ = transform(restore_b, True)
    if restore_a != text or restore_b != text:
        raise RuntimeError("producer/GL inverse order did not restore P13")
    combined_raw = combined.encode("utf-8")
    return {
        "producer_helper_sha256": PRODUCER_HELPER_SHA256,
        "forward_orders_checked": 2,
        "forward_byte_equal": True,
        "inverse_orders_checked": 2,
        "inverse_exact_p13": True,
        "combined": shape(combined_raw),
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--probe13-log", type=Path, required=True)
    parser.add_argument("--probe13-error-headers", type=Path, required=True)
    parser.add_argument("--probe13-diagnostics", type=Path, required=True)
    parser.add_argument("--audit", type=Path, required=True)
    parser.add_argument("--mode", choices=("forward", "inverse"), default="forward")
    parser.add_argument("--bootstrap-seal", action="store_true")
    args = parser.parse_args()

    inverse = args.mode == "inverse"
    if args.bootstrap_seal != unsealed():
        raise RuntimeError("bootstrap/seal state mismatch")
    source = args.input.read_bytes()
    source_shape = shape(source)
    check_shape(source_shape, expected_output() if inverse else expected_input(), args.bootstrap_seal)
    mapped = verify_authority(
        args.probe13_log.read_bytes(),
        args.probe13_error_headers.read_bytes(),
        args.probe13_diagnostics.read_bytes(),
    )
    text = source.decode("utf-8", errors="strict")
    base_text = text if not inverse else transform(text, True)[0]
    precedent = verify_precedent(base_text)
    collision = collision_audit(base_text, False)
    collision.pop("modules")
    commutation = producer_commutation_audit(base_text)
    before = trust(text)
    result_text, records = transform(text, inverse)
    result = result_text.encode("utf-8")
    result_shape = shape(result)
    check_shape(result_shape, expected_input() if inverse else expected_output(), args.bootstrap_seal)
    after = trust(result_text)
    if before != after or any(after.values()):
        raise RuntimeError(f"trust0 failure: {before} -> {after}")
    restored, _ = transform(result_text, not inverse)
    if restored.encode("utf-8") != source:
        raise RuntimeError("opposite transform failed byte-exact restoration")
    if args.output.exists() or args.audit.exists():
        raise RuntimeError("refusing to overwrite output or audit")

    record = {
        "schema": SCHEMA,
        "status": "STATIC_PASS_EXACT_P13_SEQUENCED_REFINEMENT_NOT_LEAN_EXECUTED",
        "activation": ACTIVATION,
        "promotion": False,
        "mode": args.mode,
        "authority": {
            "run_id": 31983803997,
            "artifact_id": 9273225529,
            "candidate_sha256": INPUT_SHA256,
            "candidate_git_blob": INPUT_GIT_BLOB,
            "log_sha256": LOG_SHA256,
            "headers_sha256": HEADERS_SHA256,
            "diagnostics_sha256": DIAGNOSTICS_SHA256,
            "errors": 151,
            "warnings": 341,
            "panic": 0,
            "exit": 1,
        },
        "scope": {
            "direct_diagnostic_lines": [rule.header.line for rule in RULES],
            "historical_consumed_new_anchor_refinement": True,
            "declared_historical_overlap_count": len(RULES),
            "probe14_overlap_count": 0,
        },
        "source": source_shape,
        "result": result_shape,
        "repair_families": len(RULES),
        "repair_occurrences": sum(row["occurrences"] for row in records),
        "direct_diagnostics": len(mapped),
        "diagnostic_map": mapped,
        "precedent_audit": precedent,
        "rules": records,
        "collision_audit": collision,
        "producer_commutation_audit": commutation,
        "inverse_byte_equal": True,
        "trust": after,
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
