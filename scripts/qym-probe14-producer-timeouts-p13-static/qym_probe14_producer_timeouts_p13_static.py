#!/usr/bin/env python3
"""Activation-disabled exact-Probe13 producer repair for QYM.

This helper owns the surviving H^(1/2) extendOfNorm theorem and the bounded
product-collar declarations and old-graph extendOfNorm theorem family.  It
edits producer declarations only; downstream
unknown-constant/unknown-identifier diagnostics are attributed cascades.

The projection is byte-locked, exact-counted, reversible, trust0-preserving,
and collision-audited.  It does not run Lean/Lake, mutate the repository source,
or perform Git/network/remote actions.  Activation remains disabled pending a
scratch compile against the exact terminal Probe13 authority.
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

SCHEMA = "qym-probe14-producer-timeouts-exact-p13-static-v1"
ACTIVATION = False

INPUT_SHA256 = "92e91734eb4b1d406d854a6021c815636eff6cf0aa2f4924e710249a583ebe3b"
INPUT_GIT_BLOB = "5c895f906b516366653aaf6fc459825e89045076"
INPUT_BYTES = 2_938_395
INPUT_LF = 62_112
LOG_SHA256 = "e2a675d67ef304dbbf6b3800b9e1a8c2fd1183ff16a82eb7f46b5a64fdef0826"
HEADERS_SHA256 = "74e4c1505182503c4acc9dfe6be6a4316e44b821ec7897b377597af12c07bf02"
DIAGNOSTICS_SHA256 = "0dbe572bed4860fd6f843045d3fbc9b11edab1931f63d6b5acb70bfd88d85dcb"

# Sealed after one deterministic bootstrap projection.
OUTPUT_SHA256 = "fac716c5cadbd3ed9f2d9cb12a870a7fdf436003aa6b5e899bbd3290097b2883"
OUTPUT_GIT_BLOB = "b154141a2fdeb626b5d6e14eaee1ccab5654e6fd"
OUTPUT_BYTES = 2_938_987
OUTPUT_LF = 62_119

FINITE_MAX_HEARTBEATS = 2_000_000


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
    occurrences: int = 1


TIMEOUT_WHNF = (
    "(deterministic) timeout at `whnf`, maximum number of heartbeats "
    "(200000) has been reached"
)
TIMEOUT_PENDING = (
    "(deterministic) timeout at `«synthesize pending MVars»`, maximum number "
    "of heartbeats (200000) has been reached"
)
TIMEOUT_NESTED = (
    "(deterministic) timeout at `«abstract nested proofs»`, maximum number "
    "of heartbeats (200000) has been reached"
)
TIMEOUT_DEF_EQ = (
    "(deterministic) timeout at `isDefEq`, maximum number of heartbeats "
    "(200000) has been reached"
)

CORE_MODULE = (
    "  letI : Module ℂ (InverseEtaFixedPhaseCore n) :=\n"
    "    DefinitionOneSobolev.FixedPhaseGraphCompletion.fixedPhaseGraphCoreModule n\n"
)
CORE_ADD_COMM_GROUP = (
    "  letI : AddCommGroup (InverseEtaFixedPhaseCore n) :=\n"
    "    DefinitionOneSobolev.FixedPhaseGraphCompletion.fixedPhaseGraphCoreAddCommGroup n\n"
)


RULES: tuple[Rule, ...] = (
    Rule(
        "hhalf_extension_core_pin_fixed_phase_instances",
        "      actualFixedPhaseThreeCuspTraceToHhalfFull n Y u := by\n"
        "  rcases hBound with ⟨C, hC⟩\n"
        "  simpa [actualFixedPhaseHhalfTraceExtension] using\n"
        "    (LinearMap.extendOfNorm_eq\n"
        "      (f := actualFixedPhaseThreeCuspTraceToHhalfFull n Y)\n"
        "      (e := coreMap n)\n"
        "      (denseRange_coreMap n) ⟨C, hC⟩ u)\n",
        "      actualFixedPhaseThreeCuspTraceToHhalfFull n Y u := by\n"
        + CORE_MODULE
        + CORE_ADD_COMM_GROUP
        + "  rcases hBound with ⟨C, hC⟩\n"
        "  exact LinearMap.extendOfNorm_eq\n"
        "    (denseRange_coreMap n) ⟨C, hC⟩ u\n",
        (
            Header(42217, 0, TIMEOUT_WHNF),
            Header(
                42236,
                8,
                "(kernel) unknown constant "
                "'QYM.FullCertification.P2ClassicalHhalfTraceExtension."
                "actualFixedPhaseHhalfTraceExtension_core'",
                kind="cascade",
            ),
        ),
        "Pin the exact fixed-phase core Module/AddCommGroup carried by coreMap, then use the receiver-inferred extendOfNorm theorem directly.",
        "The same local-instance plus direct-API blocks compile in the stored-L2 core theorem at exact P13 lines 36735-36746.",
    ),
    Rule(
        "product_collar_norm_sq_finite_heartbeat_wrapper",
        "theorem actualFixedPhaseProductCollar_norm_sq_decomposition\n",
        f"set_option maxHeartbeats {FINITE_MAX_HEARTBEATS} in\n"
        "theorem actualFixedPhaseProductCollar_norm_sq_decomposition\n",
        (
            Header(49149, 6, TIMEOUT_WHNF),
            Header(49153, 73, TIMEOUT_PENDING),
        ),
        "Give only this expensive nested-WithLp Pythagorean declaration a finite ten-times heartbeat budget.",
        "Two independent deterministic 200000-heartbeat failures occur inside this one declaration after Probe13's explicit nested norm/inner caches are active.",
    ),
    Rule(
        "product_collar_core_synthesis_finite_heartbeat_wrapper",
        "noncomputable def actualFixedPhaseProductCollarCoreSynthesis\n",
        f"set_option maxHeartbeats {FINITE_MAX_HEARTBEATS} in\n"
        "noncomputable def actualFixedPhaseProductCollarCoreSynthesis\n",
        (
            Header(49167, 18, TIMEOUT_NESTED),
            Header(49181, 8, TIMEOUT_WHNF),
            Header(
                49189,
                9,
                "Unknown identifier `actualFixedPhaseProductCollarCoreSynthesis`",
                "lean.unknownIdentifier",
                "cascade",
            ),
            Header(
                49200,
                7,
                "Unknown identifier `actualFixedPhaseProductCollarCoreSynthesis`",
                "lean.unknownIdentifier",
                "cascade",
            ),
            Header(
                49216,
                16,
                "Unknown identifier `actualFixedPhaseProductCollarCoreSynthesis`",
                "lean.unknownIdentifier",
                "cascade",
            ),
            Header(
                49402,
                18,
                "Unknown identifier `actualFixedPhaseProductCollarCoreSynthesis`",
                "lean.unknownIdentifier",
                "cascade",
            ),
        ),
        "Bound the structure elaboration and its two linearity proofs without changing the mathematical term.",
        "The declaration reports deterministic timeouts at abstract-nested-proofs and whnf; all listed unknown identifiers are downstream of the missing definition.",
    ),
    Rule(
        "product_collar_core_synthesis_surjective_finite_heartbeat_wrapper",
        "theorem actualFixedPhaseProductCollarCoreSynthesis_surjective\n",
        f"set_option maxHeartbeats {FINITE_MAX_HEARTBEATS} in\n"
        "theorem actualFixedPhaseProductCollarCoreSynthesis_surjective\n",
        (
            Header(49204, 6, TIMEOUT_WHNF),
            Header(
                49217,
                3,
                "Unknown identifier `actualFixedPhaseProductCollarCoreSynthesis_surjective`",
                "lean.unknownIdentifier",
                "cascade",
            ),
            Header(
                49413,
                4,
                "Unknown identifier `actualFixedPhaseProductCollarCoreSynthesis_denseRange`",
                "lean.unknownIdentifier",
                "cascade",
            ),
            Header(
                49427,
                14,
                "Unknown constant `QYM.FullCertification.P2CollarTraceExtension."
                "actualFixedPhaseProductCollarCoreSynthesis_surjective`",
                "lean.unknownIdentifier",
                "cascade",
            ),
            Header(
                49431,
                14,
                "Unknown constant `QYM.FullCertification.P2CollarTraceExtension."
                "actualFixedPhaseProductCollarStoredEnergyCertificate`",
                "lean.unknownIdentifier",
                "cascade",
            ),
        ),
        "Give the constructive surjectivity proof a finite declaration-local budget.",
        "Its subtype construction times out at whnf; denseRange, certificate, and axiom-audit failures are downstream declarations.",
    ),
    Rule(
        "product_collar_old_graph_extension_core_pin_fixed_phase_instances",
        "      actualFixedPhaseSmoothCoreToProductCollarProfile n Y u := by\n"
        "  rcases hBound with ⟨C0, hC0⟩\n"
        "  simpa [actualFixedPhaseOldGraphToProductCollarExtension] using\n"
        "    (LinearMap.extendOfNorm_eq\n"
        "      (f := actualFixedPhaseSmoothCoreToProductCollarProfile n Y)\n"
        "      (e := coreMap n)\n"
        "      (denseRange_coreMap n) ⟨C0, hC0⟩ u)\n",
        "      actualFixedPhaseSmoothCoreToProductCollarProfile n Y u := by\n"
        + CORE_MODULE
        + CORE_ADD_COMM_GROUP
        + "  rcases hBound with ⟨C0, hC0⟩\n"
        "  exact LinearMap.extendOfNorm_eq\n"
        "    (denseRange_coreMap n) ⟨C0, hC0⟩ u\n",
        (
            Header(49268, 0, TIMEOUT_WHNF),
            Header(
                49320,
                8,
                "(kernel) unknown constant "
                "'QYM.FullCertification.P2CollarTraceExtension."
                "actualFixedPhaseOldGraphToProductCollarExtension_core'",
                kind="cascade",
            ),
        ),
        "Pin the core structures and use the direct extendOfNorm core theorem.",
        "This is the exact successful stored-trace core theorem pattern, specialized only in the codomain linear map.",
    ),
    Rule(
        "product_collar_old_graph_extension_norm_pin_fixed_phase_instances",
        "      C0 * ‖x‖ := by\n"
        "  simpa [actualFixedPhaseOldGraphToProductCollarExtension] using\n"
        "    (LinearMap.norm_extendOfNorm_apply_le\n"
        "      (f := actualFixedPhaseSmoothCoreToProductCollarProfile n Y)\n"
        "      (e := coreMap n)\n"
        "      (denseRange_coreMap n) C0 hC0 x)\n",
        "      C0 * ‖x‖ := by\n"
        + CORE_MODULE
        + CORE_ADD_COMM_GROUP
        + "  exact LinearMap.norm_extendOfNorm_apply_le\n"
        "    (denseRange_coreMap n) C0 hC0 x\n",
        (Header(49296, 6, TIMEOUT_DEF_EQ),),
        "Pin the structures and let the expected type infer f/e for norm_extendOfNorm_apply_le.",
        "The exact P13 stored-trace norm theorem at lines 36750-36762 uses this block and has no diagnostic.",
    ),
    Rule(
        "product_collar_old_graph_extension_unique_pin_fixed_phase_instances",
        "    actualFixedPhaseOldGraphToProductCollarExtension n Y = T := by\n"
        "  rcases hBound with ⟨C0, hC0⟩\n"
        "  have hComp : T.toLinearMap.comp (coreMap n) =\n"
        "      actualFixedPhaseSmoothCoreToProductCollarProfile n Y := by\n"
        "    ext u\n"
        "    exact hT u\n"
        "  simpa [actualFixedPhaseOldGraphToProductCollarExtension] using\n"
        "    (LinearMap.extendOfNorm_unique\n"
        "      (f := actualFixedPhaseSmoothCoreToProductCollarProfile n Y)\n"
        "      (e := coreMap n)\n"
        "      (denseRange_coreMap n) C0 hC0 T hComp)\n",
        "    actualFixedPhaseOldGraphToProductCollarExtension n Y = T := by\n"
        + CORE_MODULE
        + CORE_ADD_COMM_GROUP
        + "  rcases hBound with ⟨C0, hC0⟩\n"
        "  have hComp : T.toLinearMap.comp (coreMap n) =\n"
        "      actualFixedPhaseSmoothCoreToProductCollarProfile n Y := by\n"
        "    ext u\n"
        "    exact hT u\n"
        "  exact LinearMap.extendOfNorm_unique\n"
        "    (denseRange_coreMap n) C0 hC0 T hComp\n",
        (Header(49298, 0, TIMEOUT_WHNF),),
        "Pin the structures and use the receiver-inferred uniqueness theorem directly.",
        "The exact P13 stored-trace unique theorem at lines 36784-36801 uses the identical instance/API pattern.",
    ),
)


# Frozen active Probe12/Probe13 components plus the already sealed Probe14 tail.
FOREIGN_HELPERS: tuple[tuple[str, str, str], ...] = (
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
    ("p14_tail_sealed", "qym-probe14-tail-prep-p13-static/qym_probe14_tail_prep_p13_static.py", "acd2cefb1db2b250558a362777b5e31c26fdb4dcfb23a29b4ff81f1a4c835412"),
    ("p14_frontier_sealed", "qym-probe14-30k47k-p13-reanchored/qym_probe14_30k47k_p13_reanchored.py", "671f909e011eb3a18e402c33bd4df30bcc7aa098bf928ecbf629aa8a09028686"),
)


PRECEDENT_SNIPPETS: tuple[tuple[str, str], ...] = (
    (
        "stored_trace_core",
        "theorem actualFixedPhaseStoredTraceExtension_core\n"
        "    (n : ℤ) (Y : ℝ)\n"
        "    (hBound : ActualFixedPhaseStoredTraceBounded n Y)\n"
        "    (u : InverseEtaFixedPhaseCore n) :\n"
        "    actualFixedPhaseStoredTraceExtension n Y (coreMap n u) =\n"
        "      actualFixedPhaseThreeCuspTraceToL2Linear n Y u := by\n"
        + CORE_MODULE
        + CORE_ADD_COMM_GROUP
        + "  rcases hBound with ⟨C, hC⟩\n"
        "  exact LinearMap.extendOfNorm_eq (denseRange_coreMap n) ⟨C, hC⟩ u\n",
    ),
    (
        "stored_trace_norm",
        "    ‖actualFixedPhaseStoredTraceExtension n Y x‖ ≤ C * ‖x‖ := by\n"
        + CORE_MODULE
        + CORE_ADD_COMM_GROUP
        + "  exact LinearMap.norm_extendOfNorm_apply_le\n"
        "    (denseRange_coreMap n) C hC x\n",
    ),
    (
        "stored_trace_unique",
        "    actualFixedPhaseStoredTraceExtension n Y = T := by\n"
        + CORE_MODULE
        + CORE_ADD_COMM_GROUP
        + "  rcases hBound with ⟨C, hC⟩\n"
        "  have hComp : T.toLinearMap.comp (coreMap n) =\n"
        "      actualFixedPhaseThreeCuspTraceToL2Linear n Y := by\n"
        "    ext u\n"
        "    exact hT u\n"
        "  exact LinearMap.extendOfNorm_unique\n"
        "    (denseRange_coreMap n) C hC T hComp\n",
    ),
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
        "maxHeartbeats_zero": len(
            re.findall(r"set_option\s+maxHeartbeats\s+0\b", text)
        ),
    }


def finite_heartbeat_inventory(text: str) -> dict[str, int]:
    values = [
        int(match.group(1))
        for match in re.finditer(r"set_option\s+maxHeartbeats\s+(\d+)\b", text)
    ]
    return {
        "finite_positive": sum(value > 0 for value in values),
        "zero": sum(value == 0 for value in values),
        "probe14_value": sum(value == FINITE_MAX_HEARTBEATS for value in values),
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
    seen: set[tuple[int, int]] = set()
    for rule in RULES:
        for header in rule.headers:
            key = (header.line, header.column)
            if key in seen:
                raise RuntimeError(f"diagnostic ownership overlap: {key}")
            seen.add(key)
            prefix = (
                f"PrimalitySheafVerification/QYM.lean:{header.line}:{header.column}: error"
                + (f"({header.code})" if header.code else "")
                + f": {header.message}"
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
                raise RuntimeError(
                    f"diagnostic mismatch: {rule.label} {header.line}:{header.column}"
                )
            mapped.append({"rule": rule.label, **header.__dict__})
    return mapped


def verify_precedents(text: str) -> dict[str, object]:
    counts = {label: text.count(snippet) for label, snippet in PRECEDENT_SNIPPETS}
    if any(count != 1 for count in counts.values()):
        raise RuntimeError(f"exact local precedent mismatch: {counts}")
    return {
        "counts": counts,
        "diagnostic_free_p13_lines": ["36735-36746", "36750-36762", "36784-36801"],
        "same_module_addcomm_api_pattern": True,
    }


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
        raise RuntimeError(f"foreign helper drift: {name}")
    module_name = "_qym_probe14_producer_" + name
    spec = importlib.util.spec_from_file_location(module_name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot import foreign helper: {name}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[module_name] = module
    spec.loader.exec_module(module)
    return module


def collision_audit(text: str, inverse: bool) -> dict[str, object]:
    own: list[tuple[int, int, str, int]] = []
    exact_anchor_equalities: list[tuple[str, str, str, str, str]] = []
    for rule in RULES:
        active = rule.new if inverse else rule.old
        inactive = rule.old if inverse else rule.new
        found = spans(text, active)
        embedded_inactive = active.count(inactive) * len(found)
        if len(found) != rule.occurrences or text.count(inactive) != embedded_inactive:
            raise RuntimeError(f"active/inactive anchor collision: {rule.label}")
        for start, end in found:
            line = text.count("\n", 0, start) + 1
            if not (42_000 <= line <= 42_999 or 49_000 <= line <= 49_999):
                raise RuntimeError(f"scope violation: {rule.label}: {line}")
            own.append((start, end, rule.label, line))
    ordered = sorted(own)
    own_overlaps = [
        (left[2], right[2])
        for left, right in zip(ordered, ordered[1:])
        if left[1] > right[0]
    ]
    foreign_overlaps: list[tuple[str, str, str]] = []
    identities: dict[str, str] = {}
    for name, relative, expected_sha in FOREIGN_HELPERS:
        module = load_foreign(name, relative, expected_sha)
        identities[name] = expected_sha
        table = getattr(module, "RULES", None) or getattr(module, "REPAIRS", None)
        if not isinstance(table, tuple):
            raise RuntimeError(f"foreign helper has no tuple rule table: {name}")
        for foreign in table:
            for foreign_variant, anchor in (("old", foreign.old), ("new", foreign.new)):
                for own_rule in RULES:
                    for own_variant, own_anchor in (("old", own_rule.old), ("new", own_rule.new)):
                        if own_anchor == anchor:
                            exact_anchor_equalities.append(
                                (own_rule.label, own_variant, name, foreign.label, foreign_variant)
                            )
                for fstart, fend in spans(text, anchor):
                    for ostart, oend, own_label, _ in own:
                        if max(fstart, ostart) < min(fend, oend):
                            foreign_overlaps.append(
                                (own_label, f"{name}:{foreign.label}", foreign_variant)
                            )
    if own_overlaps or exact_anchor_equalities or foreign_overlaps:
        raise RuntimeError(
            "collision0 failure: "
            f"own={own_overlaps}, equalities={exact_anchor_equalities}, foreign={foreign_overlaps}"
        )
    return {
        "foreign_helper_sha256": identities,
        "own_spans": [
            {"label": label, "line": line, "start": start, "end": end}
            for start, end, label, line in ordered
        ],
        "own_span_overlaps": [],
        "exact_anchor_equalities": [],
        "foreign_span_overlaps": [],
        "undeclared_collisions": 0,
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
                "headers": [header.__dict__ for header in rule.headers],
                "rationale": rule.rationale,
                "evidence": rule.evidence,
            }
        )
    return text, records


apply_rules = transform


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
    precedents = verify_precedents(text)
    collisions = collision_audit(text, inverse)
    before_trust = trust(text)
    before_heartbeat = finite_heartbeat_inventory(text)
    result_text, records = transform(text, inverse)
    result = result_text.encode("utf-8")
    result_shape = shape(result)
    check_shape(result_shape, expected_input() if inverse else expected_output(), args.bootstrap_seal)
    after_trust = trust(result_text)
    after_heartbeat = finite_heartbeat_inventory(result_text)
    if before_trust != after_trust or any(after_trust.values()):
        raise RuntimeError(f"trust0 failure: {before_trust} -> {after_trust}")
    expected_delta = -3 if inverse else 3
    if after_heartbeat["finite_positive"] - before_heartbeat["finite_positive"] != expected_delta:
        raise RuntimeError(f"finite heartbeat inventory drift: {before_heartbeat} -> {after_heartbeat}")
    if after_heartbeat["zero"] or before_heartbeat["zero"]:
        raise RuntimeError("maxHeartbeats 0 forbidden")
    restored, _ = transform(result_text, not inverse)
    if restored.encode("utf-8") != source:
        raise RuntimeError("opposite transform failed byte-exact restoration")
    if args.output.exists() or args.audit.exists():
        raise RuntimeError("refusing to overwrite output or audit")

    record = {
        "schema": SCHEMA,
        "status": "STATIC_PASS_EXACT_TERMINAL_PROBE13_NOT_LEAN_EXECUTED",
        "activation": ACTIVATION,
        "promotion": False,
        "mode": args.mode,
        "authority": {
            "run_id": 31983803997,
            "artifact_id": 9273225529,
            "candidate_sha256": INPUT_SHA256,
            "candidate_git_blob": INPUT_GIT_BLOB,
            "candidate_bytes": INPUT_BYTES,
            "candidate_lf": INPUT_LF,
            "log_sha256": LOG_SHA256,
            "headers_sha256": HEADERS_SHA256,
            "diagnostics_sha256": DIAGNOSTICS_SHA256,
            "errors": 151,
            "warnings": 341,
            "panic": 0,
            "exit": 1,
        },
        "scope": {
            "producer_roots": [42217, 49125, 49167, 49197, 49268, 49284, 49298],
            "direct_diagnostic_lines": sorted(
                {
                    header.line
                    for rule in RULES
                    for header in rule.headers
                    if header.kind == "direct"
                }
            ),
            "cascade_diagnostic_lines": sorted(
                {
                    header.line
                    for rule in RULES
                    for header in rule.headers
                    if header.kind == "cascade"
                }
            ),
            "cascade_lines_modified": False,
            "maxHeartbeats_zero_forbidden": True,
            "finite_declaration_budget": FINITE_MAX_HEARTBEATS,
            "probe13_cached_nested_withlp_instances_retained": True,
        },
        "source": source_shape,
        "result": result_shape,
        "repair_families": len(RULES),
        "repair_occurrences": sum(record["occurrences"] for record in records),
        "direct_diagnostics": sum(header.kind == "direct" for rule in RULES for header in rule.headers),
        "cascade_diagnostics": sum(header.kind == "cascade" for rule in RULES for header in rule.headers),
        "diagnostic_map": mapped,
        "precedent_audit": precedents,
        "rules": records,
        "collision_audit": collisions,
        "finite_heartbeat_before": before_heartbeat,
        "finite_heartbeat_after": after_heartbeat,
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
