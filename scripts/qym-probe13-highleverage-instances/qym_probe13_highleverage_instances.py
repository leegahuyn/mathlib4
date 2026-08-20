#!/usr/bin/env python3
"""Exact-P12 producer-only repairs for QYM lines 36k--49,999.

Activation is disabled. ``transform`` is import-safe, byte-locked, reversible,
trust0-preserving, collision-audited, and performs no filesystem or subprocess
operation.
"""

from __future__ import annotations

import hashlib
import re
from dataclasses import dataclass


SCHEMA = "qym-probe13-highleverage-instances-exact-p12-v1"
ACTIVATION = False
INPUT_SHA256 = "4a123f69912bd7ce2ab070433f8cad0ecc284652a9cbab634def1936e9037212"
INPUT_GIT_BLOB = "76dd931638b9a6ad50ee764c65cd14489e8be310"
INPUT_BYTES = 2_936_558
INPUT_LF = 62_068
LOG_SHA256 = "62ce7c1b4ec23a23d690c64d49e45901faec66ff751d86e314e669b8c876c398"
HEADERS_SHA256 = "0cebf8d7bbcb923165a13f68f2afbbef1843bb26d77e072252c570b8e77b0dd9"
DIAGNOSTICS_SHA256 = "16b69f25e53f28d028cbefca21d5401e25dbfaa2847bdfdc8f7532034690ca23"

# Populated by one deterministic in-memory projection, then frozen.
OUTPUT_SHA256 = "2233d00552ec7fb81e2e2ba5bda585db1bd8945dc75be098ce15a618f8a4177b"
OUTPUT_GIT_BLOB = "ed43a01ba1bb081123c26fd2fdd63b2be1b5fb3a"
OUTPUT_BYTES = 2_937_767
OUTPUT_LF = 62_096


@dataclass(frozen=True)
class Rule:
    label: str
    old: str
    new: str
    direct_headers: tuple[int, ...]
    cascade_range: tuple[int, int]
    occurrences: int = 1


TRACE_OLD = """open QYM.FullCertification.P2ActualFixedPhaseCuspTraceGraphExtension

/-!
# The exact trace-comparison boundary
"""

TRACE_NEW = """open QYM.FullCertification.P2ActualFixedPhaseCuspTraceGraphExtension

noncomputable local instance actualFixedPhaseCanonicalCompletion_complete_inst
    (n : ℤ) (Y : ℝ) :
    CompleteSpace (ActualFixedPhaseCuspTraceCompletion n Y) :=
  actualFixedPhaseCuspTraceCompletionCompleteSpace n Y

noncomputable local instance actualFixedPhaseCanonicalCompletion_inner_inst
    (n : ℤ) (Y : ℝ) :
    InnerProductSpace ℂ (ActualFixedPhaseCuspTraceCompletion n Y) :=
  actualFixedPhaseCuspTraceCompletionInnerProductSpace n Y

/-!
# The exact trace-comparison boundary
"""

COLLAR_OLD = """noncomputable def actualFixedPhaseProductCollarStoredEnergyHilbertSpace
    (n : ℤ) (Y : ℝ) :
    HilbertSpace ℂ (ActualFixedPhaseProductCollarStoredEnergy n Y) :=
  ⟨⟩

/-- Central boundary-coordinate projection. -/
"""

COLLAR_NEW = """noncomputable def actualFixedPhaseProductCollarStoredEnergyHilbertSpace
    (n : ℤ) (Y : ℝ) :
    HilbertSpace ℂ (ActualFixedPhaseProductCollarStoredEnergy n Y) :=
  ⟨⟩

set_option synthInstance.maxHeartbeats 100000 in
noncomputable local instance actualFixedPhaseCollarZeroTraceStoredEnergy_inner_inst
    (n : ℤ) (Y : ℝ) :
    InnerProductSpace ℂ (ActualFixedPhaseCollarZeroTraceStoredEnergy n Y) :=
  inferInstance

set_option synthInstance.maxHeartbeats 100000 in
noncomputable local instance actualFixedPhaseProductCollarStoredEnergy_normed_inst
    (n : ℤ) (Y : ℝ) :
    NormedSpace ℂ (ActualFixedPhaseProductCollarStoredEnergy n Y) :=
  inferInstance

set_option synthInstance.maxHeartbeats 100000 in
noncomputable local instance actualFixedPhaseProductCollarStoredEnergy_inner_inst
    (n : ℤ) (Y : ℝ) :
    InnerProductSpace ℂ (ActualFixedPhaseProductCollarStoredEnergy n Y) :=
  inferInstance

/-- Central boundary-coordinate projection. -/
"""


RULES: tuple[Rule, ...] = (
    Rule(
        "canonical_trace_completion_reexpose_instances",
        TRACE_OLD,
        TRACE_NEW,
        (37111, 37117),
        (37111, 37322),
    ),
    Rule(
        "product_collar_cache_nested_withlp_instances",
        COLLAR_OLD,
        COLLAR_NEW,
        (48899, 48900, 48908, 48909, 49029),
        (48899, 49487),
    ),
)


def _sha(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _blob(raw: bytes) -> str:
    return hashlib.sha1(f"blob {len(raw)}\0".encode() + raw).hexdigest()


def _shape(raw: bytes) -> dict[str, object]:
    raw.decode("utf-8", errors="strict")
    return {
        "sha256": _sha(raw), "git_blob": _blob(raw), "bytes": len(raw),
        "lf": raw.count(b"\n"), "cr": b"\r" in raw, "nul": b"\0" in raw,
        "bom": raw.startswith(b"\xef\xbb\xbf"), "terminal_lf": raw.endswith(b"\n"),
    }


def _input_shape() -> dict[str, object]:
    return {
        "sha256": INPUT_SHA256, "git_blob": INPUT_GIT_BLOB,
        "bytes": INPUT_BYTES, "lf": INPUT_LF, "cr": False, "nul": False,
        "bom": False, "terminal_lf": True,
    }


def _output_shape() -> dict[str, object]:
    return {
        "sha256": OUTPUT_SHA256, "git_blob": OUTPUT_GIT_BLOB,
        "bytes": OUTPUT_BYTES, "lf": OUTPUT_LF, "cr": False, "nul": False,
        "bom": False, "terminal_lf": True,
    }


def _trust(text: str) -> dict[str, int]:
    return {
        "sorry": len(re.findall(r"\bsorry\b", text)),
        "admit": len(re.findall(r"\badmit\b", text)),
        "native_decide": len(re.findall(r"\bnative_decide\b", text)),
        "Lean.ofReduceBool": text.count("Lean.ofReduceBool"),
        "axiom_declaration": len(re.findall(r"(?m)^\s*axiom\s+", text)),
        "unsafe_declaration": len(re.findall(r"(?m)^\s*unsafe\s+", text)),
        "maxHeartbeats_zero": len(re.findall(r"set_option\s+maxHeartbeats\s+0\b", text)),
    }


def _check(actual: dict[str, object], expected: dict[str, object]) -> None:
    if actual != expected:
        raise RuntimeError(f"exact authority mismatch: {actual} != {expected}")


def _anchors(text: str, inverse: bool) -> dict[str, object]:
    spans: list[tuple[int, int, str, int]] = []
    for rule in RULES:
        active = rule.new if inverse else rule.old
        inactive = rule.old if inverse else rule.new
        starts = [m.start() for m in re.finditer(re.escape(active), text)]
        embedded_inactive = active.count(inactive) * len(starts)
        if len(starts) != 1 or text.count(inactive) != embedded_inactive:
            raise RuntimeError(f"{rule.label}: active/inactive collision")
        start = starts[0]
        line = text.count("\n", 0, start) + 1
        if not 36_000 <= line < 50_000:
            raise RuntimeError(f"{rule.label}: scope violation {line}")
        spans.append((start, start + len(active), rule.label, line))
    spans.sort()
    if any(left[1] > right[0] for left, right in zip(spans, spans[1:])):
        raise RuntimeError("rule anchor overlap")
    return {
        "own_overlap_count": 0,
        "undeclared_collision_count": 0,
        "active_lines": {label: line for _, _, label, line in spans},
    }


def _project(text: str, inverse: bool):
    rows = []
    ordered = tuple(reversed(RULES)) if inverse else RULES
    for rule in ordered:
        old, new = (rule.new, rule.old) if inverse else (rule.old, rule.new)
        count = text.count(old)
        if count != rule.occurrences:
            raise RuntimeError(f"{rule.label}: exact anchor count {count}")
        text = text.replace(old, new)
        rows.append({
            "label": rule.label,
            "direction": "inverse" if inverse else "forward",
            "occurrences": count,
            "direct_headers": list(rule.direct_headers),
            "cascade_range": list(rule.cascade_range),
        })
    return text, rows


def transform(text: str, inverse: bool = False):
    """Return transformed text and a deterministic static audit record."""
    raw = text.encode()
    unsealed = not OUTPUT_SHA256
    if inverse and unsealed:
        raise RuntimeError("inverse unavailable before output seal")
    _check(_shape(raw), _output_shape() if inverse else _input_shape())
    collision = _anchors(text, inverse)
    before = _trust(text)
    if any(before.values()):
        raise RuntimeError(f"input trust0 failure: {before}")
    result, rows = _project(text, inverse)
    result_raw = result.encode()
    if unsealed:
        s = _shape(result_raw)
        if any((s["cr"], s["nul"], s["bom"])) or not s["terminal_lf"]:
            raise RuntimeError(f"bootstrap shape failure: {s}")
    else:
        _check(_shape(result_raw), _input_shape() if inverse else _output_shape())
    after = _trust(result)
    if before != after or any(after.values()):
        raise RuntimeError(f"trust0 drift: {before} -> {after}")
    restored, _ = _project(result, not inverse)
    if restored.encode() != raw:
        raise RuntimeError("byte-exact opposite projection failed")
    return result, {
        "schema": SCHEMA,
        "status": "STATIC_PASS_EXACT_P12_NOT_LEAN_EXECUTED",
        "activation": ACTIVATION,
        "mode": "inverse" if inverse else "forward",
        "source": _shape(raw), "result": _shape(result_raw),
        "repair_families": len(RULES), "repair_occurrences": len(RULES),
        "rules": rows, "collision_audit": collision,
        "inverse_byte_equal": True, "trust": after,
        "execution": {"lean": False, "lake": False, "git": False,
                      "network": False, "remote": False,
                      "repository_source_mutation": False},
    }


apply_rules = transform
