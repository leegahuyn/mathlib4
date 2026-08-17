#!/usr/bin/env python3
"""Exact-Probe13 direct repairs for the first two independent frontier owners.

This activation-disabled transformer refines two active Probe13 early rules:
the manifold chain rule is rewritten in the goal instead of transported by a
fragile ``simpa using``, and the safe-potential bound uses the one-sided
``ContinuousLinearMap.opNorm_smul_le`` API instead of demanding the stronger
``NormSMulClass`` needed by ``norm_smul``.

The helper is exact-counted, authority-locked, reversible, trust0, and checks
the hashes and active rule spans of all four Probe13 components.  It never
invokes Lean, Lake, Git, a network, or a remote service and never mutates a
repository source.
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

SCHEMA = "qym-probe14-frontier-p13-conditional-v1"
ACTIVATION = False

INPUT_SHA256 = "92e91734eb4b1d406d854a6021c815636eff6cf0aa2f4924e710249a583ebe3b"
INPUT_GIT_BLOB = "5c895f906b516366653aaf6fc459825e89045076"
INPUT_BYTES = 2_938_395
INPUT_LF = 62_112
LOG_SHA256 = "e2a675d67ef304dbbf6b3800b9e1a8c2fd1183ff16a82eb7f46b5a64fdef0826"
HEADERS_SHA256 = "74e4c1505182503c4acc9dfe6be6a4316e44b821ec7897b377597af12c07bf02"
DIAGNOSTICS_SHA256 = "0dbe572bed4860fd6f843045d3fbc9b11edab1931f63d6b5acb70bfd88d85dcb"
EXPECTED_ERRORS = 151
EXPECTED_WARNINGS = 341

# Filled by one deterministic bootstrap projection, then frozen.
OUTPUT_SHA256 = "5f18bb505fed64b29a3e319ee8d2d634dbd7c56bad755234d6eecd85f6df8e6d"
OUTPUT_GIT_BLOB = "fb2fb12d050dde7a1b07fb46bed861295adf105a"
OUTPUT_BYTES = 2_938_467
OUTPUT_LF = 62_114


@dataclass(frozen=True)
class Header:
    line: int
    column: int
    message_prefix: str
    code: str | None = None


@dataclass(frozen=True)
class Rule:
    label: str
    old: str
    new: str
    headers: tuple[Header, ...]
    rationale: str
    owner: tuple[str, str]
    occurrences: int = 1


RULES: tuple[Rule, ...] = (
    Rule(
        "raw_differential_chain_rewrite_in_goal",
        """  have hchain :
      (rawDifferential g (γ • τ)).comp (manifoldDeckDerivative γ τ) =
        (mvfderiv 𝓘(ℂ) (g.1 ∘ manifoldDeckMap γ) τ :
          ScalarOneFormValue) := by
    symm
    apply ContinuousLinearMap.ext
    intro v
    simpa only [rawDifferential, manifoldDeckDerivative, manifoldDeckMap,
      mvfderiv, Function.comp_apply, ContinuousLinearMap.comp_apply] using
      congrArg
        (NormedSpace.fromTangentSpace (g.1 (γ • τ)))
        (mfderiv_comp_apply τ hgAt hdeckAt v)
""",
        """  have hchain :
      (rawDifferential g (γ • τ)).comp (manifoldDeckDerivative γ τ) =
        (mvfderiv 𝓘(ℂ) (g.1 ∘ manifoldDeckMap γ) τ :
          ScalarOneFormValue) := by
    symm
    apply ContinuousLinearMap.ext
    intro v
    simp only [rawDifferential, manifoldDeckDerivative, mvfderiv,
      ContinuousLinearMap.comp_apply]
    rw [mfderiv_comp_apply τ hgAt hdeckAt v]
""",
        (Header(28363, 4, "Type mismatch: After simplification, term"),),
        "Preserve manifoldDeckMap so mfderiv_comp_apply rewrites the goal directly.",
        ("probe13_early", "raw_differential_deck_use_mfderiv_comp_apply"),
    ),
    Rule(
        "safe_matter_norm_use_opnorm_smul_le",
        """theorem safeMatterPotential_norm_le_coefficient
    (sector : QSector) (Y : ℝ) :
    ‖safeMatterPotential sector Y‖ ≤ sectorPotentialCoefficient sector := by
  rw [safeMatterPotential, norm_smul]
  calc
    ‖(sectorPotentialCoefficient sector : ℂ)‖ *
          ‖deltaMatterPotential Y‖
        ≤ ‖(sectorPotentialCoefficient sector : ℂ)‖ * 1 :=
      mul_le_mul_of_nonneg_left (deltaMatterPotential_norm_le_one Y)
        (norm_nonneg _)
    _ = sectorPotentialCoefficient sector := by
      simp [abs_of_nonneg (sectorPotentialCoefficient_nonneg sector)]
""",
        """theorem safeMatterPotential_norm_le_coefficient
    (sector : QSector) (Y : ℝ) :
    ‖safeMatterPotential sector Y‖ ≤ sectorPotentialCoefficient sector := by
  calc
    ‖safeMatterPotential sector Y‖ ≤
        ‖(sectorPotentialCoefficient sector : ℂ)‖ *
          ‖deltaMatterPotential Y‖ := by
      simpa only [safeMatterPotential] using
        (ContinuousLinearMap.opNorm_smul_le
          (sectorPotentialCoefficient sector : ℂ)
          (deltaMatterPotential Y))
    _ ≤ ‖(sectorPotentialCoefficient sector : ℂ)‖ * 1 :=
      mul_le_mul_of_nonneg_left (deltaMatterPotential_norm_le_one Y)
        (norm_nonneg _)
    _ = sectorPotentialCoefficient sector := by
      simp [abs_of_nonneg (sectorPotentialCoefficient_nonneg sector)]
""",
        (
            Header(32095, 27, "failed to synthesize instance of type class", "lean.synthInstanceFailed"),
            Header(32094, 74, "unsolved goals"),
        ),
        "Use the one-sided operator-norm scalar bound, which needs IsBoundedSMul rather than NormSMulClass.",
        ("probe13_early", "safe_matter_norm_use_norm_smul_equality"),
    ),
)


FOREIGN_HELPERS: tuple[tuple[str, str, str], ...] = (
    (
        "probe13_early",
        "qym-probe13-early-p12-conditional/qym_probe13_early_p12_conditional.py",
        "5462da0d1e49fc9f5769eeaf9052515cc905cdd55740dc55c3d930992d878210",
    ),
    (
        "probe13_mid",
        "qym-probe13-highleverage-instances/qym_probe13_highleverage_instances.py",
        "e29672a27f2e6421426b73350655b3bae5dca187a8ab2fe39ea023cdf19ec47e",
    ),
    (
        "probe13_50k",
        "qym-probe13-50k50599-p12-reanchored/qym_probe13_50k50599_p12_reanchored.py",
        "a2eacbaebd1f3fddcb865a551613ea8ebbcdf12d74869be2b61c663a0891ed50",
    ),
    (
        "probe13_tail",
        "qym-probe13-tail-p12-direct/qym_probe13_tail_p12_direct.py",
        "11f19ecfabdde4da519321e133fd1a2265bedc7784cdd729e8dd05fbf310cc48",
    ),
)


def sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def git_blob(raw: bytes) -> str:
    return hashlib.sha1(f"blob {len(raw)}\0".encode() + raw).hexdigest()


def shape(raw: bytes) -> dict[str, object]:
    raw.decode("utf-8", errors="strict")
    return {
        "sha256": sha256(raw), "git_blob": git_blob(raw), "bytes": len(raw),
        "lf": raw.count(b"\n"), "cr": b"\r" in raw, "nul": b"\0" in raw,
        "bom": raw.startswith(b"\xef\xbb\xbf"), "terminal_lf": raw.endswith(b"\n"),
    }


def expected_shape(inverse: bool) -> dict[str, object]:
    values = (
        (OUTPUT_SHA256, OUTPUT_GIT_BLOB, OUTPUT_BYTES, OUTPUT_LF)
        if inverse else
        (INPUT_SHA256, INPUT_GIT_BLOB, INPUT_BYTES, INPUT_LF)
    )
    return {
        "sha256": values[0], "git_blob": values[1], "bytes": values[2],
        "lf": values[3], "cr": False, "nul": False, "bom": False,
        "terminal_lf": True,
    }


def unsealed() -> bool:
    return not OUTPUT_SHA256 and not OUTPUT_GIT_BLOB and OUTPUT_BYTES == OUTPUT_LF == 0


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


def resolve_foreign(relative: str) -> Path:
    here = Path(__file__).resolve()
    candidates = (
        here.parents[1] / relative,
        here.parents[2] / "work" / relative,
    )
    hits: list[Path] = []
    for candidate in candidates:
        path = candidate.resolve()
        if path.is_file() and path not in hits:
            hits.append(path)
    if len(hits) != 1:
        raise RuntimeError(f"foreign helper resolution failed: {relative}: {hits}")
    return hits[0]


def load_foreign(name: str, relative: str, expected: str) -> ModuleType:
    path = resolve_foreign(relative)
    raw = path.read_bytes()
    if sha256(raw) != expected:
        raise RuntimeError(f"foreign helper identity mismatch: {name}")
    module_name = "_qym_probe14_foreign_" + name
    spec = importlib.util.spec_from_file_location(module_name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"foreign import spec unavailable: {name}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[module_name] = module
    spec.loader.exec_module(module)
    if sha256(path.read_bytes()) != expected:
        raise RuntimeError(f"foreign helper changed during import: {name}")
    return module


def spans(text: str, needle: str) -> list[tuple[int, int]]:
    return [(m.start(), m.end()) for m in re.finditer(re.escape(needle), text)]


def collision_audit(text: str, inverse: bool) -> dict[str, object]:
    own: list[tuple[int, int, str]] = []
    for rule in RULES:
        active = rule.new if inverse else rule.old
        found = spans(text, active)
        if len(found) != rule.occurrences:
            raise RuntimeError(f"{rule.label}: active span count {len(found)}")
        for start, end in found:
            line = text.count("\n", 0, start) + 1
            if not 28_000 <= line < 33_000:
                raise RuntimeError(f"{rule.label}: scope violation {line}")
            own.append((start, end, rule.label))
    own.sort()
    if any(left[1] > right[0] for left, right in zip(own, own[1:])):
        raise RuntimeError("own rule overlap")

    foreign_hashes: dict[str, str] = {}
    owner_map: dict[tuple[str, str], object] = {}
    active_foreign: list[tuple[int, int, str, str]] = []
    for name, relative, expected in FOREIGN_HELPERS:
        module = load_foreign(name, relative, expected)
        foreign_hashes[name] = expected
        if getattr(module, "ACTIVATION", False) is not False:
            raise RuntimeError(f"foreign activation drift: {name}")
        for foreign in tuple(getattr(module, "RULES", ())):
            owner_map[(name, foreign.label)] = foreign
            for start, end in spans(text, foreign.new):
                active_foreign.append((start, end, name, foreign.label))

    refinements = []
    expected_owner_overlaps = set()
    for rule in RULES:
        owner = owner_map.get(rule.owner)
        if owner is None or rule.old != owner.new:
            raise RuntimeError(f"{rule.label}: exact active-owner equality missing")
        expected_owner_overlaps.add((rule.label, rule.owner[0], rule.owner[1]))
        refinements.append({"rule": rule.label, "owner": ":".join(rule.owner),
                            "relationship": "probe14_old_equals_active_probe13_new"})

    observed = set()
    if not inverse:
        for a, b, label in own:
            for c, d, name, foreign_label in active_foreign:
                if max(a, c) < min(b, d):
                    observed.add((label, name, foreign_label))
        if observed != expected_owner_overlaps:
            raise RuntimeError(f"foreign overlap contract drift: {sorted(observed)}")

    return {
        "own_spans": len(own), "own_overlap_count": 0,
        "foreign_helper_sha256": foreign_hashes,
        "declared_refinements": refinements,
        "active_owner_overlaps": sorted(observed),
        "undeclared_overlap_count": 0,
    }


def verify_authority(log: bytes, headers: bytes, diagnostics: bytes) -> dict[str, object]:
    for label, raw, expected in (
        ("log", log, LOG_SHA256), ("headers", headers, HEADERS_SHA256),
        ("diagnostics", diagnostics, DIAGNOSTICS_SHA256),
    ):
        if sha256(raw) != expected:
            raise RuntimeError(f"exact Probe13 {label} gate failed")
    rows = [json.loads(line) for line in diagnostics.decode().splitlines() if line]
    errors = [row for row in rows if row.get("severity") == "error"]
    warnings = [row for row in rows if row.get("severity") == "warning"]
    if (len(errors), len(warnings)) != (EXPECTED_ERRORS, EXPECTED_WARNINGS):
        raise RuntimeError("Probe13 diagnostic totals drift")
    claimed = []
    for rule in RULES:
        for header in rule.headers:
            matches = [row for row in errors if row.get("line") == header.line
                       and row.get("column") == header.column
                       and row.get("code") == header.code
                       and str(row.get("message", "")).startswith(header.message_prefix)]
            if len(matches) != 1:
                raise RuntimeError(f"{rule.label}: exact diagnostic ownership drift")
            claimed.append({"rule": rule.label, **header.__dict__})
    if len(headers.decode().splitlines()) != EXPECTED_ERRORS:
        raise RuntimeError("Probe13 header count drift")
    return {"errors": len(errors), "warnings": len(warnings),
            "direct_diagnostics": claimed, "panic": 0, "exit": 1}


def apply_rules(text: str, inverse: bool = False) -> tuple[str, list[dict[str, object]]]:
    rows = []
    ordered = tuple(reversed(RULES)) if inverse else RULES
    for rule in ordered:
        old, new = (rule.new, rule.old) if inverse else (rule.old, rule.new)
        count = text.count(old)
        if count != rule.occurrences:
            raise RuntimeError(f"{rule.label}: exact anchor count {count}")
        text = text.replace(old, new)
        rows.append({"label": rule.label, "inverse": inverse, "occurrences": count,
                     "headers": [header.__dict__ for header in rule.headers],
                     "rationale": rule.rationale,
                     "declared_owner": ":".join(rule.owner)})
    return text, rows


transform = apply_rules


def preflight(paths: tuple[Path, ...]) -> None:
    resolved = tuple(path.resolve() for path in paths)
    if len(set(resolved)) != len(resolved):
        raise RuntimeError("destinations must be distinct")
    for path in resolved:
        if path.exists() or not path.parent.is_dir():
            raise RuntimeError(f"destination must be fresh with existing parent: {path}")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--audit", type=Path, required=True)
    parser.add_argument("--inverse", action="store_true")
    parser.add_argument("--bootstrap-seal", action="store_true")
    parser.add_argument("--probe13-log", type=Path, required=True)
    parser.add_argument("--probe13-error-headers", type=Path, required=True)
    parser.add_argument("--probe13-diagnostics", type=Path, required=True)
    args = parser.parse_args()
    if args.bootstrap_seal != unsealed():
        raise RuntimeError("bootstrap/seal state mismatch")
    if args.inverse and unsealed():
        raise RuntimeError("inverse unavailable before output seal")
    preflight((args.output, args.audit))
    authority = verify_authority(args.probe13_log.read_bytes(),
                                 args.probe13_error_headers.read_bytes(),
                                 args.probe13_diagnostics.read_bytes())
    source_raw = args.input.read_bytes()
    source = source_raw.decode("utf-8", errors="strict")
    actual_source = shape(source_raw)
    expected_source = expected_shape(args.inverse)
    if not unsealed() and actual_source != expected_source:
        raise RuntimeError(f"source identity mismatch: {actual_source}")
    if unsealed() and actual_source != expected_shape(False):
        raise RuntimeError("bootstrap exact Probe13 source mismatch")
    before = trust(source)
    if any(before.values()):
        raise RuntimeError(f"source trust0 failure: {before}")
    collisions = collision_audit(source, args.inverse)
    result, rows = apply_rules(source, args.inverse)
    result_raw = result.encode()
    actual_result = shape(result_raw)
    if unsealed():
        if any((actual_result["cr"], actual_result["nul"], actual_result["bom"])) \
                or not actual_result["terminal_lf"]:
            raise RuntimeError("bootstrap result shape failure")
    elif actual_result != expected_shape(not args.inverse):
        raise RuntimeError(f"result identity mismatch: {actual_result}")
    after = trust(result)
    if before != after or any(after.values()):
        raise RuntimeError(f"trust drift: {before} -> {after}")
    restored, _ = apply_rules(result, not args.inverse)
    if restored.encode() != source_raw:
        raise RuntimeError("byte-exact opposite projection failed")
    record = {
        "schema": SCHEMA,
        "status": "STATIC_PASS_EXACT_P13_NOT_LEAN_EXECUTED",
        "activation": ACTIVATION, "promotion": False,
        "mode": "inverse" if args.inverse else "forward",
        "authority": authority, "source": actual_source, "result": actual_result,
        "repair_families": len(RULES),
        "repair_occurrences": sum(rule.occurrences for rule in RULES),
        "diagnostic_ownership_records": sum(len(rule.headers) for rule in RULES),
        "rules": rows, "collision_audit": collisions,
        "inverse_byte_equal": True, "trust": after,
        "execution": {"lean": False, "lake": False, "git": False,
                      "network": False, "remote": False,
                      "repository_source_mutation": False},
    }
    result_bytes = result.encode()
    audit_bytes = (json.dumps(record, indent=2, sort_keys=True) + "\n").encode()
    args.output.write_bytes(result_bytes)
    args.audit.write_bytes(audit_bytes)
    print(json.dumps({"result": actual_result, "families": len(RULES)}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
