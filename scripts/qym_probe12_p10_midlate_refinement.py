#!/usr/bin/env python3
"""Declared downstream refinement of three active Probe10 midlate rules.

The terminal Probe10 run shows that three midlate replacements survived with
new diagnostics at lines 34069 and 34157 through 34167.  This helper refines
those exact active replacements rather than pretending to be collision-free.
Its owner-rule equalities and span overlap are enumerated and required; every
other equality or overlap fails closed.  The transform is exact-P10 guarded,
reversible, trust0, and activation-disabled.  It never invokes Lean, Lake,
Git, the network, a remote API, or a canonical repository source.
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

SCHEMA = "qym-probe12-p10-midlate-refinement-v1-exact-terminal-probe10"
INPUT_SHA256 = "ef19b4f666bd7238164aec7795e10c3f802d9a3e49e5d5f617cc09d4cbe617dc"
INPUT_GIT_BLOB = "496c24e5a90d1f72c66bb03fcc9d3565a06f4b2e"
INPUT_BYTES = 2_923_612
INPUT_LF = 61_783
LOG_SHA256 = "0fa01861e0984e1e45107a46789d894f33d2bbd4a035d9dbaa29060956ab3ad2"
HEADERS_SHA256 = "b1130e19aa9ca16b044eeab07ebf762c0cb2bdfe46c0b7d242ef68b0c151a7a5"
DIAGNOSTICS_SHA256 = "b51f3cc940634dc1eba28003770ae750f8621c4452483f27fdf464188591c43a"

# Sealed after one deterministic in-memory projection.
OUTPUT_SHA256 = "6c6c5c7a0d6520cf1d2a5b7f4b299ec2ec263cae8ffd17b862c47b1c0889b947"
OUTPUT_GIT_BLOB = "b8de2f819b1e4fd0ae4acd83a7ca5597a96f3bfc"
OUTPUT_BYTES = 2_924_033
OUTPUT_LF = 61_788

FOREIGN_HELPERS: dict[str, tuple[str, str]] = {
    "qym_probe10_earlytail_static.py": (
        "5d7c848db8b8ec238bbdaad29bc5532ae0020f134846d16be064a78372c58434",
        "new",
    ),
    "qym_probe10_midlate_static.py": (
        "42d8f76c68b19aac520d15659c71d02db2e1beb397cfe0865bcdaf436e885be0",
        "new",
    ),
    "qym_probe10_late_static.py": (
        "d1c9aef94af3efac77ab5b9b87b2851adbc3eac3fcf7f18e5cc9695a61b7bccd",
        "new",
    ),
    "qym_probe10_extendofnorm_instances.py": (
        "b7942ba8d0ae94dd2827f5a59560a81a291482880c8716df299cc13dbac246bb",
        "new",
    ),
    "qym_probe11_early_frontier_static.py": (
        "9177e4fd6aa03215aec4728415d095e7e099594f6bc12facbf5a2fd879175b9a",
        "old",
    ),
    "qym_probe11_mid_p10_authority.py": (
        "f2adebd8803e40df538a8b85401ea5a26af4585aefe521135c77dde8576a1fc6",
        "old",
    ),
    "qym_probe11_tail_p10_conditional.py": (
        "e76d0830315918d8d51c5063048b0f85ad9f4a68c8dffa2dbab19da25a9aae49",
        "old",
    ),
    "qym_probe11_earlymid_p10_conditional.py": (
        "683e740e96970dd4ca53c51016f30839a4ead5c641c7c8619f5b85733e9612e6",
        "old",
    ),
}
EXPECTED_FOREIGN_RULE_FAMILIES = 79
OWNER_HELPER = "qym_probe10_midlate_static.py"


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
    precedent: str
    provenance: str
    occurrences: int = 1


RULES: tuple[Rule, ...] = (
    Rule(
        "polygon_edge_pairing_set_open_pointwise_refinement",
        """theorem polygonEdge_pairing_set (e : PolygonEdge) :
    ((e.pairingElement : SL(2, ℤ)) • polygonEdgeSet e : Set ℍ) =
      polygonEdgeSet e.paired := by
  exact gammaTwoActualPolygonEdgePairing_set e
""",
        """open scoped Pointwise in
theorem polygonEdge_pairing_set (e : PolygonEdge) :
    ((e.pairingElement : SL(2, ℤ)) • polygonEdgeSet e : Set ℍ) =
      polygonEdgeSet e.paired := by
  exact gammaTwoActualPolygonEdgePairing_set e
""",
        (
            Header(
                34069,
                5,
                "failed to synthesize instance of type class",
                "lean.synthInstanceFailed",
            ),
        ),
        "Retain Probe10's result ascription and locally activate the scoped Set pointwise-action instance.",
        "The exit-zero Mock2_FunctionalAnalysis producer has Pointwise open globally at line 283 and proves the same set action at lines 8079-8097.",
        "Exact terminal-Probe10 survivor of polygon_edge_pairing_set_result_ascription.",
    ),
    Rule(
        "smooth_compact_weight_core_namespace_accessor_refinement",
        """theorem smoothCompactWeightCore_hasMultiplierMatchedPolygonTrace
    {k : ℤ} {M : HalfIntegralMultiplier GammaTwo k}
    (u : Mock2FA.PaperCorrections.AutomorphicSobolev.SmoothCompactCoreGeometry.SmoothCompactWeightCore M) :
    HasMultiplierMatchedPolygonTrace M u.1.toSection := by
  apply hasMultiplierMatchedPolygonTrace_of_covariance M u.1.toSection
  intro γ z
  simpa only using u.1.covariance γ z
""",
        """theorem smoothCompactWeightCore_hasMultiplierMatchedPolygonTrace
    {k : ℤ} {M : HalfIntegralMultiplier GammaTwo k}
    (u : Mock2FA.PaperCorrections.AutomorphicSobolev.SmoothCompactCoreGeometry.SmoothCompactWeightCore M) :
    HasMultiplierMatchedPolygonTrace M
      (Mock2FA.PaperCorrections.AutomorphicSobolev.SmoothCompactCoreGeometry.SmoothCompactWeightCore.toSection u) := by
  apply hasMultiplierMatchedPolygonTrace_of_covariance M
    (Mock2FA.PaperCorrections.AutomorphicSobolev.SmoothCompactCoreGeometry.SmoothCompactWeightCore.toSection u)
  intro γ z
  simpa only using
    (Mock2FA.PaperCorrections.AutomorphicSobolev.SmoothCompactCoreGeometry.SmoothCompactWeightCore.covariance u γ z)
""",
        (
            Header(
                34157,
                43,
                "Invalid field \u0060toSection\u0060: The environment does not contain \u0060Subtype.toSection\u0060, so it is not possible to project the field \u0060toSection\u0060 from an expression",
                "lean.invalidField",
            ),
            Header(
                34158,
                61,
                "Invalid field \u0060toSection\u0060: The environment does not contain \u0060Subtype.toSection\u0060, so it is not possible to project the field \u0060toSection\u0060 from an expression",
                "lean.invalidField",
            ),
            Header(
                34160,
                23,
                "Invalid field \u0060covariance\u0060: The environment does not contain \u0060Subtype.covariance\u0060, so it is not possible to project the field \u0060covariance\u0060 from an expression",
                "lean.invalidField",
            ),
        ),
        "Apply the namespace functions to the SmoothCompactWeightCore subtype; u.1 is already a WeightSection and has no toSection or covariance namespace fields.",
        "Mock2_FunctionalAnalysis.lean lines 10731-10748 define SmoothCompactWeightCore.toSection and SmoothCompactWeightCore.covariance, and later exit-zero uses call them explicitly.",
        "Exact terminal-Probe10 survivor of smooth_compact_weight_core_unwrap_subtype.",
    ),
    Rule(
        "inverse_eta_core_namespace_accessor_refinement",
        """    HasMultiplierMatchedPolygonTrace
      (inverseEtaMultiplier GammaTwo) u.1.toSection :=
  smoothCompactWeightCore_hasMultiplierMatchedPolygonTrace u
""",
        """    HasMultiplierMatchedPolygonTrace
      (inverseEtaMultiplier GammaTwo)
      (Mock2FA.PaperCorrections.AutomorphicSobolev.SmoothCompactCoreGeometry.SmoothCompactWeightCore.toSection u) :=
  smoothCompactWeightCore_hasMultiplierMatchedPolygonTrace u
""",
        (
            Header(
                34167,
                42,
                "Invalid field \u0060toSection\u0060: The environment does not contain \u0060Subtype.toSection\u0060, so it is not possible to project the field \u0060toSection\u0060 from an expression",
                "lean.invalidField",
            ),
        ),
        "Use the same exact namespace accessor in the inverse-eta specialization statement.",
        "Mock2_FunctionalAnalysis.lean lines 10731-10734 define the exact toSection accessor.",
        "Exact terminal-Probe10 survivor of inverse_eta_core_unwrap_subtype.",
    ),
)


# Each permitted overlap is a downstream refinement of one exact active
# Probe10-midlate new anchor.  No additional equality or span overlap is legal.
DECLARED_REFINEMENTS: dict[str, dict[str, str]] = {
    "polygon_edge_pairing_set_open_pointwise_refinement": {
        "helper": OWNER_HELPER,
        "rule": "polygon_edge_pairing_set_result_ascription",
        "relationship": "owner_active_new_is_strict_prefix_of_refinement_old",
    },
    "smooth_compact_weight_core_namespace_accessor_refinement": {
        "helper": OWNER_HELPER,
        "rule": "smooth_compact_weight_core_unwrap_subtype",
        "relationship": "refinement_old_equals_owner_active_new",
    },
    "inverse_eta_core_namespace_accessor_refinement": {
        "helper": OWNER_HELPER,
        "rule": "inverse_eta_core_unwrap_subtype",
        "relationship": "refinement_old_equals_owner_active_new",
    },
}


def sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def git_blob(raw: bytes) -> str:
    return hashlib.sha1(
        f"blob {len(raw)}\0".encode("ascii") + raw
    ).hexdigest()


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


def sentinels_unsealed() -> bool:
    return (
        OUTPUT_SHA256 == ""
        and OUTPUT_GIT_BLOB == ""
        and OUTPUT_BYTES == 0
        and OUTPUT_LF == 0
    )


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
    actual: dict[str, object],
    expected: dict[str, object],
    *,
    unsealed: bool = False,
) -> None:
    if unsealed:
        for key in ("cr", "nul", "bom", "terminal_lf"):
            if actual[key] != expected[key]:
                raise RuntimeError(f"unsealed structural shape mismatch: {key}")
        return
    if actual != expected:
        raise RuntimeError(f"shape mismatch: {actual} != {expected}")


def parse_diagnostics(raw: bytes) -> list[dict[str, object]]:
    return [
        json.loads(line)
        for line in raw.decode("utf-8", errors="strict").splitlines()
    ]


def verify_authority(
    log_raw: bytes,
    header_raw: bytes,
    diagnostics_raw: bytes,
) -> list[dict[str, object]]:
    identities = {
        "log": (sha256(log_raw), LOG_SHA256),
        "error_headers": (sha256(header_raw), HEADERS_SHA256),
        "diagnostics": (sha256(diagnostics_raw), DIAGNOSTICS_SHA256),
    }
    for label, (actual, expected) in identities.items():
        if actual != expected:
            raise RuntimeError(
                f"Probe10 {label} identity mismatch: {actual} != {expected}"
            )

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
            header_matches = [
                line for line in header_lines if pattern.match(line)
            ]
            diagnostic_matches = [
                row
                for row in rows
                if row.get("severity") == "error"
                and row.get("line") == header.line
                and row.get("column") == header.column
                and row.get("code") == header.code
                and str(row.get("message", "")).startswith(header.message)
            ]
            if len(header_matches) != 1 or len(diagnostic_matches) != 1:
                raise RuntimeError(
                    f"{rule.label}: P10 authority mapping mismatch at "
                    f"{header.line}:{header.column}"
                )
            verified.append(
                {
                    "rule": rule.label,
                    "line": header.line,
                    "column": header.column,
                    "code": header.code,
                    "message": header.message,
                    "kind": "surviving_active_probe10_rule_refinement",
                    "owner": DECLARED_REFINEMENTS[rule.label],
                    "provenance": rule.provenance,
                }
            )
    if len(verified) != 5:
        raise RuntimeError(f"expected 5 direct diagnostics, got {len(verified)}")
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
    name = "_qym_probe12_midlate_refinement_" + hashlib.sha256(
        str(path.resolve()).encode("utf-8")
    ).hexdigest()
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot import foreign helper: {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def apply_rules(
    text: str,
    inverse: bool = False,
) -> tuple[str, list[dict[str, object]]]:
    audits: list[dict[str, object]] = []
    ordered = tuple(reversed(RULES)) if inverse else RULES
    for rule in ordered:
        old, new = (rule.new, rule.old) if inverse else (rule.old, rule.new)
        count = text.count(old)
        if count != rule.occurrences:
            raise RuntimeError(
                f"{rule.label}: exact anchor count {count}, "
                f"expected {rule.occurrences}"
            )
        text = text.replace(old, new)
        audits.append(
            {
                "label": rule.label,
                "direction": "inverse" if inverse else "forward",
                "occurrences": count,
                "headers": [header.__dict__ for header in rule.headers],
                "rationale": rule.rationale,
                "precedent": rule.precedent,
                "provenance": rule.provenance,
                "declared_refinement": DECLARED_REFINEMENTS[rule.label],
            }
        )
    return text, audits


transform = apply_rules


def audit_internal_independence(
    source_text: str,
    *,
    inverse: bool,
) -> dict[str, object]:
    found_spans: list[tuple[int, int, str]] = []
    for rule in RULES:
        active = rule.new if inverse else rule.old
        found = spans(source_text, active)
        if len(found) != rule.occurrences:
            raise RuntimeError(f"own active span mismatch: {rule.label}")
        found_spans.extend((start, end, rule.label) for start, end in found)
    overlaps: list[dict[str, object]] = []
    for index, (left_start, left_end, left) in enumerate(found_spans):
        for right_start, right_end, right in found_spans[index + 1:]:
            if max(left_start, right_start) < min(left_end, right_end):
                overlaps.append(
                    {
                        "left": left,
                        "right": right,
                        "left_span": [left_start, left_end],
                        "right_span": [right_start, right_end],
                    }
                )
    if overlaps:
        raise RuntimeError(f"refinement rules overlap each other: {overlaps}")
    return {
        "own_active_spans_checked": len(found_spans),
        "own_span_overlaps": overlaps,
        "pairwise_independent": True,
    }


def audit_declared_foreign_overlaps(
    canonical_p10_text: str,
    helper_paths: list[Path],
) -> dict[str, object]:
    by_name: dict[str, Path] = {}
    for path in helper_paths:
        if path.name in by_name:
            raise RuntimeError(f"duplicate foreign helper basename: {path.name}")
        by_name[path.name] = path
    if set(by_name) != set(FOREIGN_HELPERS):
        raise RuntimeError(
            "foreign helper set mismatch: "
            f"{sorted(by_name)} != {sorted(FOREIGN_HELPERS)}"
        )

    own_spans: list[tuple[int, int, str]] = []
    for rule in RULES:
        found = spans(canonical_p10_text, rule.old)
        if len(found) != rule.occurrences:
            raise RuntimeError(
                f"refinement old span mismatch on canonical P10: {rule.label}"
            )
        own_spans.extend((start, end, rule.label) for start, end in found)

    modules: dict[str, ModuleType] = {}
    identities: dict[str, dict[str, str]] = {}
    rule_index: dict[tuple[str, str], object] = {}
    foreign_families = 0
    foreign_spans_checked = 0
    observed_overlaps: list[dict[str, object]] = []
    observed_equalities: list[dict[str, str]] = []
    for name, (expected_sha, active_variant) in FOREIGN_HELPERS.items():
        path = by_name[name]
        if not path.is_file():
            raise RuntimeError(f"foreign helper missing: {path}")
        actual_sha = sha256(path.read_bytes())
        if actual_sha != expected_sha:
            raise RuntimeError(
                f"foreign helper identity mismatch: {name}: "
                f"{actual_sha} != {expected_sha}"
            )
        module = load_helper(path)
        modules[name] = module
        foreign_rules = getattr(module, "RULES", None)
        if foreign_rules is None:
            raise RuntimeError(f"foreign helper has no RULES: {name}")
        identities[name] = {
            "sha256": actual_sha,
            "active_variant": active_variant,
        }
        for foreign in foreign_rules:
            foreign_families += 1
            foreign_label = getattr(foreign, "label")
            foreign_old = getattr(foreign, "old")
            foreign_new = getattr(foreign, "new")
            foreign_active = (
                foreign_new if active_variant == "new" else foreign_old
            )
            expected_count = getattr(foreign, "occurrences", 1)
            found = spans(canonical_p10_text, foreign_active)
            if len(found) != expected_count:
                raise RuntimeError(
                    f"foreign active span mismatch: {name}:{foreign_label}: "
                    f"{len(found)} != {expected_count}"
                )
            foreign_spans_checked += len(found)
            rule_index[(name, foreign_label)] = foreign
            for own in RULES:
                for own_kind, own_anchor in (("old", own.old), ("new", own.new)):
                    for foreign_kind, foreign_anchor in (
                        ("old", foreign_old),
                        ("new", foreign_new),
                    ):
                        if own_anchor == foreign_anchor:
                            observed_equalities.append(
                                {
                                    "own": own.label,
                                    "own_variant": own_kind,
                                    "foreign_helper": name,
                                    "foreign_rule": foreign_label,
                                    "foreign_variant": foreign_kind,
                                }
                            )
            for foreign_start, foreign_end in found:
                for own_start, own_end, own_label in own_spans:
                    if max(foreign_start, own_start) < min(
                        foreign_end, own_end
                    ):
                        observed_overlaps.append(
                            {
                                "own": own_label,
                                "foreign_helper": name,
                                "foreign_rule": foreign_label,
                                "own_span": [own_start, own_end],
                                "foreign_span": [foreign_start, foreign_end],
                            }
                        )
    if foreign_families != EXPECTED_FOREIGN_RULE_FAMILIES:
        raise RuntimeError(
            f"foreign rule-family count {foreign_families} != "
            f"{EXPECTED_FOREIGN_RULE_FAMILIES}"
        )

    expected_keys = {
        (
            own_label,
            declaration["helper"],
            declaration["rule"],
        )
        for own_label, declaration in DECLARED_REFINEMENTS.items()
    }
    observed_keys = {
        (
            item["own"],
            item["foreign_helper"],
            item["foreign_rule"],
        )
        for item in observed_overlaps
    }
    undeclared_overlap_keys = observed_keys - expected_keys
    missing_declared_overlap_keys = expected_keys - observed_keys
    if undeclared_overlap_keys or missing_declared_overlap_keys:
        raise RuntimeError(
            "declared overlap mismatch: "
            f"undeclared={sorted(undeclared_overlap_keys)}, "
            f"missing={sorted(missing_declared_overlap_keys)}"
        )

    allowed_equality_keys = {
        (
            "smooth_compact_weight_core_namespace_accessor_refinement",
            "old",
            OWNER_HELPER,
            "smooth_compact_weight_core_unwrap_subtype",
            "new",
        ),
        (
            "inverse_eta_core_namespace_accessor_refinement",
            "old",
            OWNER_HELPER,
            "inverse_eta_core_unwrap_subtype",
            "new",
        ),
    }
    equality_keys = {
        (
            item["own"],
            item["own_variant"],
            item["foreign_helper"],
            item["foreign_rule"],
            item["foreign_variant"],
        )
        for item in observed_equalities
    }
    if equality_keys != allowed_equality_keys:
        raise RuntimeError(
            f"declared exact equality mismatch: {sorted(equality_keys)}"
        )

    relationship_checks: list[dict[str, object]] = []
    for own in RULES:
        declaration = DECLARED_REFINEMENTS[own.label]
        foreign = rule_index[
            (declaration["helper"], declaration["rule"])
        ]
        foreign_active_new = getattr(foreign, "new")
        relationship = declaration["relationship"]
        if relationship == "refinement_old_equals_owner_active_new":
            valid = own.old == foreign_active_new
        elif relationship == "owner_active_new_is_strict_prefix_of_refinement_old":
            valid = (
                own.old.startswith(foreign_active_new)
                and own.old != foreign_active_new
            )
        else:
            raise RuntimeError(f"unknown relationship: {relationship}")
        if not valid:
            raise RuntimeError(
                f"declared refinement relationship failed: {own.label}"
            )
        relationship_checks.append(
            {
                "own": own.label,
                "owner_helper": declaration["helper"],
                "owner_rule": declaration["rule"],
                "relationship": relationship,
                "valid": True,
            }
        )

    return {
        "helper_identities": identities,
        "foreign_rule_families_checked": foreign_families,
        "foreign_active_spans_checked": foreign_spans_checked,
        "declared_overlap_count": len(observed_overlaps),
        "declared_exact_equality_count": len(observed_equalities),
        "declared_overlaps": observed_overlaps,
        "declared_exact_equalities": observed_equalities,
        "relationship_checks": relationship_checks,
        "undeclared_overlap_count": 0,
        "undeclared_exact_equality_count": 0,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--probe10-log", type=Path, required=True)
    parser.add_argument("--probe10-error-headers", type=Path, required=True)
    parser.add_argument("--probe10-diagnostics", type=Path, required=True)
    parser.add_argument(
        "--foreign-helper",
        type=Path,
        action="append",
        required=True,
    )
    parser.add_argument("--audit", type=Path, required=True)
    parser.add_argument(
        "--mode",
        choices=("forward", "inverse"),
        default="forward",
    )
    parser.add_argument("--bootstrap-seal", action="store_true")
    args = parser.parse_args()
    inverse = args.mode == "inverse"

    if args.bootstrap_seal and not sentinels_unsealed():
        raise RuntimeError("bootstrap seal refused: output identity already sealed")
    if not args.bootstrap_seal and sentinels_unsealed():
        raise RuntimeError("output identity unsealed; bootstrap projection required")

    source = args.input.read_bytes()
    source_shape = shape(source)
    check_shape(
        source_shape,
        output_expected() if inverse else input_expected(),
        unsealed=args.bootstrap_seal and inverse,
    )
    diagnostic_map = verify_authority(
        args.probe10_log.read_bytes(),
        args.probe10_error_headers.read_bytes(),
        args.probe10_diagnostics.read_bytes(),
    )
    source_text = source.decode("utf-8", errors="strict")
    internal = audit_internal_independence(source_text, inverse=inverse)
    if inverse:
        canonical_p10_text, _ = apply_rules(source_text, inverse=True)
    else:
        canonical_p10_text = source_text
    declared_overlap_audit = audit_declared_foreign_overlaps(
        canonical_p10_text,
        args.foreign_helper,
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
        raise RuntimeError("opposite transform failed byte-exact restoration")
    if args.output.exists() or args.audit.exists():
        raise RuntimeError("refusing to overwrite output or audit")

    record = {
        "schema": SCHEMA,
        "status": "STATIC_PASS_DECLARED_PROBE10_MIDLATE_REFINEMENT_NOT_LEAN_EXECUTED",
        "activation": False,
        "promotion": False,
        "mode": args.mode,
        "authority": {
            "probe10_run_id": 31973408809,
            "probe10_job_id": 95229227905,
            "probe10_head_sha": "0957f9b925663bc78b76c7207084fb6199eb60de",
            "probe10_result_sha256": "0a908f0ae2bae582285d3d48c5ccb30829c2225af2b397b5ffd1a499798d279d",
            "artifact_id": 9270510078,
            "artifact_name": "qym-repair-probe10-integrated-0957f9b925663bc78b76c7207084fb6199eb60de-attempt1",
            "artifact_api_size": 10487379,
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
            "candidate_lines": [34069, 34167],
            "surviving_active_probe10_midlate_rules_only": True,
            "declared_owner_helper": OWNER_HELPER,
            "declared_refinements": DECLARED_REFINEMENTS,
            "undeclared_collisions_fail_closed": True,
            "cascade_diagnostics_selected": False,
        },
        "source": source_shape,
        "result": result_shape,
        "repair_families": len(RULES),
        "repair_occurrences": sum(
            item["occurrences"] for item in rule_audit
        ),
        "direct_diagnostics": len(diagnostic_map),
        "diagnostic_map": diagnostic_map,
        "rules": rule_audit,
        "selected_exact_probe10_lines": sorted(
            {header.line for rule in RULES for header in rule.headers}
        ),
        "internal_independence_audit": internal,
        "declared_foreign_overlap_audit": declared_overlap_audit,
        "inverse_byte_equal": True,
        "trust": after_trust,
        "static_evidence": {
            "pointwise_scope_precedent": "Mock2_FunctionalAnalysis exit-zero line 283 and lines 8079-8097",
            "smooth_compact_core_accessors": "Mock2_FunctionalAnalysis.lean lines 10731-10748",
            "full_goal_evidence": {
                "34069": "missing HSMul SL(2,Z) (Set UpperHalfPlane)",
                "34157-34160": "u.1 has type WeightSection; Subtype has no toSection or covariance field",
                "34167": "u.1 has type inverse-eta WeightSection; Subtype has no toSection field",
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
        json.dumps(record, indent=2) + "\n",
        encoding="utf-8",
        newline="\n",
    )
    print(json.dumps(record, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
