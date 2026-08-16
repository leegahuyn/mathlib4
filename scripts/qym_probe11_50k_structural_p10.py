#!/usr/bin/env python3
"""Bounded exact-P10 structural audit and local API producer repair.

The carrier mismatch between the P2 effective quotient and Mock2's original
quotient is deliberately not rewritten: repairing it requires an explicit
equivalence plus topology, measure, and bundle transport.  This helper changes
only the two independent smooth-trivialization producer calls whose exact P10
diagnostics prove that the current Mathlib API accepts the point as its sole
explicit argument.  It is byte-locked, reversible, trust0, and inactive.
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

SCHEMA = "qym-probe11-50k-structural-p10-v1-exact-terminal-probe10"
INPUT_SHA256 = "ef19b4f666bd7238164aec7795e10c3f802d9a3e49e5d5f617cc09d4cbe617dc"
INPUT_GIT_BLOB = "496c24e5a90d1f72c66bb03fcc9d3565a06f4b2e"
INPUT_BYTES = 2_923_612
INPUT_LF = 61_783
LOG_SHA256 = "0fa01861e0984e1e45107a46789d894f33d2bbd4a035d9dbaa29060956ab3ad2"
HEADERS_SHA256 = "b1130e19aa9ca16b044eeab07ebf762c0cb2bdfe46c0b7d242ef68b0c151a7a5"
DIAGNOSTICS_SHA256 = "b51f3cc940634dc1eba28003770ae750f8621c4452483f27fdf464188591c43a"

# Sealed after the one deterministic bootstrap projection.
OUTPUT_SHA256 = "7bffcf2a89f8b616eee61ef0ed64b91e9ede23ae22daa325ac3fa4f00322e8b8"
OUTPUT_GIT_BLOB = "39e0855d15d69b99a37f5c4de504c4256f2ba9c8"
OUTPUT_BYTES = 2_923_542
OUTPUT_LF = 61_781


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
    headers: tuple[Header, ...]
    declarations: tuple[str, ...]
    rationale: str
    occurrences: int = 1


RULES: tuple[Rule, ...] = (
    Rule(
        "ext_chart_target_neighborhood_use_current_point_only_api",
        "      [extChartAt_target_mem_nhdsWithin\n"
        "        (𝓘(ℂ).prod 𝓘(ℂ)) ",
        "      [extChartAt_target_mem_nhdsWithin ",
        (
            Header(51276, 7, "Function expected at"),
            Header(51309, 7, "Function expected at"),
        ),
        (
            "inverseEtaTotalTrivialization_contMDiff",
            "inverseEtaTotalTrivialization_symm_contMDiff",
        ),
        "The exact diagnostic says the theorem is already a neighborhood-membership proposition after the first supplied argument: the current API's sole explicit argument is the point, so the old code mistakenly binds the model expression as that point and then applies the real point as an invalid second argument.  The model is inferred from the installed chart.",
        occurrences=2,
    ),
)


FOREIGN_HELPERS: tuple[tuple[str, str, str], ...] = (
    ("probe10_earlytail", "qym-probe10-earlytail-static/qym_probe10_earlytail_static.py", "5d7c848db8b8ec238bbdaad29bc5532ae0020f134846d16be064a78372c58434"),
    ("probe10_midlate", "qym-probe10-midlate-static/qym_probe10_midlate_static.py", "42d8f76c68b19aac520d15659c71d02db2e1beb397cfe0865bcdaf436e885be0"),
    ("probe10_late", "qym-probe10-late-static/qym_probe10_late_static.py", "d1c9aef94af3efac77ab5b9b87b2851adbc3eac3fcf7f18e5cc9695a61b7bccd"),
    ("probe10_extendofnorm", "qym-probe10-extendofnorm-instances/qym_probe10_extendofnorm_instances.py", "b7942ba8d0ae94dd2827f5a59560a81a291482880c8716df299cc13dbac246bb"),
    ("probe11_mid_p10", "qym-probe11-mid-p10-authority/qym_probe11_mid_p10_authority.py", "f2adebd8803e40df538a8b85401ea5a26af4585aefe521135c77dde8576a1fc6"),
    ("probe11_tail_p10", "qym-probe11-tail-p10-conditional/qym_probe11_tail_p10_conditional.py", "e76d0830315918d8d51c5063048b0f85ad9f4a68c8dffa2dbab19da25a9aae49"),
    ("probe11_early_frontier_p10", "qym-probe11-early-frontier-static/qym_probe11_early_frontier_static.py", "9177e4fd6aa03215aec4728415d095e7e099594f6bc12facbf5a2fd879175b9a"),
    ("probe11_40k_p10", "qym-probe11-40k-p10-conditional/qym_probe11_40k_p10_conditional.py", "6765e05b8681e4d7e13bc735c4d37ea038c75423a7d5ebc1ad73b179a99e0052"),
)


STRUCTURAL_BLOCKERS: tuple[dict[str, object], ...] = (
    {
        "rank": 1,
        "producer": "P3InverseEtaQuotientBundleExtension.InverseEtaBase",
        "declaration_line": 47619,
        "anchor": "abbrev InverseEtaBase := Mock2.Definition15Geometry.X",
        "first_cluster_failure": "50035:78",
        "impact": "The P3 quotient bundle is based on Mock2.Definition15Geometry.X, while the P2 intrinsic stage is a subtype of the faithful-effective GammaTwoQuotient.  At least the 50035-50439 family and 51837 directly substitute the latter where the former is required.",
        "repair_status": "BLOCKED_NO_LOCAL_REPAIR",
        "required_design": "Construct and prove a canonical equivalence/homeomorphism between the original and effective orbit quotients, then transport topology, measurable structure, measures, projection fibres, sections, and the line-bundle trivialization.",
    },
    {
        "rank": 2,
        "producer": "P3InverseEtaSmoothTrivializationClosureExtension.inverseEtaBaseChartedSpaceH",
        "declaration_line": 51094,
        "first_cluster_failure": "51096:2",
        "impact": "The P2 ChartedSpace and HasGroupoid/IsManifold producers are applied directly to the non-definitionally-equal InverseEtaBase, producing the 51096-51130 atlas family and poisoning downstream transported-chart instance synthesis.",
        "repair_status": "BLOCKED_BY_MISSING_BASE_EQUIVALENCE",
        "required_design": "Transport the P2 atlas and groupoid/manifold proofs along the explicit base homeomorphism; direct assignment is not type-correct.",
    },
    {
        "rank": 3,
        "producer": "inverseEtaTotalTrivialization_contMDiff / inverseEtaTotalTrivialization_symm_contMDiff",
        "declaration_lines": [51264, 51282],
        "direct_failures": ["51276:7", "51309:7"],
        "impact": "The two forward/inverse smoothness producers use an obsolete extra explicit model argument and feed several later smooth trivialization/projection/section declarations.",
        "repair_status": "LOCAL_API_REPAIR_SEALED_INACTIVE",
        "rules": ["ext_chart_target_neighborhood_use_current_point_only_api"],
    },
)


def shape(raw: bytes) -> dict[str, object]:
    raw.decode("utf-8", errors="strict")
    return {"sha256": sha256(raw), "git_blob": git_blob(raw), "bytes": len(raw),
            "lf": raw.count(b"\n"), "cr": b"\r" in raw, "nul": b"\0" in raw,
            "bom": raw.startswith(b"\xef\xbb\xbf"), "terminal_lf": raw.endswith(b"\n")}


def trust(text: str) -> dict[str, int]:
    return {"sorry": len(re.findall(r"\bsorry\b", text)),
            "admit": len(re.findall(r"\badmit\b", text)),
            "native_decide": len(re.findall(r"\bnative_decide\b", text)),
            "Lean.ofReduceBool": text.count("Lean.ofReduceBool"),
            "axiom_declaration": len(re.findall(r"(?m)^\s*axiom\s+", text)),
            "unsafe_declaration": len(re.findall(r"(?m)^\s*unsafe\s+", text)),
            "maxHeartbeats_zero": len(re.findall(r"set_option\s+maxHeartbeats\s+0\b", text))}


def input_expected() -> dict[str, object]:
    return {"sha256": INPUT_SHA256, "git_blob": INPUT_GIT_BLOB,
            "bytes": INPUT_BYTES, "lf": INPUT_LF, "cr": False, "nul": False,
            "bom": False, "terminal_lf": True}


def output_expected() -> dict[str, object]:
    return {"sha256": OUTPUT_SHA256, "git_blob": OUTPUT_GIT_BLOB,
            "bytes": OUTPUT_BYTES, "lf": OUTPUT_LF, "cr": False, "nul": False,
            "bom": False, "terminal_lf": True}


def sentinels_unsealed() -> bool:
    return OUTPUT_SHA256 == "" and OUTPUT_GIT_BLOB == "" and OUTPUT_BYTES == 0 and OUTPUT_LF == 0


def check_shape(actual: dict[str, object], expected: dict[str, object], *, unsealed: bool = False) -> None:
    keys = ("cr", "nul", "bom", "terminal_lf") if unsealed else tuple(expected)
    if any(actual[key] != expected[key] for key in keys):
        raise RuntimeError(f"shape mismatch: {actual} != {expected}")


def verify_authority(log_raw: bytes, header_raw: bytes, diagnostics_raw: bytes) -> tuple[list[dict[str, object]], dict[str, object]]:
    for label, actual, expected in (
        ("log", sha256(log_raw), LOG_SHA256),
        ("headers", sha256(header_raw), HEADERS_SHA256),
        ("diagnostics", sha256(diagnostics_raw), DIAGNOSTICS_SHA256),
    ):
        if actual != expected:
            raise RuntimeError(f"Probe10 {label} identity mismatch: {actual}")
    headers = header_raw.decode("utf-8", errors="strict").splitlines()
    rows = [json.loads(line) for line in diagnostics_raw.decode("utf-8", errors="strict").splitlines()]
    if len(headers) != 255 or sum(row.get("severity") == "error" for row in rows) != 255:
        raise RuntimeError("Probe10 exact error count mismatch")
    if sum(row.get("severity") == "warning" for row in rows) != 343:
        raise RuntimeError("Probe10 exact warning count mismatch")
    cluster = [row for row in rows if row.get("severity") == "error"
               and 50000 <= int(row.get("line", 0)) <= 51837]
    if len(cluster) != 48:
        raise RuntimeError(f"expected 48 exact structural-window errors, got {len(cluster)}")
    mapped: list[dict[str, object]] = []
    for rule in RULES:
        for header in rule.headers:
            pattern = re.compile(
                rf"^PrimalitySheafVerification/QYM\.lean:{header.line}:{header.column}: "
                rf"error: {re.escape(header.message)}"
            )
            hm = [line for line in headers if pattern.match(line)]
            dm = [row for row in rows if row.get("severity") == "error"
                  and row.get("line") == header.line and row.get("column") == header.column
                  and row.get("code") is None
                  and str(row.get("message", "")).startswith(header.message)]
            if len(hm) != 1 or len(dm) != 1:
                raise RuntimeError(f"{rule.label}: authority mapping mismatch at {header.line}:{header.column}")
            mapped.append({"rule": rule.label, **header.__dict__, "kind": "local_API_producer_root"})
    owned_probe10_late = [50755, 50775, 50893, 50914]
    if any(not any(row.get("line") == line for row in cluster) for line in owned_probe10_late):
        raise RuntimeError("expected Probe10-late residual headers missing")
    return mapped, {"window_errors": len(cluster),
                    "probe10_late_owned_errors_excluded": owned_probe10_late,
                    "unowned_window_errors_before_local_helper": len(cluster) - len(owned_probe10_late)}


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
        raise RuntimeError(f"foreign helper identity mismatch: {name}")
    module_name = "_qym_50k_structural_foreign_" + name
    spec = importlib.util.spec_from_file_location(module_name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot import foreign helper: {name}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[module_name] = module
    spec.loader.exec_module(module)
    return module


def audit_collisions(text: str, *, inverse: bool) -> dict[str, object]:
    own: list[tuple[int, int, str]] = []
    for rule in RULES:
        active = rule.new if inverse else rule.old
        found = spans(text, active)
        if len(found) != rule.occurrences:
            raise RuntimeError(f"{rule.label}: active anchor count {len(found)}")
        for start, end in found:
            line = text.count("\n", 0, start) + 1
            if not 50000 <= line <= 51837:
                raise RuntimeError(f"{rule.label}: scope violation at line {line}")
            own.append((start, end, rule.label))
    equalities: list[dict[str, str]] = []
    overlaps: list[dict[str, object]] = []
    identities: dict[str, str] = {}
    foreign_spans = 0
    for name, relative, expected_sha in FOREIGN_HELPERS:
        module = load_foreign(name, relative, expected_sha)
        identities[name] = expected_sha
        for foreign in module.RULES:
            for variant, anchor in (("old", foreign.old), ("new", foreign.new)):
                found = spans(text, anchor)
                foreign_spans += len(found)
                for rule in RULES:
                    for own_variant, own_anchor in (("old", rule.old), ("new", rule.new)):
                        if own_anchor == anchor:
                            equalities.append({"own": rule.label, "own_variant": own_variant,
                                               "foreign": f"{name}:{foreign.label}", "foreign_variant": variant})
                for fstart, fend in found:
                    for ostart, oend, own_label in own:
                        if max(fstart, ostart) < min(fend, oend):
                            overlaps.append({"own": own_label, "foreign": f"{name}:{foreign.label}",
                                             "foreign_variant": variant,
                                             "own_span": [ostart, oend], "foreign_span": [fstart, fend]})
    if equalities or overlaps:
        raise RuntimeError(f"foreign collision: equalities={equalities}, overlaps={overlaps}")
    return {"foreign_helper_sha256": identities, "own_spans_checked": len(own),
            "foreign_active_spans_checked": foreign_spans,
            "exact_anchor_equalities": equalities, "span_overlaps": overlaps}


def verify_blocker_anchors(text: str) -> None:
    for blocker in STRUCTURAL_BLOCKERS[:2]:
        anchor = str(blocker["anchor"]) if "anchor" in blocker else None
        if anchor is not None and text.count(anchor) != 1:
            raise RuntimeError(f"structural blocker anchor mismatch: {blocker['producer']}")
    atlas_anchor = (
        "noncomputable def inverseEtaBaseChartedSpaceH :\n"
        "    ChartedSpace ℍ InverseEtaBase :=\n"
        "  QYM.FullCertification.P2SmoothQuotientAtlasExtension.allCoveringSheetsChartedSpaceH\n"
    )
    if text.count(atlas_anchor) != 1:
        raise RuntimeError("inverseEtaBaseChartedSpaceH producer anchor mismatch")


def apply_rules(text: str, inverse: bool = False) -> tuple[str, list[dict[str, object]]]:
    audits: list[dict[str, object]] = []
    ordered = tuple(reversed(RULES)) if inverse else RULES
    for rule in ordered:
        old, new = (rule.new, rule.old) if inverse else (rule.old, rule.new)
        count = text.count(old)
        if count != rule.occurrences:
            raise RuntimeError(f"{rule.label}: exact anchor count {count}, expected {rule.occurrences}")
        text = text.replace(old, new)
        audits.append({"label": rule.label, "direction": "inverse" if inverse else "forward",
                       "occurrences": count, "headers": [h.__dict__ for h in rule.headers],
                       "declarations": list(rule.declarations), "rationale": rule.rationale})
    return text, audits


transform = apply_rules


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--probe10-log", type=Path, required=True)
    parser.add_argument("--probe10-error-headers", type=Path, required=True)
    parser.add_argument("--probe10-diagnostics", type=Path, required=True)
    parser.add_argument("--audit", type=Path, required=True)
    parser.add_argument("--mode", choices=("forward", "inverse"), default="forward")
    parser.add_argument("--bootstrap-seal", action="store_true")
    args = parser.parse_args()
    inverse = args.mode == "inverse"
    if args.bootstrap_seal and not sentinels_unsealed():
        raise RuntimeError("bootstrap refused: output identity already sealed")
    if not args.bootstrap_seal and sentinels_unsealed():
        raise RuntimeError("output identity unsealed")
    source = args.input.read_bytes()
    source_shape = shape(source)
    check_shape(source_shape, output_expected() if inverse else input_expected(),
                unsealed=args.bootstrap_seal and inverse)
    mapped, window = verify_authority(
        args.probe10_log.read_bytes(), args.probe10_error_headers.read_bytes(),
        args.probe10_diagnostics.read_bytes())
    source_text = source.decode("utf-8", errors="strict")
    verify_blocker_anchors(source_text)
    collision = audit_collisions(source_text, inverse=inverse)
    before_trust = trust(source_text)
    result_text, rule_audit = apply_rules(source_text, inverse=inverse)
    result = result_text.encode("utf-8")
    result_shape = shape(result)
    check_shape(result_shape, input_expected() if inverse else output_expected(),
                unsealed=args.bootstrap_seal and not inverse)
    after_trust = trust(result_text)
    if before_trust != after_trust or any(after_trust.values()):
        raise RuntimeError(f"trust0 failure: {before_trust} -> {after_trust}")
    restored, _ = apply_rules(result_text, inverse=not inverse)
    if restored.encode("utf-8") != source:
        raise RuntimeError("opposite transform failed byte-exact restoration")
    if args.output.exists() or args.audit.exists():
        raise RuntimeError("refusing to overwrite output or audit")
    record = {
        "schema": SCHEMA,
        "status": "STATIC_LOCAL_API_PASS_WITH_STRUCTURAL_BLOCKERS_NOT_LEAN_EXECUTED",
        "activation": False,
        "promotion": False,
        "mode": args.mode,
        "authority": {"candidate_sha256": INPUT_SHA256, "candidate_git_blob": INPUT_GIT_BLOB,
                      "log_sha256": LOG_SHA256, "error_headers_sha256": HEADERS_SHA256,
                      "diagnostics_sha256": DIAGNOSTICS_SHA256,
                      "errors": 255, "warnings": 343, "panic": 0, "exit": 1},
        "window": window,
        "structural_root_analysis": list(STRUCTURAL_BLOCKERS),
        "scope": {"candidate_lines": [50000, 51837],
                  "primary_carrier_or_atlas_rewritten": False,
                  "cascade_diagnostics_patched": False,
                  "local_API_producer_declarations": 2,
                  "foreign_helper_span_overlap": False},
        "source": source_shape,
        "result": result_shape,
        "repair_families": len(RULES),
        "repair_occurrences": sum(item["occurrences"] for item in rule_audit),
        "direct_diagnostics": len(mapped),
        "selected_exact_probe10_lines": sorted({h.line for r in RULES for h in r.headers}),
        "diagnostic_map": mapped,
        "rules": rule_audit,
        "collision_audit": collision,
        "inverse_byte_equal": True,
        "trust": after_trust,
        "execution": {"lean": False, "lake": False, "git": False, "network": False,
                      "remote": False, "repository_source_mutation": False},
    }
    args.output.write_bytes(result)
    args.audit.write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(json.dumps(record, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
