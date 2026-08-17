#!/usr/bin/env python3
"""Fail-closed exact-P13 integrator for five frozen Probe14 components.

Every helper is hash/blob checked before import.  The declarative rule sets
are composed directly, all 120 component orders and their matching reverse
inverses are replayed, and two fresh destinations are preflighted before any
write.  This program never invokes Lean, Lake, Git, a network, or a remote
service; repository installation and workflow execution are separate steps.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import itertools
import json
import re
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from types import ModuleType


sys.dont_write_bytecode = True

SCHEMA = "qym-probe14-integrated-exact-terminal-p13-v1"
ACTIVATION = False
PACKAGE_DIR = Path(__file__).resolve().parent

INPUT_SHA256 = "92e91734eb4b1d406d854a6021c815636eff6cf0aa2f4924e710249a583ebe3b"
INPUT_GIT_BLOB = "5c895f906b516366653aaf6fc459825e89045076"
INPUT_BYTES = 2_938_395
INPUT_LF = 62_112
OUTPUT_SHA256 = "e8ac0ba15f35c88792552a0d55d789c222d360a10d30c3cedb0ce0a8dfb879b7"
OUTPUT_GIT_BLOB = "49b71abd253e0b1292ecacd9ebc984fa9ea3d9de"
OUTPUT_BYTES = 2_940_390
OUTPUT_LF = 62_158

LOG_SHA256 = "e2a675d67ef304dbbf6b3800b9e1a8c2fd1183ff16a82eb7f46b5a64fdef0826"
HEADERS_SHA256 = "74e4c1505182503c4acc9dfe6be6a4316e44b821ec7897b377597af12c07bf02"
DIAGNOSTICS_SHA256 = "0dbe572bed4860fd6f843045d3fbc9b11edab1931f63d6b5acb70bfd88d85dcb"
EXPECTED_ERRORS = 151
EXPECTED_WARNINGS = 341


@dataclass(frozen=True)
class Component:
    label: str
    relative_path: str
    helper_sha256: str
    helper_git_blob: str
    expected_rules: int
    expected_occurrences: int
    expected_owned_diagnostics: int
    expected_direct_diagnostics: int
    standalone_output_sha256: str


COMPONENTS: tuple[Component, ...] = (
    Component(
        "probe14_frontier",
        "qym-probe14-frontier-p13-conditional/qym_probe14_frontier_p13_conditional.py",
        "1118d53e64698cfe4d41da84d0a4450ad80efb4a0409b1eace0992abdfe20929",
        "9c0a58862d07f466f17016e00498d747c88f9a4c",
        2,
        2,
        3,
        3,
        "5f18bb505fed64b29a3e319ee8d2d634dbd7c56bad755234d6eecd85f6df8e6d",
    ),
    Component(
        "probe14_30k47k",
        "qym-probe14-30k47k-p13-reanchored/qym_probe14_30k47k_p13_reanchored.py",
        "671f909e011eb3a18e402c33bd4df30bcc7aa098bf928ecbf629aa8a09028686",
        "196e8b19026b2bdb378f2ee231f150ec7267a3e4",
        11,
        11,
        13,
        13,
        "65c87b052d1dceac49b48f51700f873211dfb5089409ead64e4692bc3233212d",
    ),
    Component(
        "probe14_producer_timeouts",
        "qym-probe14-producer-timeouts-p13-static/qym_probe14_producer_timeouts_p13_static.py",
        "65a610e3dd278f084fb5f24285143f798685fd858efa9d8c92a589442a725cc0",
        "fecdb4950da759f45c7d5cf2b5945abf696ac3a3",
        7,
        7,
        19,
        9,
        "fac716c5cadbd3ed9f2d9cb12a870a7fdf436003aa6b5e899bbd3290097b2883",
    ),
    Component(
        "probe14_gl_refinement",
        "qym-probe14-gl-action-p13-sequenced/qym_probe14_gl_action_p13_sequenced.py",
        "8a152cc89f8994eb5ab41adc21f17821e193056ae60e5e1bdc7aed75f669943e",
        "307028f11bc5cc5514ff779fbec2e89ebdf4d22e",
        3,
        3,
        3,
        3,
        "22bccab685696d63ff4a810301adbdec0957eb7758ad84f0162462279c3a273a",
    ),
    Component(
        "probe14_tail",
        "qym-probe14-tail-prep-p13-static/qym_probe14_tail_prep_p13_static.py",
        "acd2cefb1db2b250558a362777b5e31c26fdb4dcfb23a29b4ff81f1a4c835412",
        "1a1a4da2bd500b7bab4dda6c740389c765a36768",
        5,
        5,
        5,
        5,
        "1f51eab0e820b9a4370433bb2c42554fe9cf7afbe52c03a2b940f7b31dc6fcbd",
    ),
)

EXPECTED_RULES = 28
EXPECTED_OCCURRENCES = 28
EXPECTED_OWNED_DIAGNOSTICS = 43
EXPECTED_DIRECT_DIAGNOSTICS = 33


@dataclass(frozen=True)
class Loaded:
    component: Component
    path: Path
    module: ModuleType
    rules: tuple[object, ...]


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


def expected_shape(inverse: bool) -> dict[str, object]:
    values = (
        (OUTPUT_SHA256, OUTPUT_GIT_BLOB, OUTPUT_BYTES, OUTPUT_LF)
        if inverse
        else (INPUT_SHA256, INPUT_GIT_BLOB, INPUT_BYTES, INPUT_LF)
    )
    return {
        "sha256": values[0],
        "git_blob": values[1],
        "bytes": values[2],
        "lf": values[3],
        "cr": False,
        "nul": False,
        "bom": False,
        "terminal_lf": True,
    }


def trust(text: str) -> dict[str, int]:
    patterns = {
        "sorry": r"\bsorry\b",
        "admit": r"\badmit\b",
        "native_decide": r"\bnative_decide\b",
        "Lean.ofReduceBool": r"\bLean\.ofReduceBool\b",
        "axiom_declaration": r"(?m)^\s*axiom\s+",
        "unsafe_declaration": r"(?m)^\s*unsafe\s+(?:def|theorem|opaque|abbrev|instance)\s+",
        "maxHeartbeats_zero": r"set_option\s+maxHeartbeats\s+0\b",
    }
    return {label: len(re.findall(pattern, text)) for label, pattern in patterns.items()}


def rule_headers(rule: object) -> tuple[object, ...]:
    plural = getattr(rule, "headers", None)
    if plural is not None:
        return tuple(plural)
    singular = getattr(rule, "header", None)
    if singular is not None:
        return (singular,)
    return ()


def path_candidates(relative: str) -> tuple[Path, ...]:
    return (
        (PACKAGE_DIR / relative).resolve(),
        (PACKAGE_DIR.parent / relative).resolve(),
        (PACKAGE_DIR.parents[1] / "work" / relative).resolve(),
    )


def resolve_component(component: Component) -> Path:
    seen: list[Path] = []
    for path in path_candidates(component.relative_path):
        if path not in seen and path.is_file():
            seen.append(path)
    exact = [path for path in seen if sha256(path.read_bytes()) == component.helper_sha256]
    if len(exact) != 1:
        observed = {str(path): sha256(path.read_bytes()) for path in seen}
        raise RuntimeError(f"{component.label}: exact helper resolution failed: {observed}")
    raw = exact[0].read_bytes()
    if git_blob(raw) != component.helper_git_blob:
        raise RuntimeError(f"{component.label}: helper blob mismatch")
    return exact[0]


def import_component(component: Component, path: Path) -> ModuleType:
    if sha256(path.read_bytes()) != component.helper_sha256:
        raise RuntimeError(f"{component.label}: changed before import")
    name = "_qym_probe14_integrated_" + component.label
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"{component.label}: import spec unavailable")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    if sha256(path.read_bytes()) != component.helper_sha256:
        raise RuntimeError(f"{component.label}: changed during import")
    return module


def load_components() -> tuple[Loaded, ...]:
    loaded: list[Loaded] = []
    for component in COMPONENTS:
        path = resolve_component(component)
        module = import_component(component, path)
        for key, expected in (
            ("INPUT_SHA256", INPUT_SHA256),
            ("INPUT_GIT_BLOB", INPUT_GIT_BLOB),
            ("INPUT_BYTES", INPUT_BYTES),
            ("INPUT_LF", INPUT_LF),
            ("OUTPUT_SHA256", component.standalone_output_sha256),
        ):
            if getattr(module, key, None) != expected:
                raise RuntimeError(f"{component.label}: runtime {key} mismatch")
        if getattr(module, "ACTIVATION", False) is not False:
            raise RuntimeError(f"{component.label}: activation must be false")
        rules = tuple(getattr(module, "RULES", ()))
        if len(rules) != component.expected_rules:
            raise RuntimeError(f"{component.label}: rule count mismatch")
        occurrences = sum(int(getattr(rule, "occurrences", 1)) for rule in rules)
        owned = sum(len(rule_headers(rule)) for rule in rules)
        direct = sum(
            getattr(header, "kind", "direct") != "cascade"
            for rule in rules
            for header in rule_headers(rule)
        )
        if occurrences != component.expected_occurrences:
            raise RuntimeError(f"{component.label}: occurrence count mismatch")
        if owned != component.expected_owned_diagnostics:
            raise RuntimeError(f"{component.label}: owned diagnostic count mismatch")
        if direct != component.expected_direct_diagnostics:
            raise RuntimeError(f"{component.label}: direct diagnostic count mismatch")
        for rule in rules:
            if not all(
                isinstance(getattr(rule, key, None), str)
                for key in ("label", "old", "new")
            ):
                raise RuntimeError(f"{component.label}: malformed declarative rule")
        loaded.append(Loaded(component, path, module, rules))
    if (
        sum(len(item.rules) for item in loaded) != EXPECTED_RULES
        or sum(
            int(getattr(rule, "occurrences", 1))
            for item in loaded
            for rule in item.rules
        )
        != EXPECTED_OCCURRENCES
        or sum(
            len(rule_headers(rule)) for item in loaded for rule in item.rules
        )
        != EXPECTED_OWNED_DIAGNOSTICS
        or sum(
            getattr(header, "kind", "direct") != "cascade"
            for item in loaded
            for rule in item.rules
            for header in rule_headers(rule)
        )
        != EXPECTED_DIRECT_DIAGNOSTICS
    ):
        raise RuntimeError("integrated component totals drifted")
    return tuple(loaded)


def apply_rule_set(
    text: str, item: Loaded, inverse: bool
) -> tuple[str, list[dict[str, object]]]:
    rows: list[dict[str, object]] = []
    rules = tuple(reversed(item.rules)) if inverse else item.rules
    for rule in rules:
        old, new = (
            (getattr(rule, "new"), getattr(rule, "old"))
            if inverse
            else (getattr(rule, "old"), getattr(rule, "new"))
        )
        occurrences = int(getattr(rule, "occurrences", 1))
        count = text.count(old)
        if count != occurrences:
            raise RuntimeError(
                f"{item.component.label}:{getattr(rule, 'label')}: "
                f"anchor count {count}, expected {occurrences}"
            )
        text = text.replace(old, new)
        rows.append(
            {
                "component": item.component.label,
                "label": getattr(rule, "label"),
                "inverse": inverse,
                "occurrences": count,
                "owned_diagnostics": len(rule_headers(rule)),
                "direct_diagnostics": sum(
                    getattr(header, "kind", "direct") != "cascade"
                    for header in rule_headers(rule)
                ),
            }
        )
    return text, rows


def apply_order(
    text: str,
    loaded: tuple[Loaded, ...],
    order: tuple[int, ...],
    inverse: bool,
) -> tuple[str, list[dict[str, object]]]:
    result = text
    rows: list[dict[str, object]] = []
    indices = tuple(reversed(order)) if inverse else order
    for index in indices:
        result, component_rows = apply_rule_set(result, loaded[index], inverse)
        rows.extend(component_rows)
    return result, rows


def transform(text: str, inverse: bool = False) -> tuple[str, list[dict[str, object]]]:
    raw = text.encode("utf-8")
    if shape(raw) != expected_shape(inverse):
        source_label = "Probe14" if inverse else "Probe13"
        raise RuntimeError(f"exact {source_label} candidate gate failed")
    before = trust(text)
    if any(before.values()):
        raise RuntimeError(f"source trust0 failure: {before}")
    loaded = load_components()
    canonical = tuple(range(len(loaded)))
    result, rows = apply_order(text, loaded, canonical, inverse)
    if shape(result.encode("utf-8")) != expected_shape(not inverse):
        raise RuntimeError("integrated output identity mismatch")
    after = trust(result)
    if before != after or any(after.values()):
        raise RuntimeError(f"integrated trust drift: {before} -> {after}")
    if (
        len(rows) != EXPECTED_RULES
        or sum(int(row["occurrences"]) for row in rows) != EXPECTED_OCCURRENCES
        or sum(int(row["owned_diagnostics"]) for row in rows)
        != EXPECTED_OWNED_DIAGNOSTICS
        or sum(int(row["direct_diagnostics"]) for row in rows)
        != EXPECTED_DIRECT_DIAGNOSTICS
    ):
        raise RuntimeError("integrated rule totals mismatch")
    return result, rows


def verify_authority(
    log: bytes, headers: bytes, diagnostics: bytes
) -> dict[str, object]:
    for label, raw, expected in (
        ("log", log, LOG_SHA256),
        ("headers", headers, HEADERS_SHA256),
        ("diagnostics", diagnostics, DIAGNOSTICS_SHA256),
    ):
        if sha256(raw) != expected:
            raise RuntimeError(f"exact Probe13 {label} sidecar gate failed")
    rows = [json.loads(line) for line in diagnostics.decode("utf-8").splitlines() if line]
    errors = sum(row.get("severity") == "error" for row in rows)
    warnings = sum(row.get("severity") == "warning" for row in rows)
    header_count = len(headers.decode("utf-8").splitlines())
    if (errors, warnings, header_count) != (
        EXPECTED_ERRORS,
        EXPECTED_WARNINGS,
        EXPECTED_ERRORS,
    ):
        raise RuntimeError(
            f"Probe13 diagnostic totals mismatch: {(errors, warnings, header_count)}"
        )
    return {
        "candidate_sha256": INPUT_SHA256,
        "candidate_git_blob": INPUT_GIT_BLOB,
        "log_sha256": LOG_SHA256,
        "headers_sha256": HEADERS_SHA256,
        "diagnostics_sha256": DIAGNOSTICS_SHA256,
        "errors": errors,
        "warnings": warnings,
        "panic": 0,
        "exit": 1,
    }


def audit_all_orders(source: str, loaded: tuple[Loaded, ...]) -> dict[str, object]:
    expected = expected_shape(True)
    output_hashes: set[str] = set()
    count = 0
    for order in itertools.permutations(range(len(loaded))):
        forward, _ = apply_order(source, loaded, order, False)
        forward_raw = forward.encode("utf-8")
        if shape(forward_raw) != expected:
            raise RuntimeError(f"component-order output drift: {order}")
        if any(trust(forward).values()):
            raise RuntimeError(f"component-order trust drift: {order}")
        output_hashes.add(sha256(forward_raw))
        restored, _ = apply_order(forward, loaded, order, True)
        if restored != source:
            raise RuntimeError(f"component-order inverse drift: {order}")
        count += 1
    if count != 120 or output_hashes != {OUTPUT_SHA256}:
        raise RuntimeError("exhaustive component-order audit did not seal one output")
    return {
        "orders": count,
        "unique_outputs": len(output_hashes),
        "all_output_sha256": OUTPUT_SHA256,
        "all_output_git_blob": OUTPUT_GIT_BLOB,
        "matching_reverse_inverse_exact": True,
        "all_outputs_trust0": True,
    }


def preflight(paths: tuple[Path, ...]) -> None:
    resolved = tuple(path.resolve() for path in paths)
    if len(set(resolved)) != len(resolved):
        raise RuntimeError("output and audit paths must be distinct")
    for path in resolved:
        if path.exists() or not path.parent.is_dir():
            raise RuntimeError(f"destination must be fresh with existing parent: {path}")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--audit", type=Path, required=True)
    parser.add_argument("--inverse", action="store_true")
    parser.add_argument("--probe13-log", type=Path, required=True)
    parser.add_argument("--probe13-error-headers", type=Path, required=True)
    parser.add_argument("--probe13-diagnostics", type=Path, required=True)
    args = parser.parse_args()

    preflight((args.output, args.audit))
    authority = verify_authority(
        args.probe13_log.read_bytes(),
        args.probe13_error_headers.read_bytes(),
        args.probe13_diagnostics.read_bytes(),
    )
    source_raw = args.input.read_bytes()
    source = source_raw.decode("utf-8", errors="strict")
    result, rows = transform(source, args.inverse)
    restored, inverse_rows = transform(result, not args.inverse)
    if restored.encode("utf-8") != source_raw:
        raise RuntimeError("canonical inverse is not byte exact")
    loaded = load_components()
    authority_source = source if not args.inverse else result
    order_audit = audit_all_orders(authority_source, loaded)
    record = {
        "schema": SCHEMA,
        "status": "STATIC_PASS_EXACT_COMPOSITION_NOT_LEAN_EXECUTED",
        "activation": ACTIVATION,
        "promotion": False,
        "mode": "inverse" if args.inverse else "forward",
        "authority": authority,
        "source": shape(source_raw),
        "result": shape(result.encode("utf-8")),
        "components": [asdict(component) for component in COMPONENTS],
        "repair_families": EXPECTED_RULES,
        "repair_occurrences": EXPECTED_OCCURRENCES,
        "diagnostic_ownership_records": EXPECTED_OWNED_DIAGNOSTICS,
        "direct_diagnostic_ownership_records": EXPECTED_DIRECT_DIAGNOSTICS,
        "cascade_diagnostic_ownership_records": (
            EXPECTED_OWNED_DIAGNOSTICS - EXPECTED_DIRECT_DIAGNOSTICS
        ),
        "rules": rows,
        "matching_inverse_rules": inverse_rows,
        "inverse_byte_equal": True,
        "all_order_audit": order_audit,
        "trust": trust(result),
        "execution": {
            "lean": False,
            "lake": False,
            "git": False,
            "network": False,
            "remote": False,
            "repository_source_mutation": False,
        },
    }
    result_raw = result.encode("utf-8")
    audit_raw = (
        json.dumps(record, indent=2, ensure_ascii=False) + "\n"
    ).encode("utf-8")
    args.output.write_bytes(result_raw)
    args.audit.write_bytes(audit_raw)
    print(
        json.dumps(
            {"result": record["result"], "orders": order_audit["orders"]},
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
