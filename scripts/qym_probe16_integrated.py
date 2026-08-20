#!/usr/bin/env python3
"""Fail-closed exact-P15 integrator for three frozen Probe16 repair components.

The helper files are SHA-256/Git-blob/shape pinned before import. Only their
declarative RULES values and exact static/collision contracts are used.
Every component is replayed standalone, all six component orders and matching
inverses are checked, and exact terminal Probe15 sidecars are required.
Lean, Lake, Git, network, install, and canonical-source mutation are outside
this program.
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

SCHEMA = "qym-probe16-integrated-exact-terminal-p15-v2"
ACTIVATION = False
PACKAGE_DIR = Path(__file__).resolve().parent

INPUT_SHA256 = "9cd10544c82d5871d1cb336b1816b80c310e8413f051284db0261efcd676c7b6"
INPUT_GIT_BLOB = "c604421ed340e71fe3e24d3a7d391115990882ec"
INPUT_BYTES = 2_941_554
INPUT_LF = 62_190
OUTPUT_SHA256 = "19e68721a055a4131d7873fe37ee02509565bb4e0f202c74b646cba2275aba74"
OUTPUT_GIT_BLOB = "5d8def67719cdb3a7471c33aa320fafbf44ff186"
OUTPUT_BYTES = 2_942_215
OUTPUT_LF = 62_206

RUN_ID = 31992267418
JOB_ID = 95277790400
ARTIFACT_ID = 9275890870
TRIGGER_SHA = "1679e9e9f916e95d5a4fe10f9e59502471c84191"
ZIP_SHA256 = "b6f435c38aa5e712b32511025ab95720f8e7e0a34b0b0cccc5ef021bbcdddc07"
RESULT_SHA256 = "0254b92c4ce85a80a10f42f6038bf4fd6787411f84bae20a0abc0af638584853"
LOG_SHA256 = "8722d57acddee9696debb88d34a586ba4b28adbf9d2f64ca8b0500198a0db511"
HEADERS_SHA256 = "1c7ad5d2a165913802412602a9e4b37e719ce69bc1da8c0a1b74ad5e5df98381"
DIAGNOSTICS_SHA256 = "54e83aa0f8f792efc92b1a509729001e0049a87bb8ae5705b48792086bf6df58"
EXPECTED_ERRORS = 100
EXPECTED_WARNINGS = 350


@dataclass(frozen=True)
class Component:
    label: str
    relative_path: str
    helper_sha256: str
    helper_git_blob: str
    helper_bytes: int
    helper_lf: int
    expected_rules: int
    expected_occurrences: int
    expected_owned_diagnostics: int
    expected_direct_diagnostics: int
    standalone_sha256: str
    standalone_git_blob: str
    standalone_bytes: int
    standalone_lf: int


COMPONENTS: tuple[Component, ...] = (
    Component(
        "mid37k49k",
        "qym-probe16-mid37k49k-p15-static/qym_probe16_mid37k49k_p15_static.py",
        "5723983fb113915956363e8189299b51368e6ab5b3b2e7cc046de12668110473",
        "c130e0d8b76330c441b13ee737587aec177c3c24",
        16_562, 426, 7, 7, 9, 9,
        "19e13d24617978b7a4932680847e0ae235257b6b2087a5a002f801a7462ada02",
        "c0cd987885babc7dd03d93f82c0f9c00b39901dc",
        2_941_847, 62_197,
    ),
    Component(
        "ambient_zero_extension",
        "qym-probe16-ambient-zero-extension-p15-static/qym_probe16_ambient_zero_extension_p15_static.py",
        "8594fdd90e811b7e04fad3a17d67b034e26a7b69b76672c78e2a278bd114e1e4",
        "798bdfa6446bb21435c9540718cad5b89412eeaa",
        15_691, 455, 1, 1, 1, 1,
        "b0e7acb5e294ecd311b05442fa9a50ce12a30b1800f949abd350c0f848183f9b",
        "ad414ecd9ad863bdcd056a0b1a00437adc024800",
        2_941_600, 62_191,
    ),
    Component(
        "tail_sequenced",
        "qym-probe16-tail-p15-sequenced/qym_probe16_tail_p15_sequenced.py",
        "1fa1af220902c3c54bbb504987c9fb8cf82b0a92db4fc4f8dc5286afbaa8772e",
        "e401024361837a62c8a8575a8d4d0cc86d053eb8",
        24_175, 619, 8, 8, 9, 9,
        "ce8fc72801741ae7a4a8c203f972e65aca2c53beb3b75b72dfdd7cc0feef6e67",
        "1ab924ef0363bdfe2de652fc7121b06c13a1c075",
        2_941_876, 62_198,
    ),
)

EXPECTED_RULES = 16
EXPECTED_OCCURRENCES = 16
EXPECTED_OWNED_DIAGNOSTICS = 19
EXPECTED_DIRECT_DIAGNOSTICS = 19
EXPECTED_DECLARED_BASELINE_OVERLAPS = 4


@dataclass(frozen=True)
class RuleView:
    label: str
    old: str
    new: str
    occurrences: int


@dataclass(frozen=True)
class Loaded:
    component: Component
    path: Path
    module: ModuleType
    rules: tuple[RuleView, ...]


def sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def git_blob(raw: bytes) -> str:
    return hashlib.sha1(
        b"blob " + str(len(raw)).encode("ascii") + bytes([0]) + raw
    ).hexdigest()


def shape(raw: bytes) -> dict[str, object]:
    raw.decode("utf-8", errors="strict")
    return {
        "sha256": sha256(raw),
        "git_blob": git_blob(raw),
        "bytes": len(raw),
        "lf": raw.count(bytes([10])),
        "cr": bytes([13]) in raw,
        "nul": bytes([0]) in raw,
        "bom": raw.startswith(bytes([0xEF, 0xBB, 0xBF])),
        "terminal_lf": raw.endswith(bytes([10])),
    }


def expected_shape(inverse: bool) -> dict[str, object]:
    values = (
        (OUTPUT_SHA256, OUTPUT_GIT_BLOB, OUTPUT_BYTES, OUTPUT_LF)
        if inverse
        else (INPUT_SHA256, INPUT_GIT_BLOB, INPUT_BYTES, INPUT_LF)
    )
    return {
        "sha256": values[0], "git_blob": values[1],
        "bytes": values[2], "lf": values[3],
        "cr": False, "nul": False, "bom": False, "terminal_lf": True,
    }


def trust(text: str) -> dict[str, int]:
    patterns = {
        "sorry": r"\bsorry\b",
        "admit": r"\badmit\b",
        "native_decide": r"\bnative_decide\b",
        "Lean.ofReduceBool": r"\bLean\.ofReduceBool\b",
        "axiom": r"(?m)^\s*axiom\s+",
        "unsafe": r"(?m)^\s*unsafe\s+(?:def|theorem|opaque|abbrev|instance)\s+",
        "maxHeartbeats_zero": r"set_option\s+maxHeartbeats\s+0\b",
    }
    return {name: len(re.findall(pattern, text)) for name, pattern in patterns.items()}


def helper_shape(component: Component) -> dict[str, object]:
    return {
        "sha256": component.helper_sha256,
        "git_blob": component.helper_git_blob,
        "bytes": component.helper_bytes,
        "lf": component.helper_lf,
        "cr": False, "nul": False, "bom": False, "terminal_lf": True,
    }


def standalone_shape(component: Component) -> dict[str, object]:
    return {
        "sha256": component.standalone_sha256,
        "git_blob": component.standalone_git_blob,
        "bytes": component.standalone_bytes,
        "lf": component.standalone_lf,
        "cr": False, "nul": False, "bom": False, "terminal_lf": True,
    }


def path_candidates(relative: str) -> tuple[Path, ...]:
    rel = Path(relative)
    values = (
        PACKAGE_DIR / rel,
        PACKAGE_DIR.parent / rel,
        PACKAGE_DIR.parent / "scripts" / rel,
        PACKAGE_DIR.parents[1] / "work" / rel,
    )
    seen: list[Path] = []
    for value in values:
        resolved = value.resolve()
        if resolved not in seen:
            seen.append(resolved)
    return tuple(seen)


def resolve_component(component: Component) -> Path:
    observed: dict[str, object] = {}
    matches: list[Path] = []
    for path in path_candidates(component.relative_path):
        if not path.is_file():
            continue
        raw = path.read_bytes()
        observed[str(path)] = shape(raw)
        if shape(raw) == helper_shape(component):
            matches.append(path)
    if len(matches) != 1:
        raise RuntimeError(
            f"{component.label}: exact helper resolution failed: {observed}"
        )
    return matches[0]


def import_component(component: Component, path: Path) -> ModuleType:
    before = path.read_bytes()
    if shape(before) != helper_shape(component):
        raise RuntimeError(f"{component.label}: helper changed before import")
    name = "_qym_probe16_integrated_" + component.label
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"{component.label}: import spec unavailable")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    if shape(path.read_bytes()) != helper_shape(component):
        raise RuntimeError(f"{component.label}: helper changed during import")
    if getattr(module, "ACTIVATION", False) is not False:
        raise RuntimeError(f"{component.label}: activation must be false")
    return module


def normalize_rules(component: Component, module: ModuleType) -> tuple[RuleView, ...]:
    raw_rules = tuple(getattr(module, "RULES", ()))
    rows: list[RuleView] = []
    for index, rule in enumerate(raw_rules):
        if all(hasattr(rule, key) for key in ("label", "old", "new")):
            label = getattr(rule, "label")
            old = getattr(rule, "old")
            new = getattr(rule, "new")
            occurrences = int(getattr(rule, "occurrences", 1))
        elif isinstance(rule, (tuple, list)) and len(rule) >= 3:
            label, old, new = rule[:3]
            occurrences = 1
        else:
            raise RuntimeError(f"{component.label}: malformed rule {index}")
        if (
            not isinstance(label, str)
            or not isinstance(old, str)
            or not isinstance(new, str)
            or not old
            or old == new
            or occurrences != 1
        ):
            raise RuntimeError(f"{component.label}: invalid rule {index}")
        rows.append(RuleView(label, old, new, occurrences))
    if len(rows) != component.expected_rules:
        raise RuntimeError(f"{component.label}: rule count mismatch")
    if sum(row.occurrences for row in rows) != component.expected_occurrences:
        raise RuntimeError(f"{component.label}: occurrence count mismatch")
    return tuple(rows)


def header_multiplicity(header: object) -> int:
    if isinstance(header, dict):
        return int(header.get("multiplicity", 1))
    if isinstance(header, (tuple, list)):
        return int(header[4]) if len(header) > 4 and isinstance(header[4], int) else 1
    return int(getattr(header, "multiplicity", 1))


def header_kind(header: object) -> str:
    if isinstance(header, dict):
        return str(header.get("kind", "direct"))
    if isinstance(header, (tuple, list)):
        return str(header[5]) if len(header) > 5 else "direct"
    return str(getattr(header, "kind", "direct"))


def diagnostic_counts(module: ModuleType) -> tuple[int, int]:
    global_headers = getattr(module, "HEADERS", None)
    if global_headers is not None:
        headers = tuple(global_headers)
    else:
        values: list[object] = []
        for rule in tuple(getattr(module, "RULES", ())):
            plural = getattr(rule, "headers", None)
            singular = getattr(rule, "header", None)
            if plural is not None:
                values.extend(tuple(plural))
            elif singular is not None:
                values.append(singular)
            elif isinstance(rule, (tuple, list)) and len(rule) > 3:
                values.append(rule[3])
        headers = tuple(values)
    owned = sum(header_multiplicity(header) for header in headers)
    direct = sum(
        header_multiplicity(header)
        for header in headers
        if header_kind(header) != "cascade"
    )
    return owned, direct


def load_components() -> tuple[Loaded, ...]:
    loaded: list[Loaded] = []
    for component in COMPONENTS:
        path = resolve_component(component)
        module = import_component(component, path)
        rules = normalize_rules(component, module)
        owned, direct = diagnostic_counts(module)
        if (owned, direct) != (
            component.expected_owned_diagnostics,
            component.expected_direct_diagnostics,
        ):
            raise RuntimeError(
                f"{component.label}: diagnostic ownership mismatch: {(owned, direct)}"
            )
        loaded.append(Loaded(component, path, module, rules))
    if (
        sum(len(item.rules) for item in loaded) != EXPECTED_RULES
        or sum(row.occurrences for item in loaded for row in item.rules)
        != EXPECTED_OCCURRENCES
        or sum(item.component.expected_owned_diagnostics for item in loaded)
        != EXPECTED_OWNED_DIAGNOSTICS
        or sum(item.component.expected_direct_diagnostics for item in loaded)
        != EXPECTED_DIRECT_DIAGNOSTICS
    ):
        raise RuntimeError("integrated component totals drifted")
    return tuple(loaded)


def apply_rule_set(
    text: str, item: Loaded, inverse: bool
) -> tuple[str, list[dict[str, object]]]:
    rules = tuple(reversed(item.rules)) if inverse else item.rules
    rows: list[dict[str, object]] = []
    for rule in rules:
        source, target = (rule.new, rule.old) if inverse else (rule.old, rule.new)
        count = text.count(source)
        if count != rule.occurrences:
            raise RuntimeError(
                f"{item.component.label}:{rule.label}: "
                f"anchor count {count}, expected {rule.occurrences}"
            )
        text = text.replace(source, target)
        rows.append({
            "component": item.component.label,
            "label": rule.label,
            "inverse": inverse,
            "occurrences": count,
        })
    return text, rows


def apply_order(
    text: str,
    loaded: tuple[Loaded, ...],
    order: tuple[int, ...],
    inverse: bool,
) -> tuple[str, list[dict[str, object]]]:
    result = text
    records: list[dict[str, object]] = []
    indices = tuple(reversed(order)) if inverse else order
    for index in indices:
        result, rows = apply_rule_set(result, loaded[index], inverse)
        records.extend(rows)
    return result, records


def verify_standalone_and_spans(source: str, loaded: tuple[Loaded, ...]) -> dict[str, object]:
    spans: list[tuple[int, int, str, str]] = []
    component_contracts: dict[str, object] = {}
    for item in loaded:
        standalone, _ = apply_rule_set(source, item, False)
        if shape(standalone.encode("utf-8")) != standalone_shape(item.component):
            raise RuntimeError(f"{item.component.label}: standalone output drift")
        for rule in item.rules:
            if source.count(rule.old) != rule.occurrences:
                raise RuntimeError(f"{item.component.label}:{rule.label}: base anchor drift")
            start = source.find(rule.old)
            spans.append((start, start + len(rule.old), item.component.label, rule.label))
        if item.component.label == "mid37k49k":
            contract = item.module.static_audit()
            if contract.get("undeclared_collisions") != 0:
                raise RuntimeError("mid component collision contract failed")
        elif item.component.label == "ambient_zero_extension":
            contract = item.module.collision_contract()
            if (
                contract.get("span_overlap_count") != 0
                or contract.get("textual_anchor_overlap_count") != 0
            ):
                raise RuntimeError("ambient component collision contract failed")
        elif item.component.label == "tail_sequenced":
            contract = item.module.collision_audit(source)
            declared = contract.get("declared_consumed_new_overlaps", ())
            if (
                contract.get("undeclared_overlaps") != 0
                or contract.get("own_overlaps") != 0
                or len(declared) != EXPECTED_DECLARED_BASELINE_OVERLAPS
            ):
                raise RuntimeError("tail component collision contract failed")
        else:
            raise RuntimeError(f"unknown component contract: {item.component.label}")
        component_contracts[item.component.label] = contract
    overlaps: list[tuple[object, object]] = []
    for left, right in itertools.combinations(spans, 2):
        if left[2] != right[2] and max(left[0], right[0]) < min(left[1], right[1]):
            overlaps.append((left, right))
    if overlaps:
        raise RuntimeError(f"cross-component source-span collisions: {overlaps}")
    return {
        "source_spans": len(spans),
        "cross_component_overlaps": 0,
        "declared_baseline_overlaps": EXPECTED_DECLARED_BASELINE_OVERLAPS,
        "component_contracts": component_contracts,
    }


def audit_all_orders(source: str, loaded: tuple[Loaded, ...]) -> dict[str, object]:
    expected = expected_shape(True)
    hashes: set[str] = set()
    count = 0
    for order in itertools.permutations(range(len(loaded))):
        forward, _ = apply_order(source, loaded, order, False)
        forward_raw = forward.encode("utf-8")
        if shape(forward_raw) != expected:
            raise RuntimeError(f"component-order output drift: {order}")
        if any(trust(forward).values()):
            raise RuntimeError(f"component-order trust drift: {order}")
        hashes.add(sha256(forward_raw))
        restored, _ = apply_order(forward, loaded, order, True)
        if restored != source:
            raise RuntimeError(f"component-order inverse drift: {order}")
        count += 1
    if count != 6 or hashes != {OUTPUT_SHA256}:
        raise RuntimeError("all-order audit failed to seal one exact output")
    return {
        "orders": count,
        "unique_outputs": len(hashes),
        "output_sha256": OUTPUT_SHA256,
        "output_git_blob": OUTPUT_GIT_BLOB,
        "matching_reverse_inverses_exact": True,
        "trust0": True,
    }


def transform(
    text: str, loaded: tuple[Loaded, ...], inverse: bool = False
) -> tuple[str, list[dict[str, object]]]:
    if shape(text.encode("utf-8")) != expected_shape(inverse):
        raise RuntimeError("exact integrated input candidate gate failed")
    before = trust(text)
    if any(before.values()):
        raise RuntimeError(f"source trust0 failure: {before}")
    canonical = tuple(range(len(loaded)))
    result, records = apply_order(text, loaded, canonical, inverse)
    if shape(result.encode("utf-8")) != expected_shape(not inverse):
        raise RuntimeError("integrated output identity mismatch")
    after = trust(result)
    if before != after or any(after.values()):
        raise RuntimeError(f"integrated trust drift: {before} -> {after}")
    return result, records


def verify_authority(
    result_raw: bytes,
    log_raw: bytes,
    headers_raw: bytes,
    diagnostics_raw: bytes,
    exit_raw: bytes,
    panic_raw: bytes,
) -> dict[str, object]:
    for name, raw, expected in (
        ("result", result_raw, RESULT_SHA256),
        ("log", log_raw, LOG_SHA256),
        ("headers", headers_raw, HEADERS_SHA256),
        ("diagnostics", diagnostics_raw, DIAGNOSTICS_SHA256),
    ):
        if sha256(raw) != expected:
            raise RuntimeError(f"exact Probe15 {name} sidecar gate failed")
    if exit_raw.strip() != b"1" or panic_raw:
        raise RuntimeError("exact Probe15 exit/panic gate failed")
    result = json.loads(result_raw)
    required = {
        "github_sha": TRIGGER_SHA,
        "candidate_qym_sha256": INPUT_SHA256,
        "candidate_qym_blob": INPUT_GIT_BLOB,
        "log_sha256": LOG_SHA256,
        "exit": 1,
        "error_headers": EXPECTED_ERRORS,
        "warning_headers": EXPECTED_WARNINGS,
        "panic_lines": 0,
        "semantic_pass": False,
    }
    for key, expected in required.items():
        if result.get(key) != expected:
            raise RuntimeError(f"Probe15 result field mismatch: {key}")
    headers = headers_raw.decode("utf-8").splitlines()
    diagnostics = [
        json.loads(line)
        for line in diagnostics_raw.decode("utf-8").splitlines()
        if line
    ]
    errors = sum(row.get("severity") == "error" for row in diagnostics)
    warnings = sum(row.get("severity") == "warning" for row in diagnostics)
    if (len(headers), errors, warnings) != (
        EXPECTED_ERRORS, EXPECTED_ERRORS, EXPECTED_WARNINGS
    ):
        raise RuntimeError("Probe15 diagnostic totals mismatch")
    return {
        "run_id": RUN_ID, "job_id": JOB_ID, "artifact_id": ARTIFACT_ID,
        "trigger_sha": TRIGGER_SHA, "zip_sha256": ZIP_SHA256,
        "result_sha256": RESULT_SHA256, "log_sha256": LOG_SHA256,
        "headers_sha256": HEADERS_SHA256,
        "diagnostics_sha256": DIAGNOSTICS_SHA256,
        "errors": errors, "warnings": warnings, "panic": 0, "exit": 1,
    }


def preflight(paths: tuple[Path, ...]) -> None:
    resolved = tuple(path.resolve() for path in paths)
    if len(set(resolved)) != len(resolved):
        raise RuntimeError("output and audit destinations must be distinct")
    for path in resolved:
        if path.exists():
            raise RuntimeError(f"refusing overwrite: {path}")
        if not path.parent.is_dir() or path.parent.is_symlink():
            raise RuntimeError(f"destination parent must be an existing real directory: {path}")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--audit", type=Path, required=True)
    parser.add_argument("--inverse", action="store_true")
    parser.add_argument("--probe15-result", type=Path, required=True)
    parser.add_argument("--probe15-log", type=Path, required=True)
    parser.add_argument("--probe15-error-headers", type=Path, required=True)
    parser.add_argument("--probe15-diagnostics", type=Path, required=True)
    parser.add_argument("--probe15-exit", type=Path, required=True)
    parser.add_argument("--probe15-panic-lines", type=Path, required=True)
    args = parser.parse_args()

    preflight((args.output, args.audit))
    authority = verify_authority(
        args.probe15_result.read_bytes(),
        args.probe15_log.read_bytes(),
        args.probe15_error_headers.read_bytes(),
        args.probe15_diagnostics.read_bytes(),
        args.probe15_exit.read_bytes(),
        args.probe15_panic_lines.read_bytes(),
    )
    loaded = load_components()
    source_raw = args.input.read_bytes()
    source = source_raw.decode("utf-8", errors="strict")
    authority_source = source
    if args.inverse:
        authority_source, _ = transform(source, loaded, True)
    span_audit = verify_standalone_and_spans(authority_source, loaded)
    order_audit = audit_all_orders(authority_source, loaded)
    result, records = transform(source, loaded, args.inverse)
    restored, inverse_records = transform(result, loaded, not args.inverse)
    if restored.encode("utf-8") != source_raw:
        raise RuntimeError("canonical inverse is not byte exact")
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
        "owned_diagnostics": EXPECTED_OWNED_DIAGNOSTICS,
        "direct_diagnostics": EXPECTED_DIRECT_DIAGNOSTICS,
        "cascade_diagnostics": (
            EXPECTED_OWNED_DIAGNOSTICS - EXPECTED_DIRECT_DIAGNOSTICS
        ),
        "rules": records,
        "matching_inverse_rules": inverse_records,
        "inverse_byte_equal": True,
        "span_audit": span_audit,
        "all_order_audit": order_audit,
        "trust": trust(result),
        "execution": {
            "lean": False, "lake": False, "git": False,
            "network": False, "remote": False, "install": False,
            "canonical_source_mutation": False,
        },
    }
    result_raw = result.encode("utf-8")
    audit_raw = (
        json.dumps(record, ensure_ascii=False, indent=2) + "\n"
    ).encode("utf-8")
    args.output.write_bytes(result_raw)
    args.audit.write_bytes(audit_raw)
    print(json.dumps({
        "result": record["result"],
        "orders": order_audit["orders"],
        "inverse_exact": True,
    }, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
