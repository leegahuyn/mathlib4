#!/usr/bin/env python3
"""Fail-closed exact-P14 integrator for five frozen Probe15 repair components.

The helper files are SHA-256/Git-blob/shape pinned before import.  Only their
declarative RULES values are normalized; component main/transform/collision
APIs are never called.  Every component is replayed standalone, all 120
component orders and matching inverses are checked, and exact terminal Probe14
sidecars are required.  Lean, Lake, Git, network, install, and canonical-source
mutation are outside this program.
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

SCHEMA = "qym-probe15-integrated-exact-terminal-p14-v1"
ACTIVATION = False
PACKAGE_DIR = Path(__file__).resolve().parent

INPUT_SHA256 = "e8ac0ba15f35c88792552a0d55d789c222d360a10d30c3cedb0ce0a8dfb879b7"
INPUT_GIT_BLOB = "49b71abd253e0b1292ecacd9ebc984fa9ea3d9de"
INPUT_BYTES = 2_940_390
INPUT_LF = 62_158
OUTPUT_SHA256 = "9cd10544c82d5871d1cb336b1816b80c310e8413f051284db0261efcd676c7b6"
OUTPUT_GIT_BLOB = "c604421ed340e71fe3e24d3a7d391115990882ec"
OUTPUT_BYTES = 2_941_554
OUTPUT_LF = 62_190

RUN_ID = 31987036649
JOB_ID = 95263720714
ARTIFACT_ID = 9274246215
TRIGGER_SHA = "3503a346d63921bda913b07529f2ad7c3288db8c"
ZIP_SHA256 = "fd414bc1328fc0422788cb9e0d9c42db6be015b871e6f262136cc6ffcdde61ab"
RESULT_SHA256 = "4ae82181ae7271429b44347ab334bd44c8ffc30d01259bf40b9d26b0d7a57036"
LOG_SHA256 = "250bbac608414a347525dffcdd2c54efba07ba1aac1f4b5e6a26cfe5109d5efa"
HEADERS_SHA256 = "42934d8e7289d6b30dba316139441719b748df8b31b19efc1def3e10af9b9dfc"
DIAGNOSTICS_SHA256 = "4eba0f0371689b45b0e5a554e14f788cc128f51ff9a015fe5ba2b738773e9e94"
EXPECTED_ERRORS = 124
EXPECTED_WARNINGS = 349


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
        "frontier_producer",
        "qym_probe15_frontier_producer_p14.py",
        "65f869c7740b741a2536cc92efb2b27c6cac532013bc028995accfb8165b71fb",
        "470a35e603043603a16c2b0c00a8bd6319f26beb",
        8_554, 188, 7, 7, 7, 7,
        "fa8bc5b346eaf9c613d153598a03606a3bc26dd44502ab46157235d1f3b92e29",
        "71b57fd2e95dc47cdd792514e17af74cf2de86f8",
        2_940_877, 62_169,
    ),
    Component(
        "contdiff_cc579",
        "qym-probe15-contdiff-p14-reanchored/qym_probe15_contdiff_p14_reanchored.py",
        "ebcf53a6049532ca4d970fab504dca977d433642e53ca16c05d1270f9f0c9e03",
        "b7d39fe8eadf127e5e48852d78d3792abd2fc930",
        22_610, 461, 4, 4, 4, 3,
        "29c4ff78d67059eaebd6acc2990b9130225728f84d7c33b339ca1fc6180abbfb",
        "e4566869097f785ed1f91c63ceee1756c2e93fee",
        2_940_490, 62_161,
    ),
    Component(
        "tail7",
        "qym-probe15-tail7-p14-sequenced/qym_probe15_tail7_p14_sequenced.py",
        "c072aa5bda929b4c28a94cb4072d78dfafd778248ef622db5ba504a9553cedd8",
        "015e222daa4ed87731d9ae5655e68b7fa3ea8912",
        13_437, 313, 7, 7, 7, 7,
        "c305d8a1db0310f9df09acff695ade607209acc79302139332a08374631e6580",
        "2f48658f7a2fd4d351824ae11a791f1f4ba2221e",
        2_940_456, 62_160,
    ),
    Component(
        "cusp_radicand",
        "qym-probe15-cusp-radicand-p14-sequenced/qym_probe15_cusp_radicand_p14_sequenced.py",
        "2d7f38cb13a264206d716ac0b16113f50c749e6db80d4ab904dabf84ea367daa",
        "3504a105a6ddfc696818842d2e521f2a81e0bb07",
        11_109, 41, 2, 2, 9, 8,
        "fc8dcf3b76a29e32af848c0c5411d2368f74ef351b9cbe4ac83922653e0d941a",
        "9463422d2e06ca21abb693dd446e3c84f05599d5",
        2_940_734, 62_171,
    ),
    Component(
        "prior671f_refinements",
        "qym-probe15-prior671f-refinements-p14-static/qym_probe15_prior671f_refinements_p14_static.py",
        "0804abaa20320f713f922843c758d4e297a6b0722bae6be48216a084e891e7b3",
        "0d2735b9cd4290d0bfd150a26a2ad3d745e4fb92",
        11_641, 98, 6, 6, 6, 6,
        "370280e74ac86101ed1f787b17cec2fe85677882c95dc0a34c6448c31f4178fc",
        "e79b780e06ba5422edfdc787401a65d8c10d5481",
        2_940_557, 62_161,
    ),
)

EXPECTED_RULES = 26
EXPECTED_OCCURRENCES = 26
EXPECTED_OWNED_DIAGNOSTICS = 33
EXPECTED_DIRECT_DIAGNOSTICS = 31


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
    name = "_qym_probe15_integrated_" + component.label
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
    for item in loaded:
        standalone, _ = apply_rule_set(source, item, False)
        if shape(standalone.encode("utf-8")) != standalone_shape(item.component):
            raise RuntimeError(f"{item.component.label}: standalone output drift")
        for rule in item.rules:
            if source.count(rule.old) != rule.occurrences:
                raise RuntimeError(f"{item.component.label}:{rule.label}: base anchor drift")
            start = source.find(rule.old)
            spans.append((start, start + len(rule.old), item.component.label, rule.label))
    overlaps: list[tuple[object, object]] = []
    for left, right in itertools.combinations(spans, 2):
        if left[2] != right[2] and max(left[0], right[0]) < min(left[1], right[1]):
            overlaps.append((left, right))
    if overlaps:
        raise RuntimeError(f"cross-component source-span collisions: {overlaps}")
    return {"source_spans": len(spans), "cross_component_overlaps": 0}


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
    if count != 120 or hashes != {OUTPUT_SHA256}:
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
            raise RuntimeError(f"exact Probe14 {name} sidecar gate failed")
    if exit_raw.strip() != b"1" or panic_raw:
        raise RuntimeError("exact Probe14 exit/panic gate failed")
    result = json.loads(result_raw)
    required = {
        "github_sha": TRIGGER_SHA,
        "candidate_qym_sha256": INPUT_SHA256,
        "candidate_qym_blob": INPUT_GIT_BLOB,
        "log_sha256": LOG_SHA256,
        "exit": 1,
        "error_headers": EXPECTED_ERRORS,
        "warning_headers": EXPECTED_WARNINGS,
    }
    for key, expected in required.items():
        if result.get(key) != expected:
            raise RuntimeError(f"Probe14 result field mismatch: {key}")
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
        raise RuntimeError("Probe14 diagnostic totals mismatch")
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
    parser.add_argument("--probe14-result", type=Path, required=True)
    parser.add_argument("--probe14-log", type=Path, required=True)
    parser.add_argument("--probe14-error-headers", type=Path, required=True)
    parser.add_argument("--probe14-diagnostics", type=Path, required=True)
    parser.add_argument("--probe14-exit", type=Path, required=True)
    parser.add_argument("--probe14-panic-lines", type=Path, required=True)
    args = parser.parse_args()

    preflight((args.output, args.audit))
    authority = verify_authority(
        args.probe14_result.read_bytes(),
        args.probe14_log.read_bytes(),
        args.probe14_error_headers.read_bytes(),
        args.probe14_diagnostics.read_bytes(),
        args.probe14_exit.read_bytes(),
        args.probe14_panic_lines.read_bytes(),
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
