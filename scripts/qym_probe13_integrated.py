#!/usr/bin/env python3
"""Fail-closed exact-P12 integrator for the four frozen Probe13 components.

The component modules are hash checked before import.  Their declarative
``RULES`` are composed directly, so standalone authority gates remain intact.
The CLI also pins the terminal Probe12 sidecars, replays all 24 component
orders and matching inverses, and preflights two fresh distinct outputs before
performing any write.  It never invokes Lean, Lake, Git, or the network.
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
SCHEMA = "qym-probe13-integrated-exact-terminal-p12-v1"
ACTIVATION = False
PACKAGE_DIR = Path(__file__).resolve().parent

INPUT_SHA256 = "4a123f69912bd7ce2ab070433f8cad0ecc284652a9cbab634def1936e9037212"
INPUT_GIT_BLOB = "76dd931638b9a6ad50ee764c65cd14489e8be310"
INPUT_BYTES = 2_936_558
INPUT_LF = 62_068
OUTPUT_SHA256 = "92e91734eb4b1d406d854a6021c815636eff6cf0aa2f4924e710249a583ebe3b"
OUTPUT_GIT_BLOB = "5c895f906b516366653aaf6fc459825e89045076"
OUTPUT_BYTES = 2_938_395
OUTPUT_LF = 62_112

LOG_SHA256 = "62ce7c1b4ec23a23d690c64d49e45901faec66ff751d86e314e669b8c876c398"
HEADERS_SHA256 = "0cebf8d7bbcb923165a13f68f2afbbef1843bb26d77e072252c570b8e77b0dd9"
DIAGNOSTICS_SHA256 = "16b69f25e53f28d028cbefca21d5401e25dbfaa2847bdfdc8f7532034690ca23"
EXPECTED_ERRORS = 183
EXPECTED_WARNINGS = 350


@dataclass(frozen=True)
class Component:
    label: str
    relative_path: str
    helper_sha256: str
    helper_git_blob: str
    expected_rules: int
    expected_occurrences: int
    expected_diagnostics: int
    standalone_output_sha256: str


COMPONENTS: tuple[Component, ...] = (
    Component(
        "probe13_early",
        "qym-probe13-early-p12-conditional/qym_probe13_early_p12_conditional.py",
        "5462da0d1e49fc9f5769eeaf9052515cc905cdd55740dc55c3d930992d878210",
        "d5c9d2dca629c25055934d26ff651c60a205215d",
        5, 5, 5,
        "96bec0509b3aa2d598450f15c9f691a99f26f82b4674fb3bb1e0e5ff04e6dc56",
    ),
    Component(
        "probe13_50k_direct",
        "qym-probe13-50k50599-p12-reanchored/qym_probe13_50k50599_p12_reanchored.py",
        "a2eacbaebd1f3fddcb865a551613ea8ebbcdf12d74869be2b61c663a0891ed50",
        "42604c79d17e496024e6c974543a10a896c2bb07",
        4, 4, 5,
        "9fd2c7c432af883647c3c5113c8ae13454d40c147148428db54c471a91ba1e84",
    ),
    Component(
        "probe13_mid_highleverage",
        "qym-probe13-highleverage-instances/qym_probe13_highleverage_instances.py",
        "e29672a27f2e6421426b73350655b3bae5dca187a8ab2fe39ea023cdf19ec47e",
        "40336fc8ecbcb7bd1920487a2faf324f608b17a1",
        2, 2, 7,
        "2233d00552ec7fb81e2e2ba5bda585db1bd8945dc75be098ce15a618f8a4177b",
    ),
    Component(
        "probe13_tail",
        "qym-probe13-tail-p12-direct/qym_probe13_tail_p12_direct.py",
        "11f19ecfabdde4da519321e133fd1a2265bedc7784cdd729e8dd05fbf310cc48",
        "0a657e6a7765b06937a76f29d1b25d9c5d659853",
        12, 12, 13,
        "6b1ecbc494cbaaa71a3507e604594c7ffd173ee5ebaa7e5a6f42dab4dd74b823",
    ),
)

EXPECTED_RULES = 23
EXPECTED_OCCURRENCES = 23
EXPECTED_DIAGNOSTICS = 30


@dataclass(frozen=True)
class Loaded:
    component: Component
    path: Path
    module: ModuleType
    rules: tuple[object, ...]


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
    if inverse:
        values = (OUTPUT_SHA256, OUTPUT_GIT_BLOB, OUTPUT_BYTES, OUTPUT_LF)
    else:
        values = (INPUT_SHA256, INPUT_GIT_BLOB, INPUT_BYTES, INPUT_LF)
    return {
        "sha256": values[0], "git_blob": values[1], "bytes": values[2],
        "lf": values[3], "cr": False, "nul": False, "bom": False,
        "terminal_lf": True,
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
    exact = [p for p in seen if sha256(p.read_bytes()) == component.helper_sha256]
    if len(exact) != 1:
        observed = {str(p): sha256(p.read_bytes()) for p in seen}
        raise RuntimeError(f"{component.label}: exact helper resolution failed: {observed}")
    raw = exact[0].read_bytes()
    if git_blob(raw) != component.helper_git_blob:
        raise RuntimeError(f"{component.label}: helper blob mismatch")
    return exact[0]


def import_component(component: Component, path: Path) -> ModuleType:
    if sha256(path.read_bytes()) != component.helper_sha256:
        raise RuntimeError(f"{component.label}: changed before import")
    name = "_qym_probe13_integrated_" + component.label
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
            ("INPUT_SHA256", INPUT_SHA256), ("INPUT_GIT_BLOB", INPUT_GIT_BLOB),
            ("INPUT_BYTES", INPUT_BYTES), ("INPUT_LF", INPUT_LF),
            ("OUTPUT_SHA256", component.standalone_output_sha256),
        ):
            if getattr(module, key, None) != expected:
                raise RuntimeError(f"{component.label}: runtime {key} mismatch")
        if getattr(module, "ACTIVATION", False) is not False:
            raise RuntimeError(f"{component.label}: activation must be false")
        rules = tuple(getattr(module, "RULES", ()))
        if len(rules) != component.expected_rules:
            raise RuntimeError(f"{component.label}: rule count mismatch")
        if sum(int(rule.occurrences) for rule in rules) != component.expected_occurrences:
            raise RuntimeError(f"{component.label}: occurrence count mismatch")
        for rule in rules:
            if not all(isinstance(getattr(rule, key, None), str) for key in ("label", "old", "new")):
                raise RuntimeError(f"{component.label}: malformed declarative rule")
        loaded.append(Loaded(component, path, module, rules))
    return tuple(loaded)


def apply_rule_set(text: str, item: Loaded, inverse: bool):
    rows = []
    rules = tuple(reversed(item.rules)) if inverse else item.rules
    for rule in rules:
        old, new = (rule.new, rule.old) if inverse else (rule.old, rule.new)
        count = text.count(old)
        if count != int(rule.occurrences):
            raise RuntimeError(f"{item.component.label}:{rule.label}: anchor count {count}")
        text = text.replace(old, new)
        rows.append({"component": item.component.label, "label": rule.label,
                     "inverse": inverse, "occurrences": count})
    return text, rows


def apply_order(text: str, loaded: tuple[Loaded, ...], order: tuple[int, ...], inverse: bool):
    result = text
    rows: list[dict[str, object]] = []
    indices = tuple(reversed(order)) if inverse else order
    for index in indices:
        result, component_rows = apply_rule_set(result, loaded[index], inverse)
        rows.extend(component_rows)
    return result, rows


def transform(text: str, inverse: bool = False):
    raw = text.encode()
    if shape(raw) != expected_shape(inverse):
        raise RuntimeError(f"exact {'Probe13' if inverse else 'Probe12'} candidate gate failed")
    before = trust(text)
    if any(before.values()):
        raise RuntimeError(f"source trust0 failure: {before}")
    loaded = load_components()
    canonical = tuple(range(len(loaded)))
    result, rows = apply_order(text, loaded, canonical, inverse)
    if shape(result.encode()) != expected_shape(not inverse):
        raise RuntimeError("integrated output identity mismatch")
    after = trust(result)
    if before != after or any(after.values()):
        raise RuntimeError(f"integrated trust drift: {before} -> {after}")
    if len(rows) != EXPECTED_RULES or sum(int(r["occurrences"]) for r in rows) != EXPECTED_OCCURRENCES:
        raise RuntimeError("integrated rule totals mismatch")
    return result, rows


def verify_authority(log: bytes, headers: bytes, diagnostics: bytes) -> dict[str, object]:
    for label, raw, expected in (
        ("log", log, LOG_SHA256), ("headers", headers, HEADERS_SHA256),
        ("diagnostics", diagnostics, DIAGNOSTICS_SHA256),
    ):
        if sha256(raw) != expected:
            raise RuntimeError(f"exact Probe12 {label} sidecar gate failed")
    rows = [json.loads(line) for line in diagnostics.decode().splitlines() if line]
    errors = sum(row.get("severity") == "error" for row in rows)
    warnings = sum(row.get("severity") == "warning" for row in rows)
    if (errors, warnings) != (EXPECTED_ERRORS, EXPECTED_WARNINGS):
        raise RuntimeError(f"Probe12 diagnostic totals mismatch: {(errors, warnings)}")
    return {"log_sha256": LOG_SHA256, "headers_sha256": HEADERS_SHA256,
            "diagnostics_sha256": DIAGNOSTICS_SHA256,
            "errors": errors, "warnings": warnings, "panic": 0, "exit": 1}


def audit_all_orders(source: str, loaded: tuple[Loaded, ...]) -> dict[str, object]:
    expected = expected_shape(True)
    count = 0
    for order in itertools.permutations(range(len(loaded))):
        forward, _ = apply_order(source, loaded, order, False)
        if shape(forward.encode()) != expected:
            raise RuntimeError(f"component-order output drift: {order}")
        restored, _ = apply_order(forward, loaded, order, True)
        if restored != source:
            raise RuntimeError(f"component-order inverse drift: {order}")
        count += 1
    return {"orders": count, "unique_outputs": 1,
            "all_output_sha256": OUTPUT_SHA256,
            "matching_reverse_inverse_exact": True}


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
    parser.add_argument("--probe12-log", type=Path, required=True)
    parser.add_argument("--probe12-error-headers", type=Path, required=True)
    parser.add_argument("--probe12-diagnostics", type=Path, required=True)
    args = parser.parse_args()
    preflight((args.output, args.audit))
    authority = verify_authority(args.probe12_log.read_bytes(),
                                 args.probe12_error_headers.read_bytes(),
                                 args.probe12_diagnostics.read_bytes())
    source_raw = args.input.read_bytes()
    source = source_raw.decode("utf-8", errors="strict")
    result, rows = transform(source, args.inverse)
    restored, inverse_rows = transform(result, not args.inverse)
    if restored.encode() != source_raw:
        raise RuntimeError("canonical inverse is not byte exact")
    loaded = load_components()
    order_audit = audit_all_orders(source if not args.inverse else result, loaded)
    record = {
        "schema": SCHEMA,
        "status": "STATIC_PASS_EXACT_COMPOSITION_NOT_LEAN_EXECUTED",
        "activation": ACTIVATION, "promotion": False,
        "mode": "inverse" if args.inverse else "forward",
        "authority": authority,
        "source": shape(source_raw), "result": shape(result.encode()),
        "components": [asdict(component) for component in COMPONENTS],
        "repair_families": EXPECTED_RULES,
        "repair_occurrences": EXPECTED_OCCURRENCES,
        "diagnostic_ownership_records": EXPECTED_DIAGNOSTICS,
        "rules": rows, "matching_inverse_rules": inverse_rows,
        "inverse_byte_equal": True, "all_order_audit": order_audit,
        "trust": trust(result),
        "execution": {"lean": False, "lake": False, "git": False,
                      "network": False, "remote": False,
                      "repository_source_mutation": False},
    }
    # Both byte strings exist before either destination is touched.
    result_raw = result.encode()
    audit_raw = (json.dumps(record, indent=2) + "\n").encode()
    args.output.write_bytes(result_raw)
    args.audit.write_bytes(audit_raw)
    print(json.dumps({"result": record["result"], "orders": order_audit["orders"]}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
