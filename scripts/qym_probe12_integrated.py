#!/usr/bin/env python3
"""Exact-P11-gated Probe12 integrator for four frozen component helpers.

The module exposes an import-safe ``transform(text, inverse=False)`` API and a
fail-closed CLI.  Forward mode accepts only the exact terminal Probe11 bytes;
inverse mode accepts only the exact integrated Probe12 bytes.  Helpers and the
two helper-import dependencies are hash checked before any module executes.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import re
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from types import ModuleType


sys.dont_write_bytecode = True

SCHEMA = "qym-probe12-integrated-v1-exact-terminal-probe11"
PACKAGE_DIR = Path(__file__).resolve().parent

INPUT_SHA256 = "d8290febb2b1c69cc8b911bcb672303beede1b87db290bd37c6608e39356cf25"
INPUT_GIT_BLOB = "9b5ba50acc8e2f3d6f55cf8cef6fc505926410cd"
INPUT_BYTES = 2_928_376
INPUT_LF = 61_891

OUTPUT_SHA256 = "4a123f69912bd7ce2ab070433f8cad0ecc284652a9cbab634def1936e9037212"
OUTPUT_GIT_BLOB = "76dd931638b9a6ad50ee764c65cd14489e8be310"
OUTPUT_BYTES = 2_936_558
OUTPUT_LF = 62_068

LOG_SHA256 = "474f153278507d0ead7fe21675f326def15556281bd7b5cf67392836ea5ea97e"
HEADERS_SHA256 = "b0fe7508ba87fc324236cce71b74c59d042a0833ec1c101a1ae625a1f24dd4e6"
DIAGNOSTICS_SHA256 = "d9259b316d1c1317ea7e11f8f0370feaabacb3a2ae6066c3133ab748a2dee504"
EXPECTED_ERRORS = 217
EXPECTED_WARNINGS = 350


@dataclass(frozen=True)
class FilePin:
    relative_path: str
    sha256: str


@dataclass(frozen=True)
class Component:
    label: str
    helper: FilePin
    expected_rules: int
    expected_occurrences: int
    expected_diagnostics: int
    standalone_output_sha256: str
    dependencies: tuple[FilePin, ...] = ()


COMPONENTS: tuple[Component, ...] = (
    Component(
        label="probe12_early_frontier",
        helper=FilePin(
            "qym-probe12-early-frontier-p11-conditional/"
            "qym_probe12_early_frontier_p11_conditional.py",
            "35b5ccf5f04899c810ca798cbcf700230fdfc4b930d16ab5d9cf646584954215",
        ),
        expected_rules=8,
        expected_occurrences=8,
        expected_diagnostics=11,
        standalone_output_sha256=(
            "0a6544bc32715b99f4117854073efb4acf6afb4fa1e6293cbb1060033af368da"
        ),
    ),
    Component(
        label="probe12_36k42k",
        helper=FilePin(
            "qym-probe12-36k42k-p11-reanchored/"
            "qym_probe12_36k42k_p11_reanchored.py",
            "5bd02f57232ac30c336b3e13574b7cba4dc4b0998f159e3fdebd41ed6354a365",
        ),
        expected_rules=13,
        expected_occurrences=13,
        expected_diagnostics=14,
        standalone_output_sha256=(
            "54c9a1ebff4bc2de215568b1e25e5b30ecfd17d0dee0ab8c1fc302603518eaf8"
        ),
    ),
    Component(
        label="probe12_43k49k",
        helper=FilePin(
            "qym-probe12-43k49k-p11-conditional/"
            "qym_probe12_43k49k_p11_conditional.py",
            "5070ada686ac425b76403ae53210e586bda305a8a70606d6d3bc6529ff2b2523",
        ),
        expected_rules=18,
        expected_occurrences=18,
        expected_diagnostics=26,
        standalone_output_sha256=(
            "a4246ffed06477b39460dd32db7b18c5974d01ef3cf7fa95143a98cb20347f6e"
        ),
        dependencies=(
            FilePin(
                "qym-probe12-43k49k-p10-conditional/"
                "qym_probe12_43k49k_p10_conditional.py",
                "5cea81a9deb981609655d767487a3cbb5fda032849869902ba074d8729fa976d",
            ),
        ),
    ),
    Component(
        label="probe12_50k53k",
        helper=FilePin(
            "qym-probe12-50k53k-p11-conditional/"
            "qym_probe12_50k53k_p11_conditional.py",
            "5352b37ec754a5131164e91649b54a277b5d257258bc316f653b6d218bfb63c8",
        ),
        expected_rules=7,
        expected_occurrences=7,
        expected_diagnostics=7,
        standalone_output_sha256=(
            "d71251281812bfc7ac9e8fc026417641a8402508f829de3fade71b44f3d04f61"
        ),
    ),
    Component(
        label="probe12_52k61k",
        helper=FilePin(
            "qym-probe12-52k61k-p11-conditional/"
            "qym_probe12_52k61k_p11_conditional.py",
            "7066e3297bd171ec58a4547ed426a8d9a6228abf4de78bf3ad203d880ef7f795",
        ),
        expected_rules=20,
        expected_occurrences=20,
        expected_diagnostics=22,
        standalone_output_sha256=(
            "23be98d651a77ea06c843f5cb492142caf616f9f22db1e0adb49a6d7e379aeaa"
        ),
        dependencies=(
            FilePin(
                "qym-probe12-52k61k-p10-conditional/"
                "qym_probe12_52k61k_p10_conditional.py",
                "dde4c4df0473bbbd1da69bce9968f00b0859d045d254740b5852f72e5b489545",
            ),
        ),
    ),
)

EXPECTED_RULES = 66
EXPECTED_OCCURRENCES = 66
EXPECTED_DIAGNOSTICS = 80


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
    if inverse:
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


def expected_result_shape(inverse: bool) -> dict[str, object]:
    return expected_shape(not inverse)


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


def path_candidates(relative_path: str) -> tuple[Path, ...]:
    candidates = (
        PACKAGE_DIR / relative_path,
        PACKAGE_DIR.parent / relative_path,
        PACKAGE_DIR.parents[1] / "work" / relative_path,
    )
    unique: list[Path] = []
    for path in candidates:
        resolved = path.resolve()
        if resolved not in unique:
            unique.append(resolved)
    return tuple(unique)


def resolve_pin(pin: FilePin) -> Path:
    existing = [path for path in path_candidates(pin.relative_path) if path.is_file()]
    exact = [path for path in existing if sha256(path.read_bytes()) == pin.sha256]
    if len(exact) != 1:
        observed = {str(path): sha256(path.read_bytes()) for path in existing}
        raise RuntimeError(
            f"exact file resolution failed for {pin.relative_path}: {observed}"
        )
    return exact[0]


def snapshot_directories(paths: tuple[Path, ...]) -> dict[str, dict[str, object]]:
    roots = sorted({path.parent for path in paths}, key=lambda path: str(path))
    rows: dict[str, dict[str, object]] = {}
    for root in roots:
        for path in sorted(root.rglob("*"), key=lambda item: str(item)):
            if not path.is_file():
                continue
            raw = path.read_bytes()
            rows[str(path)] = {
                "sha256": sha256(raw),
                "bytes": len(raw),
                "mtime_ns": path.stat().st_mtime_ns,
            }
    return rows


def import_exact(component: Component, path: Path) -> ModuleType:
    raw = path.read_bytes()
    if sha256(raw) != component.helper.sha256:
        raise RuntimeError(f"{component.label} helper changed before import")
    name = "_qym_probe12_integrated_" + component.label
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot import {component.label}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def load_components() -> tuple[tuple[Loaded, ...], dict[str, object]]:
    helper_paths = tuple(resolve_pin(component.helper) for component in COMPONENTS)
    dependency_paths = tuple(
        resolve_pin(pin) for component in COMPONENTS for pin in component.dependencies
    )
    tracked_paths = helper_paths + dependency_paths
    before = snapshot_directories(tracked_paths)
    loaded: list[Loaded] = []
    for component, path in zip(COMPONENTS, helper_paths):
        module = import_exact(component, path)
        for key, expected in (
            ("INPUT_SHA256", INPUT_SHA256),
            ("INPUT_GIT_BLOB", INPUT_GIT_BLOB),
            ("INPUT_BYTES", INPUT_BYTES),
            ("INPUT_LF", INPUT_LF),
            ("OUTPUT_SHA256", component.standalone_output_sha256),
        ):
            if getattr(module, key, None) != expected:
                raise RuntimeError(f"{component.label} runtime {key} mismatch")
        if not callable(getattr(module, "transform", None)):
            raise RuntimeError(f"{component.label} transform API missing")
        rules = tuple(getattr(module, "RULES", ()))
        if len(rules) != component.expected_rules:
            raise RuntimeError(f"{component.label} rule count mismatch")
        if sum(int(rule.occurrences) for rule in rules) != component.expected_occurrences:
            raise RuntimeError(f"{component.label} occurrence count mismatch")
        loaded.append(Loaded(component, path, module, rules))
    after = snapshot_directories(tracked_paths)
    if after != before:
        raise RuntimeError("component import mutated a helper or dependency directory")
    return tuple(loaded), {
        "helper_paths": [str(path) for path in helper_paths],
        "dependency_paths": [str(path) for path in dependency_paths],
        "exact_hashes_checked_before_import": True,
        "tree_snapshot_unchanged_after_import": True,
        "dont_write_bytecode": sys.dont_write_bytecode,
    }


def apply_loaded(
    text: str, loaded: tuple[Loaded, ...], inverse: bool
) -> tuple[str, list[dict[str, object]]]:
    order = tuple(reversed(loaded)) if inverse else loaded
    result = text
    records: list[dict[str, object]] = []
    for item in order:
        transformed = item.module.transform(result, inverse=inverse)
        if not isinstance(transformed, tuple) or len(transformed) != 2:
            raise RuntimeError(f"{item.component.label} transform contract drift")
        result, rule_audit = transformed
        if len(rule_audit) != item.component.expected_rules:
            raise RuntimeError(f"{item.component.label} rule audit count mismatch")
        occurrences = sum(int(row.get("occurrences", 0)) for row in rule_audit)
        if occurrences != item.component.expected_occurrences:
            raise RuntimeError(f"{item.component.label} occurrence audit mismatch")
        records.append(
            {
                "component": item.component.label,
                "inverse": inverse,
                "rules": len(rule_audit),
                "occurrences": occurrences,
                "diagnostics": item.component.expected_diagnostics,
            }
        )
    return result, records


def transform(text: str, inverse: bool = False) -> tuple[str, list[dict[str, object]]]:
    source_raw = text.encode("utf-8")
    actual_source = shape(source_raw)
    if actual_source != expected_shape(inverse):
        raise RuntimeError(f"exact {'Probe12' if inverse else 'Probe11'} gate failed")
    source_trust = trust(text)
    if any(source_trust.values()):
        raise RuntimeError(f"source is not trust0: {source_trust}")
    loaded, _ = load_components()
    result, records = apply_loaded(text, loaded, inverse)
    result_raw = result.encode("utf-8")
    if shape(result_raw) != expected_result_shape(inverse):
        raise RuntimeError("integrated output identity mismatch")
    result_trust = trust(result)
    if result_trust != source_trust or any(result_trust.values()):
        raise RuntimeError(f"integrated trust drift: {source_trust} -> {result_trust}")
    if sum(int(row["rules"]) for row in records) != EXPECTED_RULES:
        raise RuntimeError("integrated rule total mismatch")
    if sum(int(row["occurrences"]) for row in records) != EXPECTED_OCCURRENCES:
        raise RuntimeError("integrated occurrence total mismatch")
    if sum(int(row["diagnostics"]) for row in records) != EXPECTED_DIAGNOSTICS:
        raise RuntimeError("integrated diagnostic ownership total mismatch")
    return result, records


def write_new(path: Path, raw: bytes) -> None:
    if path.exists():
        raise RuntimeError(f"refusing to overwrite {path}")
    if not path.parent.is_dir():
        raise RuntimeError(f"output parent does not exist: {path.parent}")
    path.write_bytes(raw)


def preflight_new_outputs(paths: tuple[Path, ...]) -> None:
    resolved = tuple(path.resolve() for path in paths)
    if len(set(resolved)) != len(resolved):
        raise RuntimeError("output and audit paths must be distinct")
    for path, canonical in zip(paths, resolved):
        if canonical.exists():
            raise RuntimeError(f"refusing to overwrite {path}")
        if not canonical.parent.is_dir():
            raise RuntimeError(f"output parent does not exist: {path.parent}")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--audit", type=Path, required=True)
    parser.add_argument("--inverse", action="store_true")
    args = parser.parse_args()

    # No transform or write may begin until both destinations are independently
    # proven fresh.  This prevents a valid candidate from being stranded when
    # the second write target is invalid or aliases the first one.
    preflight_new_outputs((args.output, args.audit))
    source_raw = args.input.read_bytes()
    source_text = source_raw.decode("utf-8", errors="strict")
    result, records = transform(source_text, inverse=args.inverse)
    result_raw = result.encode("utf-8")

    # Exercise the matching opposite direction before any output is written.
    restored, inverse_records = transform(result, inverse=not args.inverse)
    roundtrip_equal = restored.encode("utf-8") == source_raw
    if not roundtrip_equal:
        raise RuntimeError("matching inverse is not byte exact")
    _, import_audit = load_components()
    record = {
        "schema": SCHEMA,
        "status": "STATIC_PASS_EXACT_COMPOSITION_NOT_LEAN_EXECUTED",
        "activation": False,
        "promotion": False,
        "mode": "inverse" if args.inverse else "forward",
        "authority": {
            "candidate_sha256": INPUT_SHA256,
            "candidate_git_blob": INPUT_GIT_BLOB,
            "log_sha256": LOG_SHA256,
            "headers_sha256": HEADERS_SHA256,
            "diagnostics_sha256": DIAGNOSTICS_SHA256,
            "errors": EXPECTED_ERRORS,
            "warnings": EXPECTED_WARNINGS,
        },
        "source": shape(source_raw),
        "result": shape(result_raw),
        "components": [asdict(component) for component in COMPONENTS],
        "repair_families": EXPECTED_RULES,
        "repair_occurrences": EXPECTED_OCCURRENCES,
        "diagnostic_ownership_records": EXPECTED_DIAGNOSTICS,
        "component_order": [record["component"] for record in records],
        "rules": records,
        "matching_inverse_rules": inverse_records,
        "inverse_byte_equal": roundtrip_equal,
        "trust": trust(result),
        "import_safety": import_audit,
        "execution": {
            "lean": False,
            "lake": False,
            "git": False,
            "network": False,
            "remote": False,
            "repository_source_mutation": False,
        },
    }
    write_new(args.output, result_raw)
    write_new(args.audit, (json.dumps(record, indent=2) + "\n").encode("utf-8"))
    print(json.dumps({"mode": record["mode"], "result": record["result"]}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
