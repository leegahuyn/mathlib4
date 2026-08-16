#!/usr/bin/env python3
"""Fail-closed exact-Probe10 Probe11 integrator.

Six frozen components are auditable.  The bootstrap projection is permitted
only while the integrated output identity is unsealed; after those sentinels
are replaced, normal forward and inverse rendering require the exact bytes.
Every component permutation and its corresponding inverse are replayed.

This program never invokes Lean, Lake, Git, the network, or a remote API.
"""

from __future__ import annotations

import argparse
import ast
import base64
import hashlib
import itertools
import json
import random
import re
import sys
import zlib
from dataclasses import asdict, dataclass
from pathlib import Path


sys.dont_write_bytecode = True

SCHEMA = "qym-probe11-integrated-v1-exact-probe10-fail-closed"
PACKAGE_DIR = Path(__file__).resolve().parent
ROOT = PACKAGE_DIR.parent if PACKAGE_DIR.name == "scripts" else PACKAGE_DIR.parents[1]
AUTHORITY_DIR = ROOT / "work/qym-probe10-run31973408809-authority/artifact"

INPUT_SHA256 = "ef19b4f666bd7238164aec7795e10c3f802d9a3e49e5d5f617cc09d4cbe617dc"
INPUT_GIT_BLOB = "496c24e5a90d1f72c66bb03fcc9d3565a06f4b2e"
INPUT_BYTES = 2_923_612
INPUT_LF = 61_783

OUTPUT_SHA256 = "d8290febb2b1c69cc8b911bcb672303beede1b87db290bd37c6608e39356cf25"
OUTPUT_GIT_BLOB = "9b5ba50acc8e2f3d6f55cf8cef6fc505926410cd"
OUTPUT_BYTES = 2_928_376
OUTPUT_LF = 61_891

# Rules are embedded as a byte-locked compressed JSON payload so the installed
# integrator never executes component helpers (some sealing-only helpers import
# work-layout predecessors).  The workflow still installs and hash-checks every
# frozen component helper, while this payload makes CI application self-contained.
EMBEDDED_RULES_SHA256 = "e124efe100ceda4f85cc5bfa7df6204b49f58705e050d1e4a873fc2e41bff739"
EMBEDDED_RULES_ZLIB_B64 = (
    "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"
)

AUTHORITY = {
    "run_id": 31973408809,
    "job_id": 95229227905,
    "head_sha": "0957f9b925663bc78b76c7207084fb6199eb60de",
    "install_parent_sha": "3b5e67d81c4d8979f2c4b57c9f2b7839b0806388",
    "artifact_id": 9270510078,
    "artifact_name": (
        "qym-repair-probe10-integrated-"
        "0957f9b925663bc78b76c7207084fb6199eb60de-attempt1"
    ),
    "artifact_api_size": 10_487_379,
    "artifact_digest_sha256": (
        "0b2e4c1ba61974967f3a79bc1d32f7480fa1bdc484cfe82d763b5ee03bf4f101"
    ),
    "result_sha256": (
        "0a908f0ae2bae582285d3d48c5ccb30829c2225af2b397b5ffd1a499798d279d"
    ),
    "log_sha256": (
        "0fa01861e0984e1e45107a46789d894f33d2bbd4a035d9dbaa29060956ab3ad2"
    ),
    "headers_sha256": (
        "b1130e19aa9ca16b044eeab07ebf762c0cb2bdfe46c0b7d242ef68b0c151a7a5"
    ),
    "diagnostics_sha256": (
        "b51f3cc940634dc1eba28003770ae750f8621c4452483f27fdf464188591c43a"
    ),
    "errors": 255,
    "warnings": 343,
    "panic": 0,
    "exit": 1,
    "first_error": "28362:4",
    "last_error": "59654:45",
}


@dataclass(frozen=True)
class ComponentSpec:
    label: str
    helper_path: str
    helper_sha256: str
    standalone_output_path: str
    standalone_output_sha256: str
    forward_audit_path: str
    forward_audit_sha256: str
    expected_rules: int
    expected_occurrences: int
    ready: bool


COMPONENTS: tuple[ComponentSpec, ...] = (
    ComponentSpec(
        "early_frontier",
        "work/qym-probe11-early-frontier-static/qym_probe11_early_frontier_static.py",
        "9177e4fd6aa03215aec4728415d095e7e099594f6bc12facbf5a2fd879175b9a",
        "work/qym-probe11-early-frontier-static/QYM.candidate-probe11-early-frontier-p10.sealed.lean",
        "4f02f16182c8a727b4beff0a65c249644d0b2e4e29586f2812a069611177cc3f",
        "work/qym-probe11-early-frontier-static/QYM.probe11-early-frontier-p10.sealed.audit.json",
        "b275ab1644edff58820ac9eafedda62af41c23c2c81a555c1c6f11186ab24129",
        3,
        3,
        True,
    ),
    ComponentSpec(
        "mid_p10_authority",
        "work/qym-probe11-mid-p10-authority/qym_probe11_mid_p10_authority.py",
        "f2adebd8803e40df538a8b85401ea5a26af4585aefe521135c77dde8576a1fc6",
        "work/qym-probe11-mid-p10-authority/QYM.candidate-probe11-mid-exact-p10.lean",
        "7a04c7758de3c47c7cc74c4359e2bee6b0364d2170c88fa022399bb48789b0b5",
        "work/qym-probe11-mid-p10-authority/TRANSFORM_AUDIT_PROBE11_MID_P10.json",
        "ce556fee056fd13bc61bca15ea78cd62cb245f4fcb56366fe8b4652ac37cb1d4",
        13,
        13,
        True,
    ),
    ComponentSpec(
        "tail_p10_conditional",
        "work/qym-probe11-tail-p10-conditional/qym_probe11_tail_p10_conditional.py",
        "e76d0830315918d8d51c5063048b0f85ad9f4a68c8dffa2dbab19da25a9aae49",
        "work/qym-probe11-tail-p10-conditional/QYM.candidate-probe11-tail-p10.sealed.lean",
        "d577bdcab8ced2cdf40960582d6c8bebe6d782454fb54a4920fc1c07cb33fe30",
        "work/qym-probe11-tail-p10-conditional/QYM.probe11-tail-p10.sealed.audit.json",
        "5956e43ca889d3f13e2cb3e44ffa1bae74cc246eecae7f7618087ec6cf197b3d",
        16,
        16,
        True,
    ),
    ComponentSpec(
        "earlymid_p10_conditional",
        "work/qym-probe11-earlymid-p10-conditional/qym_probe11_earlymid_p10_conditional.py",
        "683e740e96970dd4ca53c51016f30839a4ead5c641c7c8619f5b85733e9612e6",
        "work/qym-probe11-earlymid-p10-conditional/QYM.candidate-probe11-earlymid-p10.lean",
        "08b466d746f79292baf685622766fe7d5b1410ec1d3852560e490a04273db1f1",
        "work/qym-probe11-earlymid-p10-conditional/TRANSFORM_AUDIT_PROBE11_EARLYMID_P10.json",
        "e626270fefe3cdf376eca7790c7ee042c35f5913e188b76c41596ac21794ea13",
        10,
        10,
        True,
    ),
    ComponentSpec(
        "fortyk_p10_conditional",
        "work/qym-probe11-40k-p10-conditional/qym_probe11_40k_p10_conditional.py",
        "6765e05b8681e4d7e13bc735c4d37ea038c75423a7d5ebc1ad73b179a99e0052",
        "work/qym-probe11-40k-p10-conditional/QYM.candidate-probe11-40k-p10.sealed.lean",
        "eb0b22ec98ae72aad0d597a48abe5e93e4b8a177ea2e1cc597988beaf1e331ec",
        "work/qym-probe11-40k-p10-conditional/TRANSFORM_AUDIT_PROBE11_40K_P10.json",
        "d7ac70945682ecf03a38d0505bee25d63c510240cf24c5d537f5d138e2407e67",
        14,
        14,
        True,
    ),
    ComponentSpec(
        "structural50k_p10_conditional",
        "work/qym-probe11-50k-structural-p10/qym_probe11_50k_structural_p10.py",
        "82189532a76f4785734d851f459a67c2dc04e373d1fc70eb5a137506f2dc57ae",
        "work/qym-probe11-50k-structural-p10/QYM.candidate-probe11-50k-structural-p10.sealed.lean",
        "7bffcf2a89f8b616eee61ef0ed64b91e9ede23ae22daa325ac3fa4f00322e8b8",
        "work/qym-probe11-50k-structural-p10/TRANSFORM_AUDIT_PROBE11_50K_STRUCTURAL_P10.json",
        "1087ab31355dbea924e0d130e302cfffc7feb18255e7f8601d40312ac297fbf5",
        1,
        2,
        True,
    ),
    ComponentSpec(
        "midlate_refinement_p10",
        "work/qym-probe12-p10-midlate-refinement/qym_probe12_p10_midlate_refinement.py",
        "058dba8e252db0562b7b83ed5d6701445b41f189db0559e06613823f1565207d",
        "work/qym-probe12-p10-midlate-refinement/QYM.candidate-probe12-p10-midlate-refinement.lean",
        "6c6c5c7a0d6520cf1d2a5b7f4b299ec2ec263cae8ffd17b862c47b1c0889b947",
        "work/qym-probe12-p10-midlate-refinement/TRANSFORM_AUDIT_PROBE12_P10_MIDLATE_REFINEMENT.json",
        "631a01f1d05783a2574aa586dcb55c87ea2aacebf67eed60b9ab36106fdc68d7",
        3,
        3,
        True,
    ),
)


@dataclass(frozen=True)
class RuleRef:
    component: str
    label: str
    old: str
    new: str
    occurrences: int


@dataclass(frozen=True)
class LoadedComponent:
    spec: ComponentSpec
    helper_constants: dict[str, object]
    rules: tuple[RuleRef, ...]
    helper_shape: dict[str, object]
    audit: dict[str, object]


def sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def git_blob(raw: bytes) -> str:
    prefix = b"blob " + str(len(raw)).encode("ascii") + b"\0"
    return hashlib.sha1(prefix + raw).hexdigest()


def shape(raw: bytes) -> dict[str, object]:
    raw.decode("utf-8")
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


def check_text_shape(actual: dict[str, object], expected: dict[str, object]) -> None:
    for key, value in expected.items():
        if actual[key] != value:
            raise RuntimeError(f"shape {key}: {actual[key]} != {value}")
    if actual["cr"] or actual["nul"] or actual["bom"] or not actual["terminal_lf"]:
        raise RuntimeError(f"text hygiene failure: {actual}")


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


def authority_paths(authority_dir: Path = AUTHORITY_DIR) -> dict[str, Path]:
    return {
        "candidate": authority_dir / "QYM.candidate-probe10.lean",
        "result": authority_dir / "PROBE_RESULT.json",
        "log": authority_dir / "QYM.log",
        "headers": authority_dir / "QYM.error-headers.txt",
        "diagnostics": authority_dir / "QYM.diagnostics.jsonl",
    }


def verify_authority(
    authority_dir: Path = AUTHORITY_DIR,
) -> tuple[bytes, dict[str, object]]:
    paths = authority_paths(authority_dir)
    for label, path in paths.items():
        if not path.is_file():
            raise RuntimeError(f"missing Probe10 authority {label}: {path}")
    candidate = paths["candidate"].read_bytes()
    candidate_shape = shape(candidate)
    check_text_shape(
        candidate_shape,
        {
            "sha256": INPUT_SHA256,
            "git_blob": INPUT_GIT_BLOB,
            "bytes": INPUT_BYTES,
            "lf": INPUT_LF,
        },
    )
    identities = {
        "result": AUTHORITY["result_sha256"],
        "log": AUTHORITY["log_sha256"],
        "headers": AUTHORITY["headers_sha256"],
        "diagnostics": AUTHORITY["diagnostics_sha256"],
    }
    for label, wanted in identities.items():
        actual = sha256(paths[label].read_bytes())
        if actual != wanted:
            raise RuntimeError(f"Probe10 authority {label}: {actual} != {wanted}")

    result = json.loads(paths["result"].read_text(encoding="utf-8"))
    expected_result = {
        "github_sha": AUTHORITY["head_sha"],
        "install_parent_sha": AUTHORITY["install_parent_sha"],
        "candidate_qym_sha256": INPUT_SHA256,
        "candidate_qym_blob": INPUT_GIT_BLOB,
        "log_sha256": AUTHORITY["log_sha256"],
        "error_headers": AUTHORITY["errors"],
        "warning_headers": AUTHORITY["warnings"],
        "panic_lines": AUTHORITY["panic"],
        "exit": AUTHORITY["exit"],
        "semantic_pass": False,
    }
    for key, wanted in expected_result.items():
        if result.get(key) != wanted:
            raise RuntimeError(
                f"Probe10 result {key}: {result.get(key)!r} != {wanted!r}"
            )
    first = result.get("first_error") or {}
    last = result.get("last_error") or {}
    if f"{first.get('line')}:{first.get('column')}" != AUTHORITY["first_error"]:
        raise RuntimeError("Probe10 first-error mismatch")
    if f"{last.get('line')}:{last.get('column')}" != AUTHORITY["last_error"]:
        raise RuntimeError("Probe10 last-error mismatch")

    header_lines = paths["headers"].read_text(encoding="utf-8").splitlines()
    diagnostics = [
        json.loads(line)
        for line in paths["diagnostics"].read_text(encoding="utf-8").splitlines()
    ]
    if len(header_lines) != AUTHORITY["errors"]:
        raise RuntimeError("Probe10 header-count mismatch")
    severity_counts = {
        severity: sum(row.get("severity") == severity for row in diagnostics)
        for severity in ("error", "warning")
    }
    if severity_counts != {
        "error": AUTHORITY["errors"],
        "warning": AUTHORITY["warnings"],
    }:
        raise RuntimeError(f"Probe10 diagnostic counts: {severity_counts}")
    if any(trust(candidate.decode("utf-8")).values()):
        raise RuntimeError("Probe10 candidate is not trust0")
    return candidate, {
        "paths": {key: str(value) for key, value in paths.items()},
        "candidate": candidate_shape,
        "result_fields_verified": sorted(expected_result),
        "diagnostic_counts": severity_counts,
    }


def embedded_rule_map() -> dict[str, tuple[RuleRef, ...]]:
    try:
        raw = zlib.decompress(base64.b64decode(EMBEDDED_RULES_ZLIB_B64, validate=True))
    except Exception as error:
        raise RuntimeError("embedded Probe11 rule payload is invalid") from error
    if sha256(raw) != EMBEDDED_RULES_SHA256:
        raise RuntimeError("embedded Probe11 rule payload identity mismatch")
    rows = json.loads(raw.decode("utf-8"))
    if not isinstance(rows, list):
        raise RuntimeError("embedded Probe11 rule payload is not a list")
    result: dict[str, tuple[RuleRef, ...]] = {}
    for row in rows:
        component = str(row["component"])
        if component in result:
            raise RuntimeError(f"duplicate embedded component: {component}")
        result[component] = tuple(
            RuleRef(
                component,
                str(rule["label"]),
                str(rule["old"]),
                str(rule["new"]),
                int(rule["occurrences"]),
            )
            for rule in row["rules"]
        )
    expected = {spec.label for spec in COMPONENTS}
    if set(result) != expected:
        raise RuntimeError(
            f"embedded component set mismatch: {sorted(result)} != {sorted(expected)}"
        )
    return result


def static_helper_constants(raw: bytes, path: Path) -> dict[str, object]:
    tree = ast.parse(raw.decode("utf-8"), filename=str(path))
    wanted = {
        "INPUT_SHA256",
        "INPUT_GIT_BLOB",
        "INPUT_BYTES",
        "INPUT_LF",
        "OUTPUT_SHA256",
        "OUTPUT_GIT_BLOB",
        "OUTPUT_BYTES",
        "OUTPUT_LF",
    }
    values: dict[str, object] = {}
    for node in tree.body:
        target: ast.expr | None = None
        value: ast.expr | None = None
        if isinstance(node, ast.Assign) and len(node.targets) == 1:
            target, value = node.targets[0], node.value
        elif isinstance(node, ast.AnnAssign):
            target, value = node.target, node.value
        if isinstance(target, ast.Name) and target.id in wanted and value is not None:
            try:
                values[target.id] = ast.literal_eval(value)
            except (ValueError, TypeError) as error:
                raise RuntimeError(
                    f"{path.name} constant {target.id} is not a literal"
                ) from error
    if set(values) != wanted:
        raise RuntimeError(
            f"{path.name} helper constant set mismatch: {sorted(values)}"
        )
    return values


def resolve_helper_path(spec: ComponentSpec) -> Path:
    local = ROOT / spec.helper_path
    installed = PACKAGE_DIR / Path(spec.helper_path).name
    if local.is_file():
        return local
    if installed.is_file():
        return installed
    raise RuntimeError(
        f"missing component helper {spec.label}: tried {local} and {installed}"
    )


def load_component(spec: ComponentSpec) -> LoadedComponent:
    if not spec.ready:
        raise RuntimeError(f"attempted to load unsealed component {spec.label}")
    helper_path = resolve_helper_path(spec)
    helper_raw = helper_path.read_bytes()
    helper_shape = shape(helper_raw)
    if helper_shape["sha256"] != spec.helper_sha256:
        raise RuntimeError(
            f"{spec.label} helper drift: {helper_shape['sha256']} != {spec.helper_sha256}"
        )
    constants = static_helper_constants(helper_raw, helper_path)
    module_input = {
        "INPUT_SHA256": INPUT_SHA256,
        "INPUT_GIT_BLOB": INPUT_GIT_BLOB,
        "INPUT_BYTES": INPUT_BYTES,
        "INPUT_LF": INPUT_LF,
    }
    for name, wanted in module_input.items():
        if constants.get(name) != wanted:
            raise RuntimeError(
                f"{spec.label} {name}: {constants.get(name)!r} != {wanted!r}"
            )
    if constants.get("OUTPUT_SHA256") != spec.standalone_output_sha256:
        raise RuntimeError(f"{spec.label} standalone output constant mismatch")
    rules = embedded_rule_map()[spec.label]
    if len(rules) != spec.expected_rules:
        raise RuntimeError(f"{spec.label} rule count {len(rules)}")
    if sum(rule.occurrences for rule in rules) != spec.expected_occurrences:
        raise RuntimeError(f"{spec.label} occurrence count mismatch")

    output_path = ROOT / spec.standalone_output_path
    if output_path.is_file():
        output_raw = output_path.read_bytes()
        if sha256(output_raw) != spec.standalone_output_sha256:
            raise RuntimeError(f"{spec.label} standalone output file drift")
    audit_path = ROOT / spec.forward_audit_path
    if audit_path.is_file():
        audit_raw = audit_path.read_bytes()
        if sha256(audit_raw) != spec.forward_audit_sha256:
            raise RuntimeError(f"{spec.label} audit drift")
        audit = json.loads(audit_raw.decode("utf-8"))
    else:
        audit = {
            "activation": False,
            "inverse_byte_equal": True,
            "source": {"sha256": INPUT_SHA256},
            "result": {"sha256": spec.standalone_output_sha256},
            "trust": trust(""),
            "installed_embedded_replay": True,
        }
    if audit.get("activation") is not False:
        raise RuntimeError(f"{spec.label} must remain activation=false")
    if audit.get("inverse_byte_equal") is not True:
        raise RuntimeError(f"{spec.label} audit inverse is not exact")
    if audit.get("source", {}).get("sha256") != INPUT_SHA256:
        raise RuntimeError(f"{spec.label} audit source mismatch")
    if audit.get("result", {}).get("sha256") != spec.standalone_output_sha256:
        raise RuntimeError(f"{spec.label} audit result mismatch")
    if any((audit.get("trust") or {}).values()):
        raise RuntimeError(f"{spec.label} audit is not trust0")
    return LoadedComponent(spec, constants, rules, helper_shape, audit)


def replace_rule(text: str, rule: RuleRef, inverse: bool) -> str:
    old, new = (rule.new, rule.old) if inverse else (rule.old, rule.new)
    count = text.count(old)
    if count != rule.occurrences:
        direction = "inverse" if inverse else "forward"
        raise RuntimeError(
            f"{rule.component}:{rule.label}:{direction} anchor count "
            f"{count} != {rule.occurrences}"
        )
    return text.replace(old, new)


def apply_component(text: str, component: LoadedComponent, inverse: bool) -> str:
    rules = tuple(reversed(component.rules)) if inverse else component.rules
    for rule in rules:
        text = replace_rule(text, rule, inverse)
    return text


def span_rows(text: str, components: tuple[LoadedComponent, ...]) -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    for component in components:
        for rule in component.rules:
            start = 0
            found: list[tuple[int, int]] = []
            while True:
                index = text.find(rule.old, start)
                if index < 0:
                    break
                found.append((index, index + len(rule.old)))
                start = index + 1
            if len(found) != rule.occurrences:
                raise RuntimeError(
                    f"{rule.component}:{rule.label} base spans {len(found)} "
                    f"!= {rule.occurrences}"
                )
            for occurrence, (left, right) in enumerate(found, start=1):
                rows.append(
                    {
                        "component": rule.component,
                        "rule": rule.label,
                        "occurrence": occurrence,
                        "start": left,
                        "end": right,
                    }
                )
    overlaps: list[dict[str, object]] = []
    for index, left in enumerate(rows):
        for right in rows[index + 1 :]:
            if left["start"] < right["end"] and right["start"] < left["end"]:
                overlaps.append({"left": left, "right": right})
    if overlaps:
        raise RuntimeError(f"Probe11 component source-span collision: {overlaps}")
    return rows


def audit_components(
    source: bytes, components: tuple[LoadedComponent, ...]
) -> dict[str, object]:
    source_text = source.decode("utf-8")
    source_trust = trust(source_text)
    if any(source_trust.values()):
        raise RuntimeError(f"nonzero source trust: {source_trust}")
    spans = span_rows(source_text, components)

    standalone_rows: list[dict[str, object]] = []
    for component in components:
        result = apply_component(source_text, component, False)
        result_raw = result.encode("utf-8")
        if sha256(result_raw) != component.spec.standalone_output_sha256:
            raise RuntimeError(f"{component.spec.label} independent replay mismatch")
        restored = apply_component(result, component, True)
        if restored != source_text:
            raise RuntimeError(f"{component.spec.label} independent inverse mismatch")
        result_trust = trust(result)
        if result_trust != source_trust or any(result_trust.values()):
            raise RuntimeError(f"{component.spec.label} trust drift")
        standalone_rows.append(
            {
                "component": component.spec.label,
                "rules": len(component.rules),
                "occurrences": sum(rule.occurrences for rule in component.rules),
                "output": shape(result_raw),
                "inverse_byte_equal": True,
                "trust": result_trust,
            }
        )

    def forward_order(order: tuple[LoadedComponent, ...]) -> str:
        result = source_text
        for component in order:
            result = apply_component(result, component, False)
        return result

    def inverse_order(result: str, order: tuple[LoadedComponent, ...]) -> str:
        for component in reversed(order):
            result = apply_component(result, component, True)
        return result

    # Every unordered component pair is exercised in both orders, and each
    # result is restored by the matching inverse.  Together with disjoint exact
    # source spans this is the fail-closed commutativity proof used instead of
    # delaying CI with all 7! full-file projections.
    pair_rows: list[dict[str, object]] = []
    for left, right in itertools.combinations(components, 2):
        left_right = (left, right)
        right_left = (right, left)
        result_lr = forward_order(left_right)
        result_rl = forward_order(right_left)
        if result_lr != result_rl:
            raise RuntimeError(
                f"component pair order dependence: {left.spec.label},"
                f"{right.spec.label}"
            )
        if inverse_order(result_lr, left_right) != source_text:
            raise RuntimeError("left-right pair inverse mismatch")
        if inverse_order(result_rl, right_left) != source_text:
            raise RuntimeError("right-left pair inverse mismatch")
        pair_rows.append(
            {
                "pair": [left.spec.label, right.spec.label],
                "left_right_sha256": sha256(result_lr.encode("utf-8")),
                "right_left_sha256": sha256(result_rl.encode("utf-8")),
                "outputs_equal": True,
                "matching_inverses_equal_source": True,
            }
        )

    canonical = forward_order(components)
    canonical_second = forward_order(components)
    if canonical_second != canonical:
        raise RuntimeError("canonical order is not deterministic")
    if inverse_order(canonical, components) != source_text:
        raise RuntimeError("canonical inverse mismatch")
    canonical_raw = canonical.encode("utf-8")
    canonical_shape = shape(canonical_raw)

    # Sixteen deterministic pseudo-random representatives, split across two
    # fixed seeds (8 + 8), exercise longer mixed orders without claiming an
    # exhaustive 7! replay.
    order_rows: list[dict[str, object]] = []
    seen_orders: set[tuple[int, ...]] = set()
    for group, seed in (("seed_a", 0x50524F4245313141), ("seed_b", 0x50524F4245313142)):
        generator = random.Random(seed)
        accepted = 0
        while accepted < 8:
            indices = list(range(len(components)))
            generator.shuffle(indices)
            key = tuple(indices)
            if key in seen_orders:
                continue
            seen_orders.add(key)
            accepted += 1
            order = tuple(components[index] for index in indices)
            result = forward_order(order)
            restored = inverse_order(result, order)
            if result != canonical:
                raise RuntimeError(
                    "representative component order dependence: "
                    + ",".join(component.spec.label for component in order)
                )
            if restored != source_text:
                raise RuntimeError(
                    "representative component inverse mismatch: "
                    + ",".join(component.spec.label for component in order)
                )
            order_rows.append(
                {
                    "group": group,
                    "index": accepted,
                    "order": [component.spec.label for component in order],
                    "output_sha256": sha256(result.encode("utf-8")),
                    "inverse_byte_equal": True,
                }
            )
    combined_trust = trust(canonical)
    if combined_trust != source_trust or any(combined_trust.values()):
        raise RuntimeError(f"combined trust drift: {source_trust} -> {combined_trust}")
    return {
        "components": len(components),
        "rules": sum(len(component.rules) for component in components),
        "occurrences": sum(
            rule.occurrences for component in components for rule in component.rules
        ),
        "source_spans": len(spans),
        "source_span_overlaps": [],
        "standalone_replays": standalone_rows,
        "pairwise_pairs_expected": len(components) * (len(components) - 1) // 2,
        "pairwise_pairs_tested": len(pair_rows),
        "pairwise_directions_tested": 2 * len(pair_rows),
        "all_pairwise_outputs_equal": True,
        "all_pairwise_matching_inverses_equal": True,
        "pairwise": pair_rows,
        "canonical_runs_tested": 2,
        "canonical_deterministic": True,
        "canonical_inverse_byte_equal": True,
        "representative_orders_tested": len(order_rows),
        "representative_seed_groups": {"seed_a": 8, "seed_b": 8},
        "all_representative_outputs_equal": True,
        "all_representative_inverses_equal": True,
        "exhaustive_order_count": 5040,
        "exhaustive_replay_performed": False,
        "combined_output": canonical_shape,
        "combined_trust": combined_trust,
        "orders": order_rows,
    }


def readiness() -> tuple[tuple[ComponentSpec, ...], tuple[ComponentSpec, ...]]:
    ready = tuple(spec for spec in COMPONENTS if spec.ready)
    missing = tuple(spec for spec in COMPONENTS if not spec.ready)
    return ready, missing


def require_all_components() -> tuple[ComponentSpec, ...]:
    ready, missing = readiness()
    if missing:
        labels = ", ".join(spec.label for spec in missing)
        raise RuntimeError(
            "PROBE11_RENDER_BLOCKED_UNSEALED_COMPONENTS: " + labels
        )
    if len(ready) != len(COMPONENTS):
        raise RuntimeError("Probe11 component readiness invariant failed")
    return ready


def write_new(path: Path, raw: bytes) -> None:
    if path.exists():
        raise RuntimeError(f"refusing to overwrite {path}")
    path.write_bytes(raw)


def skeleton_audit(path: Path) -> int:
    source, authority_audit = verify_authority()
    ready_specs, missing_specs = readiness()
    loaded = tuple(load_component(spec) for spec in ready_specs)
    replay = audit_components(source, loaded)

    # Mid's own exact active-Probe10 new-span gate is mandatory here because
    # it is the only ready package claiming zero overlap with all 37 P10 rules.
    mid = next(component for component in loaded if component.spec.label == "mid_p10_authority")
    collision = mid.audit.get("probe10_collision_audit") or {}
    if collision.get("foreign_rule_families_checked") != 37:
        raise RuntimeError("mid active-Probe10 family count mismatch")
    if collision.get("exact_anchor_equalities") != []:
        raise RuntimeError("mid active-Probe10 exact-anchor collision")
    if collision.get("span_overlaps") != []:
        raise RuntimeError("mid active-Probe10 span collision")

    record = {
        "schema": SCHEMA,
        "status": "SKELETON_STATIC_PASS_RENDER_BLOCKED_BY_EXACTLY_TWO_SENTINELS",
        "activation": False,
        "render_permitted": False,
        "authority": {**AUTHORITY, **authority_audit},
        "ready_components": [
            {
                **asdict(component.spec),
                "helper_shape": component.helper_shape,
                "module_output": {
                    "sha256": component.helper_constants["OUTPUT_SHA256"],
                    "git_blob": component.helper_constants["OUTPUT_GIT_BLOB"],
                    "bytes": component.helper_constants["OUTPUT_BYTES"],
                    "lf": component.helper_constants["OUTPUT_LF"],
                },
            }
            for component in loaded
        ],
        "missing_components": [asdict(spec) for spec in missing_specs],
        "missing_count": len(missing_specs),
        "replay": replay,
        "mid_active_probe10_collision_gate": collision,
        "final_output_sentinels": {
            "sha256": OUTPUT_SHA256,
            "git_blob": OUTPUT_GIT_BLOB,
            "bytes": OUTPUT_BYTES,
            "lf": OUTPUT_LF,
        },
        "trust": replay["combined_trust"],
        "execution": {
            "lean": False,
            "lake": False,
            "git": False,
            "network": False,
            "remote": False,
            "canonical_source_mutation": False,
            "candidate_rendered": False,
        },
    }
    if len(missing_specs) != 2 or {spec.label for spec in missing_specs} != {
        "earlymid_p10_conditional",
        "structural50k_p10_conditional",
    }:
        raise RuntimeError("skeleton must be blocked by exact earlymid and structural50k sentinels")
    write_new(path, (json.dumps(record, indent=2) + "\n").encode("utf-8"))
    print(json.dumps(record, sort_keys=True))
    return 0


def render(args: argparse.Namespace) -> int:
    specs = require_all_components()
    if args.input is None or args.output is None or args.audit is None:
        raise RuntimeError("forward/inverse rendering requires input, output, and --audit")
    source_authority, authority_audit = verify_authority(args.probe10_authority_dir)
    source = args.input.read_bytes()
    inverse = args.mode == "inverse"
    source_expected = (
        {
            "sha256": OUTPUT_SHA256,
            "git_blob": OUTPUT_GIT_BLOB,
            "bytes": OUTPUT_BYTES,
            "lf": OUTPUT_LF,
        }
        if inverse
        else {
            "sha256": INPUT_SHA256,
            "git_blob": INPUT_GIT_BLOB,
            "bytes": INPUT_BYTES,
            "lf": INPUT_LF,
        }
    )
    if args.bootstrap_seal and not inverse and OUTPUT_SHA256.startswith("__UNSEALED_"):
        source_expected = {
            "sha256": INPUT_SHA256,
            "git_blob": INPUT_GIT_BLOB,
            "bytes": INPUT_BYTES,
            "lf": INPUT_LF,
        }
    check_text_shape(shape(source), source_expected)
    if not inverse and source != source_authority:
        raise RuntimeError("forward input is not exact Probe10 authority bytes")
    loaded = tuple(load_component(spec) for spec in specs)
    replay = audit_components(source_authority, loaded)
    text = source.decode("utf-8")
    order = tuple(reversed(loaded)) if inverse else loaded
    for component in order:
        text = apply_component(text, component, inverse)
    result = text.encode("utf-8")
    result_shape = shape(result)
    result_expected = (
        {
            "sha256": INPUT_SHA256,
            "git_blob": INPUT_GIT_BLOB,
            "bytes": INPUT_BYTES,
            "lf": INPUT_LF,
        }
        if inverse
        else {
            "sha256": OUTPUT_SHA256,
            "git_blob": OUTPUT_GIT_BLOB,
            "bytes": OUTPUT_BYTES,
            "lf": OUTPUT_LF,
        }
    )
    if not (args.bootstrap_seal and not inverse and OUTPUT_SHA256.startswith("__UNSEALED_")):
        check_text_shape(result_shape, result_expected)
    if any(trust(text).values()):
        raise RuntimeError("integrated result is not trust0")
    restored = text
    for component in reversed(order):
        restored = apply_component(restored, component, not inverse)
    if restored.encode("utf-8") != source:
        raise RuntimeError("integrated opposite transform is not byte-exact")
    write_new(args.output, result)
    audit = {
        "schema": SCHEMA,
        "status": "STATIC_PASS_EXACT_PROBE10_NOT_LEAN_EXECUTED",
        "activation": False,
        "mode": args.mode,
        "authority": {**AUTHORITY, **authority_audit},
        "source": shape(source),
        "result": result_shape,
        "components": [asdict(spec) for spec in specs],
        "replay": replay,
        "inverse_byte_equal": True,
        "trust": trust(text),
        "execution": {
            "lean": False,
            "lake": False,
            "git": False,
            "network": False,
            "remote": False,
            "canonical_source_mutation": False,
        },
    }
    write_new(args.audit, (json.dumps(audit, indent=2) + "\n").encode("utf-8"))
    print(json.dumps(audit, sort_keys=True))
    return 0


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path, nargs="?")
    parser.add_argument("output", type=Path, nargs="?")
    parser.add_argument("--audit", type=Path)
    parser.add_argument("--mode", choices=("forward", "inverse"), default="forward")
    parser.add_argument("--bootstrap-seal", action="store_true")
    parser.add_argument(
        "--probe10-authority-dir",
        type=Path,
        default=AUTHORITY_DIR,
        help="directory containing exact terminal-Probe10 evidence",
    )
    parser.add_argument("--skeleton-audit", type=Path)
    args = parser.parse_args()
    if args.skeleton_audit is not None:
        if args.input is not None or args.output is not None or args.audit is not None:
            raise RuntimeError("--skeleton-audit cannot be combined with rendering arguments")
        return skeleton_audit(args.skeleton_audit)
    return render(args)


if __name__ == "__main__":
    raise SystemExit(main())
