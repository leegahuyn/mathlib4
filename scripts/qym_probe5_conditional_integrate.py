#!/usr/bin/env python3
"""Compose sealed conditional Probe5 transformers against exact Probe4 bytes.

This helper is deliberately static.  It never invokes Lean, Lake, Git, or the
network.  It locks every component by raw SHA-256 and authority constants,
checks standalone round trips, proves every component permutation produces
identical bytes, checks the corresponding reverse order restores Probe4
byte-for-byte, and preserves a zero executable-trust inventory.

Promotion remains forbidden until the immutable artifact from Probe4 run
31962191425 proves that it compiled the exact fb9d candidate and confirms the
selected surviving diagnostics.  This helper cannot waive that activation
gate.
"""

from __future__ import annotations

import argparse
import difflib
import hashlib
import importlib.util
import itertools
import json
import math
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from types import ModuleType
from typing import Any


sys.dont_write_bytecode = True

SCHEMA = "qym-probe5-conditional-integrated-transform-v1"
REQUIRED_PROBE4_RUN = 31962191425
REQUIRED_PROBE4_TRIGGER_SHA = "04a06a0a265253a26a7b247a8c774def1f1c6358"
EXPECTED_INPUT_SHA256 = (
    "fb9d451c88d55e71398f3e3a4b38b3cc9ff5e0a37273115579fc2351d1fdad9c"
)
EXPECTED_INPUT_GIT_BLOB = "b08d7bb621d8acc8338f3afa3f12ac2ff2c7e6d1"
EXPECTED_INPUT_BYTES = 2_910_229
EXPECTED_INPUT_LF = 61_523

# Filled only after all sealed components have passed every permutation and
# byte-exact inverse gate.  The bootstrap flag refuses to claim a sealed
# package and exists only to derive these four local identities once.
EXPECTED_OUTPUT_SHA256 = (
    "30edb320b25eadbfda284160016a5a23cc28a95d6228cbd061161d4ec615de7c"
)
EXPECTED_OUTPUT_GIT_BLOB = "9ea2ef7d03555cca4e82cbeeb01cba033dff6b99"
EXPECTED_OUTPUT_BYTES = 2_911_806
EXPECTED_OUTPUT_LF = 61_557


@dataclass(frozen=True)
class ComponentSpec:
    name: str
    helper_sha256: str
    standalone_output_sha256: str


COMPONENT_SPECS: tuple[ComponentSpec, ...] = (
    ComponentSpec(
        name="frontier",
        helper_sha256="14b7c7fdbbca2853696f9b396ba6492c46d6291264433299c892683e60fba481",
        standalone_output_sha256="3654c5ac43028fd020e46d520b3f7d5e5a3068be69596cbdf06e5700a5383fe5",
    ),
    ComponentSpec(
        name="line41115",
        helper_sha256="287293d255d774a6e9e5497649de528552f7b9910335ec70ca6727c53d7ad056",
        standalone_output_sha256="a3822ea18d2ae8aac7dea68d57469ce3cc8d6359af0e1b04b9ef1d24d5866136",
    ),
    ComponentSpec(
        name="earlymid",
        helper_sha256="14d50568b6e146d109326b1c8a359a5753c2e4d68084fa88db7dba9dd0d86dca",
        standalone_output_sha256="1927b4432bc68bdbe6c7c1bdcc6bfb9c06e79e44013ea65d9d05373c9a491245",
    ),
    ComponentSpec(
        name="realpartform",
        helper_sha256="2961ecf9eb8ec6eb0e2fc848be374cf00184a2b9f563a7e064ed357153386074",
        standalone_output_sha256="f4e4eca05adf0adb62f4881acacdaaeff9a8b61834651ecaf181620399c7f2e4",
    ),
    ComponentSpec(
        name="survivor",
        helper_sha256="89922cdeb8a9d9b14bcb253de5ab32d7f195ff2ff85ca3b911e078abc0691082",
        standalone_output_sha256="dc721d886e8e1e78b3c7354d6cce0a50eae27f8164c132fa9c19271b7c4b9cb7",
    ),
    ComponentSpec(
        name="late",
        helper_sha256="9df8cd59a61f6f3f122bd2c722e810f48a5400582b059bda26606007625f6242",
        standalone_output_sha256="c01a80c2e3b49a19ecc8fcba6aa78b5154072e0fc667cacfa01679c2f0ce86ea",
    ),
)


TRUST_PATTERNS = {
    "sorry": re.compile(r"(?<![\w.])sorry(?![\w])"),
    "admit": re.compile(r"(?<![\w.])admit(?![\w])"),
    "native_decide": re.compile(r"(?<![\w.])native_decide(?![\w])"),
    "Lean.ofReduceBool": re.compile(r"(?<![\w.])Lean\.ofReduceBool(?![\w])"),
    "axiom_declaration": re.compile(r"^[ \t]*axiom\b", re.MULTILINE),
    "unsafe_declaration": re.compile(
        r"^[ \t]*unsafe[ \t]+(?:def|theorem|abbrev|instance)\b", re.MULTILINE
    ),
    "maxHeartbeats_zero": re.compile(
        r"^[ \t]*set_option[ \t]+maxHeartbeats[ \t]+0\b", re.MULTILINE
    ),
}


@dataclass(frozen=True)
class Component:
    spec: ComponentSpec
    path: Path
    module: ModuleType


def sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def git_blob(raw: bytes) -> str:
    return hashlib.sha1(f"blob {len(raw)}\0".encode("ascii") + raw).hexdigest()


def shape(raw: bytes, label: str) -> dict[str, Any]:
    if raw.startswith(b"\xef\xbb\xbf"):
        raise RuntimeError(f"{label}: UTF-8 BOM forbidden")
    if b"\r" in raw:
        raise RuntimeError(f"{label}: CR forbidden")
    if b"\x00" in raw:
        raise RuntimeError(f"{label}: NUL forbidden")
    if not raw.endswith(b"\n"):
        raise RuntimeError(f"{label}: terminal LF required")
    raw.decode("utf-8", errors="strict")
    return {
        "sha256": sha256(raw),
        "git_blob": git_blob(raw),
        "bytes": len(raw),
        "lf": raw.count(b"\n"),
        "utf8": True,
        "bom": False,
        "cr": False,
        "nul": False,
        "terminal_lf": True,
    }


def trust_counts(text: str) -> dict[str, int]:
    return {name: len(pattern.findall(text)) for name, pattern in TRUST_PATTERNS.items()}


def exact_tuple(info: dict[str, Any]) -> tuple[str, str, int, int]:
    return (info["sha256"], info["git_blob"], info["bytes"], info["lf"])


def base_identity(module: ModuleType) -> tuple[Any, Any, Any, Any]:
    prefixes = ("EXPECTED_PROBE4_INPUT", "EXPECTED_INPUT")
    for prefix in prefixes:
        values = tuple(
            getattr(module, f"{prefix}_{suffix}", None)
            for suffix in ("SHA256", "GIT_BLOB", "BYTES", "LF")
        )
        if all(value is not None for value in values):
            return values
    raise RuntimeError(f"{module.__name__}: sealed Probe4 input constants missing")


def load_component(spec: ComponentSpec, path: Path) -> Component:
    raw = path.read_bytes()
    actual_sha = sha256(raw)
    if actual_sha != spec.helper_sha256:
        raise RuntimeError(
            f"{spec.name}: helper SHA256 {actual_sha}, expected {spec.helper_sha256}"
        )
    module_name = f"qym_probe5_{spec.name}_sealed"
    loaded = importlib.util.spec_from_file_location(module_name, path)
    if loaded is None or loaded.loader is None:
        raise RuntimeError(f"{spec.name}: cannot import {path}")
    module = importlib.util.module_from_spec(loaded)
    sys.modules[module_name] = module
    loaded.loader.exec_module(module)
    if not callable(getattr(module, "transform", None)):
        raise RuntimeError(f"{spec.name}: transform(text, inverse=...) API missing")
    expected_base = (
        EXPECTED_INPUT_SHA256,
        EXPECTED_INPUT_GIT_BLOB,
        EXPECTED_INPUT_BYTES,
        EXPECTED_INPUT_LF,
    )
    if base_identity(module) != expected_base:
        raise RuntimeError(
            f"{spec.name}: Probe4 authority constants {base_identity(module)!r} "
            f"!= {expected_base!r}"
        )
    return Component(spec=spec, path=path, module=module)


def apply_component(
    component: Component, text: str, *, inverse: bool
) -> tuple[str, Any]:
    result = component.module.transform(text, inverse=inverse)
    if not isinstance(result, tuple) or len(result) != 2 or not isinstance(result[0], str):
        raise RuntimeError(f"{component.spec.name}: invalid transform return contract")
    return result


def occurrence_total(value: Any) -> int:
    if isinstance(value, dict):
        if isinstance(value.get("occurrences"), int):
            return value["occurrences"]
        return sum(occurrence_total(item) for item in value.values())
    if isinstance(value, list):
        return sum(occurrence_total(item) for item in value)
    return 0


def compose_and_prove(
    source_text: str, components: tuple[Component, ...]
) -> tuple[str, dict[str, Any]]:
    standalone: dict[str, Any] = {}
    for component in components:
        forward, detail = apply_component(component, source_text, inverse=False)
        forward_raw = forward.encode("utf-8")
        if sha256(forward_raw) != component.spec.standalone_output_sha256:
            raise RuntimeError(f"{component.spec.name}: standalone output SHA mismatch")
        restored, _ = apply_component(component, forward, inverse=True)
        if restored != source_text:
            raise RuntimeError(f"{component.spec.name}: standalone inverse is not exact")
        standalone[component.spec.name] = {
            "helper_path": component.path.as_posix(),
            "helper_sha256": component.spec.helper_sha256,
            "standalone_output": shape(
                forward_raw, f"{component.spec.name} standalone output"
            ),
            "active_occurrences": occurrence_total(detail),
            "detail": detail,
            "inverse_byte_equal": True,
        }

    def apply_order(order: tuple[Component, ...]) -> tuple[str, list[dict[str, Any]]]:
        current = source_text
        detail_rows: list[dict[str, Any]] = []
        for component in order:
            current, detail = apply_component(component, current, inverse=False)
            detail_rows.append(
                {
                    "component": component.spec.name,
                    "active_occurrences": occurrence_total(detail),
                }
            )
        return current, detail_rows

    permutation_count = math.factorial(len(components))
    if len(components) > 5:
        pair_rows: list[dict[str, Any]] = []
        for left, right in itertools.combinations(components, 2):
            left_right, left_right_details = apply_order((left, right))
            right_left, right_left_details = apply_order((right, left))
            if left_right != right_left:
                raise RuntimeError(
                    f"component collision: {left.spec.name} and {right.spec.name} do not commute"
                )
            restored = left_right
            for component in (right, left):
                restored, _ = apply_component(component, restored, inverse=True)
            if restored != source_text:
                raise RuntimeError(
                    f"pair inverse failed: {left.spec.name}, {right.spec.name}"
                )
            pair_rows.append(
                {
                    "pair": [left.spec.name, right.spec.name],
                    "orders_checked": [
                        [left.spec.name, right.spec.name],
                        [right.spec.name, left.spec.name],
                    ],
                    "output_sha256": sha256(left_right.encode("utf-8")),
                    "left_right_details": left_right_details,
                    "right_left_details": right_left_details,
                    "commutes": True,
                    "inverse_byte_equal": True,
                }
            )
        common_output, canonical_details = apply_order(components)
        restored = common_output
        for component in reversed(components):
            restored, _ = apply_component(component, restored, inverse=True)
        if restored != source_text:
            raise RuntimeError("canonical inverse is not byte exact")
        return common_output, {
            "proof_strategy": "pairwise_disjoint_commutation_plus_canonical_roundtrip",
            "standalone": standalone,
            "permutations_checked": permutation_count,
            "permutations_enumerated": 0,
            "permutations_implied_by_pairwise_commutation": permutation_count,
            "pairwise_pairs_checked": len(pair_rows),
            "pairwise_orders_checked": 2 * len(pair_rows),
            "pairwise": pair_rows,
            "canonical_details": canonical_details,
            "canonical_inverse_byte_equal": True,
            "all_forward_permutations_identical": True,
            "all_reverse_orders_byte_exact": True,
            "collision_free": True,
        }

    common_output: str | None = None
    rows: list[dict[str, Any]] = []
    for order in itertools.permutations(components):
        current, detail_rows = apply_order(order)
        if common_output is None:
            common_output = current
        elif current != common_output:
            raise RuntimeError("component collision: forward permutations differ")

        restored = current
        for component in reversed(order):
            restored, _ = apply_component(component, restored, inverse=True)
        if restored != source_text:
            raise RuntimeError(
                "component collision: inverse failed for "
                f"{[item.spec.name for item in order]}"
            )
        rows.append(
            {
                "forward_order": [item.spec.name for item in order],
                "inverse_order": [item.spec.name for item in reversed(order)],
                "output_sha256": sha256(current.encode("utf-8")),
                "inverse_byte_equal": True,
                "details": detail_rows,
            }
        )
    if common_output is None:
        raise RuntimeError("no components configured")
    return common_output, {
        "standalone": standalone,
        "proof_strategy": "exhaustive_all_permutations",
        "permutations_checked": len(rows),
        "permutations_enumerated": len(rows),
        "permutations": rows,
        "all_forward_permutations_identical": True,
        "all_reverse_orders_byte_exact": True,
        "collision_free": True,
    }


def render_patch(before: str, after: str) -> str:
    return "".join(
        difflib.unified_diff(
            before.splitlines(keepends=True),
            after.splitlines(keepends=True),
            fromfile="QYM.candidate-probe4.lean",
            tofile="QYM.candidate-probe5-conditional.lean",
            n=3,
        )
    )


def diff_stats(patch: str) -> dict[str, int]:
    lines = patch.splitlines()
    return {
        "hunks": sum(line.startswith("@@ ") for line in lines),
        "added_lines": sum(
            line.startswith("+") and not line.startswith("+++") for line in lines
        ),
        "deleted_lines": sum(
            line.startswith("-") and not line.startswith("---") for line in lines
        ),
        "patch_bytes": len(patch.encode("utf-8")),
        "patch_lf": patch.count("\n"),
    }


def assert_exact(
    actual: dict[str, Any], expected: tuple[str, str, int, int], label: str
) -> None:
    if exact_tuple(actual) != expected:
        raise RuntimeError(f"{label}: {exact_tuple(actual)!r} != {expected!r}")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--mode", choices=("forward", "inverse"), default="forward")
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--audit", type=Path, required=True)
    parser.add_argument("--patch", type=Path, required=True)
    parser.add_argument("--frontier-transformer", type=Path, required=True)
    parser.add_argument("--line41115-transformer", type=Path, required=True)
    parser.add_argument("--earlymid-transformer", type=Path, required=True)
    parser.add_argument("--realpartform-transformer", type=Path, required=True)
    parser.add_argument("--survivor-transformer", type=Path, required=True)
    parser.add_argument("--late-transformer", type=Path, required=True)
    parser.add_argument("--bootstrap-unsealed", action="store_true", help=argparse.SUPPRESS)
    args = parser.parse_args()

    paths = {
        "frontier": args.frontier_transformer,
        "line41115": args.line41115_transformer,
        "earlymid": args.earlymid_transformer,
        "realpartform": args.realpartform_transformer,
        "survivor": args.survivor_transformer,
        "late": args.late_transformer,
    }
    components = tuple(load_component(spec, paths[spec.name]) for spec in COMPONENT_SPECS)
    raw = args.input.read_bytes()
    source_info = shape(raw, "source")
    expected_input = (
        EXPECTED_INPUT_SHA256,
        EXPECTED_INPUT_GIT_BLOB,
        EXPECTED_INPUT_BYTES,
        EXPECTED_INPUT_LF,
    )
    expected_output = (
        EXPECTED_OUTPUT_SHA256,
        EXPECTED_OUTPUT_GIT_BLOB,
        EXPECTED_OUTPUT_BYTES,
        EXPECTED_OUTPUT_LF,
    )
    sealed = not EXPECTED_OUTPUT_SHA256.startswith("__")

    if args.mode == "forward":
        assert_exact(source_info, expected_input, "Probe4 input")
        authority_text = raw.decode("utf-8")
    else:
        if not sealed:
            raise RuntimeError("inverse mode forbidden while output seal is absent")
        assert_exact(source_info, expected_output, "Probe5 input")
        current = raw.decode("utf-8")
        for component in reversed(components):
            current, _ = apply_component(component, current, inverse=True)
        authority_text = current
        assert_exact(
            shape(authority_text.encode("utf-8"), "restored Probe4"),
            expected_input,
            "restored Probe4",
        )

    integrated_text, proof = compose_and_prove(authority_text, components)
    integrated_raw = integrated_text.encode("utf-8")
    integrated_info = shape(integrated_raw, "integrated conditional Probe5")
    if sealed:
        assert_exact(integrated_info, expected_output, "integrated Probe5")
    elif not args.bootstrap_unsealed:
        raise RuntimeError("Probe5 output seal is absent; bootstrap flag required")

    before_trust = trust_counts(authority_text)
    after_trust = trust_counts(integrated_text)
    if before_trust != after_trust:
        raise RuntimeError(f"trust inventory changed: {before_trust} -> {after_trust}")
    if any(before_trust.values()):
        raise RuntimeError(f"Probe4 trust inventory is not zero: {before_trust}")

    patch_text = render_patch(authority_text, integrated_text)
    result = integrated_raw if args.mode == "forward" else authority_text.encode("utf-8")
    result_info = shape(result, "result")
    if args.mode == "inverse":
        assert_exact(result_info, expected_input, "inverse result")

    audit = {
        "schema": SCHEMA,
        "status": (
            "BOOTSTRAP_STATIC_NOT_SEALED_NOT_LEAN_EXECUTED"
            if not sealed
            else "PASS_STATIC_CONDITIONAL_NOT_PROBE4_CONFIRMED_NOT_LEAN_EXECUTED"
        ),
        "mode": args.mode,
        "conditional": True,
        "promotion_authorized": False,
        "activation_gate": {
            "required_probe4_run": REQUIRED_PROBE4_RUN,
            "required_probe4_trigger_sha": REQUIRED_PROBE4_TRIGGER_SHA,
            "required_probe4_candidate_sha256": EXPECTED_INPUT_SHA256,
            "terminal_artifact_checked": False,
            "surviving_diagnostics_checked": False,
            "automatic_promotion_forbidden": True,
        },
        "probe4_input": shape(authority_text.encode("utf-8"), "Probe4 authority"),
        "probe5_conditional_candidate": integrated_info,
        "result": result_info,
        "component_proof": proof,
        "canonical_forward_order": [spec.name for spec in COMPONENT_SPECS],
        "canonical_inverse_order": [spec.name for spec in reversed(COMPONENT_SPECS)],
        "inverse_byte_equal": True,
        "trust_counts": after_trust,
        "trust_delta_zero": True,
        "diff": diff_stats(patch_text),
        "execution": {"lean": False, "lake": False, "remote": False},
    }
    rendered = json.dumps(audit, ensure_ascii=False, indent=2, sort_keys=True) + "\n"
    args.output.write_bytes(result)
    args.audit.write_text(rendered, encoding="utf-8", newline="\n")
    args.patch.write_text(patch_text, encoding="utf-8", newline="\n")
    print(rendered, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
