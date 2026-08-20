#!/usr/bin/env python3
"""Compose the sealed Probe6 repair components over exact Probe5 authority.

This helper is deliberately static.  It never invokes Lean, Lake, Git, or the
network.  The logical ``frontier`` component is dependency ordered internally
(core then pmap addon; addon then core on inverse).  The frontier composite,
the broad conditional component, and the late component are then checked in
all 3! forward orders and all matching reverse orders.  Every helper, authority
identity, standalone projection, exact inverse, and executable-trust counter is
fail-closed.

Promotion remains forbidden until the immutable terminal artifact from Probe5
run 31964319679 activates the selected repairs and a Probe6 workflow compiles
the exact integrated candidate successfully.
"""

from __future__ import annotations

import argparse
import difflib
import hashlib
import importlib.util
import itertools
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from types import ModuleType
from typing import Any


sys.dont_write_bytecode = True

SCHEMA = "qym-probe6-integrated-transform-v1"
REQUIRED_PROBE5_RUN = 31964319679
REQUIRED_PROBE5_ARTIFACT = 9268143089
REQUIRED_PROBE5_TRIGGER_SHA = "47fba66fc5c14a11b89bf6774d7350034f275fae"
REQUIRED_PROBE5_LOG_SHA256 = (
    "c9a9799987cb18047c580777841d5cd4f0e32c592d5ab72062d05b0b9022acae"
)
EXPECTED_INPUT_SHA256 = (
    "30edb320b25eadbfda284160016a5a23cc28a95d6228cbd061161d4ec615de7c"
)
EXPECTED_INPUT_GIT_BLOB = "9ea2ef7d03555cca4e82cbeeb01cba033dff6b99"
EXPECTED_INPUT_BYTES = 2_911_806
EXPECTED_INPUT_LF = 61_557

EXPECTED_PROBE4_SHA256 = (
    "fb9d451c88d55e71398f3e3a4b38b3cc9ff5e0a37273115579fc2351d1fdad9c"
)
EXPECTED_PROBE4_GIT_BLOB = "b08d7bb621d8acc8338f3afa3f12ac2ff2c7e6d1"
EXPECTED_PROBE4_BYTES = 2_910_229
EXPECTED_PROBE4_LF = 61_523

# Sealed only after the bootstrap projection passes every static proof below.
EXPECTED_OUTPUT_SHA256 = (
    "1941ed50883da7e1c6cc0fbdcab084f0184ab1b35d89e00a754cb60809723b34"
)
EXPECTED_OUTPUT_GIT_BLOB = "21919f9a27529afa93b12bb8e88d8952cb63e292"
EXPECTED_OUTPUT_BYTES = 2_912_719
EXPECTED_OUTPUT_LF = 61_571

FRONTIER_HELPER_SHA256 = (
    "bc8383e2ac0fb47634a1310bcb0fa0da2c1715cf28cbfcf47d34f281c586378f"
)
FRONTIER_ADDON_HELPER_SHA256 = (
    "7d6e37d214caf670b5a0ebd08e5587f08d4718f214618ab2a7bf4d0fd4226d4e"
)
CONDITIONAL_HELPER_SHA256 = (
    "31d080cba9e5bc943cdb85c2566d6cb3068dd901c0cb610c710c87cf20766517"
)
LATE_HELPER_SHA256 = (
    "a943f692e9b1047e85fba082a5dd2ebc5e900b3feda1502f9ef361b1182e86dc"
)

FRONTIER_STANDALONE_SHA256 = (
    "df5b72cf703cc246baf0eeb54e77a3676aff42f6b36370e76ca7904ea9c2d92f"
)
# The sealed conditional helper contains seven tail rules that overlap the
# stronger late helper.  The integrated logical component owns only its exact
# first 31 rules; this standalone identity is sealed after that fail-closed
# slice has been projected once.
CONDITIONAL_STANDALONE_SHA256 = (
    "71c1604dfec9a0b8480213a778f3015ded600dd32c30616b2cf1f9197c726544"
)
LATE_STANDALONE_SHA256 = (
    "38c4493bbc24c165ebed4daf2a02ea5eab63f43a2841e1a898caf687c6454290"
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
class LoadedHelpers:
    frontier: ModuleType
    frontier_addon: ModuleType
    conditional: ModuleType
    late: ModuleType
    paths: dict[str, Path]


@dataclass(frozen=True)
class LogicalComponent:
    name: str
    standalone_output_sha256: str


COMPONENTS: tuple[LogicalComponent, ...] = (
    LogicalComponent("frontier", FRONTIER_STANDALONE_SHA256),
    LogicalComponent("conditional", CONDITIONAL_STANDALONE_SHA256),
    LogicalComponent("late", LATE_STANDALONE_SHA256),
)

CONDITIONAL_OWNED_RULE_COUNT = 31
CONDITIONAL_EXCLUDED_TAIL_LABELS = (
    "idempotent_positive_field_projection_parenthesized",
    "physical_raise_closable_remove_obsolete_green_argument",
    "physical_lower_closable_remove_obsolete_green_argument",
    "physical_joint_closable_remove_obsolete_green_arguments",
    "closed_raise_remove_obsolete_green_argument",
    "closed_lower_remove_obsolete_green_argument",
    "closed_joint_remove_obsolete_green_arguments",
)


def sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def git_blob(raw: bytes) -> str:
    return hashlib.sha1(f"blob {len(raw)}\0".encode("ascii") + raw).hexdigest()


def shape(raw: bytes, label: str) -> dict[str, Any]:
    if raw.startswith(b"\xef\xbb\xbf"):
        raise RuntimeError(f"{label}: UTF-8 BOM forbidden")
    if b"\r" in raw:
        raise RuntimeError(f"{label}: CR forbidden")
    if b"\0" in raw:
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


def exact_tuple(info: dict[str, Any]) -> tuple[str, str, int, int]:
    return (info["sha256"], info["git_blob"], info["bytes"], info["lf"])


def assert_exact(
    actual: dict[str, Any], expected: tuple[str, str, int, int], label: str
) -> None:
    if exact_tuple(actual) != expected:
        raise RuntimeError(f"{label}: {exact_tuple(actual)!r} != {expected!r}")


def trust_counts(text: str) -> dict[str, int]:
    return {name: len(pattern.findall(text)) for name, pattern in TRUST_PATTERNS.items()}


def load_module(name: str, path: Path, expected_sha256: str) -> ModuleType:
    raw = path.read_bytes()
    if sha256(raw) != expected_sha256:
        raise RuntimeError(
            f"{name}: helper SHA256 {sha256(raw)}, expected {expected_sha256}"
        )
    spec = importlib.util.spec_from_file_location(f"qym_probe6_{name}_sealed", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"{name}: cannot import {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def module_tuple(module: ModuleType, prefix: str) -> tuple[Any, Any, Any, Any]:
    return tuple(
        getattr(module, f"{prefix}_{suffix}", None)
        for suffix in ("SHA256", "GIT_BLOB", "BYTES", "LF")
    )


def load_helpers(args: argparse.Namespace) -> LoadedHelpers:
    paths = {
        "frontier": args.frontier_transformer,
        "frontier_addon": args.frontier_addon_transformer,
        "conditional": args.conditional_transformer,
        "late": args.late_transformer,
    }
    frontier = load_module("frontier", paths["frontier"], FRONTIER_HELPER_SHA256)
    addon = load_module(
        "frontier_addon", paths["frontier_addon"], FRONTIER_ADDON_HELPER_SHA256
    )
    conditional = load_module(
        "conditional", paths["conditional"], CONDITIONAL_HELPER_SHA256
    )
    late = load_module("late", paths["late"], LATE_HELPER_SHA256)

    expected_input = (
        EXPECTED_INPUT_SHA256,
        EXPECTED_INPUT_GIT_BLOB,
        EXPECTED_INPUT_BYTES,
        EXPECTED_INPUT_LF,
    )
    expected_probe4 = (
        EXPECTED_PROBE4_SHA256,
        EXPECTED_PROBE4_GIT_BLOB,
        EXPECTED_PROBE4_BYTES,
        EXPECTED_PROBE4_LF,
    )
    if module_tuple(frontier, "INPUT") != expected_input:
        raise RuntimeError("frontier Probe5 input constants mismatch")
    if module_tuple(conditional, "EXPECTED_INPUT") != expected_input:
        raise RuntimeError("conditional Probe5 input constants mismatch")
    if module_tuple(late, "EXPECTED_PROBE5_INPUT") != expected_input:
        raise RuntimeError("late Probe5 input constants mismatch")
    if module_tuple(late, "EXPECTED_PROBE4") != expected_probe4:
        raise RuntimeError("late Probe4 authority constants mismatch")

    frontier_output = module_tuple(frontier, "OUTPUT")
    if module_tuple(addon, "INPUT") != frontier_output:
        raise RuntimeError("frontier addon is not locked to frontier core output")
    if getattr(addon, "OUTPUT_SHA256", None) != FRONTIER_STANDALONE_SHA256:
        raise RuntimeError("frontier addon output identity mismatch")
    if getattr(conditional, "EXPECTED_OUTPUT_SHA256", None) != (
        "1d66e3a0cdc3446babe651d64dcc99e0b0f55ff282f0908d048b360dfd6f37df"
    ):
        raise RuntimeError("sealed full conditional helper output identity mismatch")
    conditional_rules = tuple(getattr(conditional, "RULES", ()))
    if len(conditional_rules) != 38:
        raise RuntimeError("conditional helper rule count is not exactly 38")
    excluded_labels = tuple(
        rule.label for rule in conditional_rules[CONDITIONAL_OWNED_RULE_COUNT:]
    )
    if excluded_labels != CONDITIONAL_EXCLUDED_TAIL_LABELS:
        raise RuntimeError(
            f"conditional excluded tail changed: {excluded_labels!r}"
        )
    if getattr(late, "EXPECTED_OUTPUT_SHA256", None) != LATE_STANDALONE_SHA256:
        raise RuntimeError("late standalone identity mismatch")
    for label, module in (("frontier", frontier), ("conditional", conditional), ("late", late)):
        if not callable(getattr(module, "transform", None)):
            raise RuntimeError(f"{label}: transform API missing")
    if not isinstance(getattr(addon, "OLD", None), str) or not isinstance(
        getattr(addon, "NEW", None), str
    ):
        raise RuntimeError("frontier addon exact block constants missing")
    return LoadedHelpers(frontier, addon, conditional, late, paths)


def occurrence_total(value: Any) -> int:
    if isinstance(value, dict):
        if isinstance(value.get("occurrences"), int):
            return value["occurrences"]
        return sum(occurrence_total(item) for item in value.values())
    if isinstance(value, list):
        return sum(occurrence_total(item) for item in value)
    return 0


def apply_addon(module: ModuleType, text: str, *, inverse: bool) -> tuple[str, Any]:
    source = module.NEW if inverse else module.OLD
    target = module.OLD if inverse else module.NEW
    count = text.count(source)
    if count != 1:
        raise RuntimeError(
            f"frontier addon: expected one {'inverse' if inverse else 'forward'} anchor, "
            f"found {count}"
        )
    result = text.replace(source, target)
    return result, {
        "label": "bind_domain_eigen_equation_pmap_addon",
        "direction": "inverse" if inverse else "forward",
        "occurrences": count,
        "probe5_error_lines": [24559],
    }


def apply_conditional_disjoint(
    module: ModuleType, text: str, *, inverse: bool
) -> tuple[str, Any]:
    """Apply the exact non-overlapping prefix of the sealed 38-rule helper.

    Late owns the exact seven-rule tail.  Six tail outputs are byte-identical
    to late's Green-argument removals; the remaining idempotent repair is
    deliberately superseded by late's explicit ``ContinuousLinearMap`` API.
    """

    all_rules = tuple(module.RULES)
    excluded_labels = tuple(
        rule.label for rule in all_rules[CONDITIONAL_OWNED_RULE_COUNT:]
    )
    if len(all_rules) != 38 or excluded_labels != CONDITIONAL_EXCLUDED_TAIL_LABELS:
        raise RuntimeError("conditional overlap ownership contract changed")
    owned = all_rules[:CONDITIONAL_OWNED_RULE_COUNT]
    ordered = tuple(reversed(owned)) if inverse else owned
    details: list[dict[str, Any]] = []
    for rule in ordered:
        source = rule.new if inverse else rule.old
        target = rule.old if inverse else rule.new
        count = text.count(source)
        if count != rule.occurrences:
            raise RuntimeError(
                f"{rule.label}: expected {rule.occurrences} active occurrence(s), "
                f"found {count}"
            )
        opposite = text.count(target)
        embedded_opposite = source.count(target) * count
        if opposite != embedded_opposite:
            raise RuntimeError(
                f"{rule.label}: unexpected opposite-form count {opposite}; "
                f"only {embedded_opposite} embedded occurrence(s) are allowed"
            )
        text = text.replace(source, target)
        details.append(
            {
                "label": rule.label,
                "direction": "inverse" if inverse else "forward",
                "occurrences": count,
                "probe4_error_lines": list(rule.probe4_error_lines),
                "probe5_anchor_lines": list(rule.probe5_anchor_lines),
                "class": rule.class_name,
            }
        )
    return text, {
        "owned_rule_count": CONDITIONAL_OWNED_RULE_COUNT,
        "excluded_tail_labels": list(CONDITIONAL_EXCLUDED_TAIL_LABELS),
        "overlap_resolution": {
            "owner": "late",
            "identical_green_argument_outputs": 6,
            "stronger_explicit_idempotent_api": 1,
        },
        "rules": details,
    }


def apply_component(
    component: LogicalComponent,
    text: str,
    *,
    inverse: bool,
    helpers: LoadedHelpers,
    probe4_text: str,
) -> tuple[str, Any]:
    if component.name == "frontier":
        if inverse:
            after_addon, addon_detail = apply_addon(
                helpers.frontier_addon, text, inverse=True
            )
            result, core_detail = helpers.frontier.transform(after_addon, inverse=True)
            return result, {
                "dependency_order": ["pmap_addon", "frontier_core"],
                "pmap_addon": addon_detail,
                "frontier_core": core_detail,
            }
        after_core, core_detail = helpers.frontier.transform(text, inverse=False)
        result, addon_detail = apply_addon(
            helpers.frontier_addon, after_core, inverse=False
        )
        return result, {
            "dependency_order": ["frontier_core", "pmap_addon"],
            "frontier_core": core_detail,
            "pmap_addon": addon_detail,
        }
    if component.name == "conditional":
        return apply_conditional_disjoint(
            helpers.conditional, text, inverse=inverse
        )
    if component.name == "late":
        return helpers.late.transform(
            text, inverse=inverse, probe4_text=probe4_text
        )
    raise RuntimeError(f"unknown component {component.name}")


def compose_and_prove(
    source_text: str, helpers: LoadedHelpers, probe4_text: str
) -> tuple[str, dict[str, Any]]:
    standalone: dict[str, Any] = {}
    for component in COMPONENTS:
        forward, detail = apply_component(
            component,
            source_text,
            inverse=False,
            helpers=helpers,
            probe4_text=probe4_text,
        )
        forward_raw = forward.encode("utf-8")
        if (
            not component.standalone_output_sha256.startswith("__")
            and sha256(forward_raw) != component.standalone_output_sha256
        ):
            raise RuntimeError(f"{component.name}: standalone output SHA mismatch")
        restored, inverse_detail = apply_component(
            component,
            forward,
            inverse=True,
            helpers=helpers,
            probe4_text=probe4_text,
        )
        if restored != source_text:
            raise RuntimeError(f"{component.name}: standalone inverse is not exact")
        standalone[component.name] = {
            "standalone_output": shape(forward_raw, f"{component.name} standalone"),
            "active_occurrences": occurrence_total(detail),
            "forward_detail": detail,
            "inverse_active_occurrences": occurrence_total(inverse_detail),
            "inverse_byte_equal": True,
        }

    common_output: str | None = None
    rows: list[dict[str, Any]] = []
    for order in itertools.permutations(COMPONENTS):
        current = source_text
        details: list[dict[str, Any]] = []
        for component in order:
            current, detail = apply_component(
                component,
                current,
                inverse=False,
                helpers=helpers,
                probe4_text=probe4_text,
            )
            details.append(
                {
                    "component": component.name,
                    "active_occurrences": occurrence_total(detail),
                }
            )
        if common_output is None:
            common_output = current
        elif current != common_output:
            raise RuntimeError(
                "component collision: forward permutations produce different bytes"
            )
        restored = current
        for component in reversed(order):
            restored, _ = apply_component(
                component,
                restored,
                inverse=True,
                helpers=helpers,
                probe4_text=probe4_text,
            )
        if restored != source_text:
            raise RuntimeError(
                f"inverse failed for order {[item.name for item in order]}"
            )
        rows.append(
            {
                "forward_order": [item.name for item in order],
                "inverse_order": [item.name for item in reversed(order)],
                "output_sha256": sha256(current.encode("utf-8")),
                "inverse_byte_equal": True,
                "details": details,
            }
        )
    if common_output is None:
        raise RuntimeError("no Probe6 components configured")
    return common_output, {
        "proof_strategy": "exhaustive_logical_component_permutations",
        "logical_components": [component.name for component in COMPONENTS],
        "frontier_internal_dependency": {
            "forward": ["frontier_core", "pmap_addon"],
            "inverse": ["pmap_addon", "frontier_core"],
        },
        "standalone": standalone,
        "permutations_checked": len(rows),
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
            fromfile="QYM.candidate-probe5-conditional.lean",
            tofile="QYM.candidate-probe6-integrated.lean",
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


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--mode", choices=("forward", "inverse"), default="forward")
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--audit", type=Path, required=True)
    parser.add_argument("--patch", type=Path, required=True)
    parser.add_argument("--probe4-authority", type=Path, required=True)
    parser.add_argument("--frontier-transformer", type=Path, required=True)
    parser.add_argument("--frontier-addon-transformer", type=Path, required=True)
    parser.add_argument("--conditional-transformer", type=Path, required=True)
    parser.add_argument("--late-transformer", type=Path, required=True)
    parser.add_argument("--bootstrap-unsealed", action="store_true", help=argparse.SUPPRESS)
    args = parser.parse_args()

    helpers = load_helpers(args)
    probe4_raw = args.probe4_authority.read_bytes()
    probe4_info = shape(probe4_raw, "Probe4 authority")
    expected_probe4 = (
        EXPECTED_PROBE4_SHA256,
        EXPECTED_PROBE4_GIT_BLOB,
        EXPECTED_PROBE4_BYTES,
        EXPECTED_PROBE4_LF,
    )
    assert_exact(probe4_info, expected_probe4, "Probe4 authority")
    probe4_text = probe4_raw.decode("utf-8")

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
        assert_exact(source_info, expected_input, "Probe5 input")
        authority_text = raw.decode("utf-8")
    else:
        if not sealed:
            raise RuntimeError("inverse mode forbidden while Probe6 seal is absent")
        assert_exact(source_info, expected_output, "Probe6 input")
        current = raw.decode("utf-8")
        for component in reversed(COMPONENTS):
            current, _ = apply_component(
                component,
                current,
                inverse=True,
                helpers=helpers,
                probe4_text=probe4_text,
            )
        authority_text = current
        assert_exact(
            shape(authority_text.encode("utf-8"), "restored Probe5"),
            expected_input,
            "restored Probe5",
        )

    integrated_text, proof = compose_and_prove(authority_text, helpers, probe4_text)
    integrated_raw = integrated_text.encode("utf-8")
    integrated_info = shape(integrated_raw, "integrated Probe6")
    if sealed:
        assert_exact(integrated_info, expected_output, "integrated Probe6")
    elif not args.bootstrap_unsealed:
        raise RuntimeError("Probe6 output seal is absent; bootstrap flag required")

    before_trust = trust_counts(authority_text)
    after_trust = trust_counts(integrated_text)
    if before_trust != after_trust:
        raise RuntimeError(f"trust inventory changed: {before_trust} -> {after_trust}")
    if any(before_trust.values()):
        raise RuntimeError(f"Probe5 trust inventory is not zero: {before_trust}")

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
            else "PASS_STATIC_ACTIVATION_REQUIRED_NOT_LEAN_EXECUTED"
        ),
        "mode": args.mode,
        "conditional": True,
        "promotion_authorized": False,
        "activation_gate": {
            "required_probe5_run": REQUIRED_PROBE5_RUN,
            "required_probe5_artifact": REQUIRED_PROBE5_ARTIFACT,
            "required_probe5_trigger_sha": REQUIRED_PROBE5_TRIGGER_SHA,
            "required_probe5_candidate_sha256": EXPECTED_INPUT_SHA256,
            "required_probe5_log_sha256": REQUIRED_PROBE5_LOG_SHA256,
            "terminal_artifact_checked": False,
            "surviving_diagnostics_checked": False,
            "automatic_promotion_forbidden": True,
        },
        "probe4_authority": probe4_info,
        "probe5_input": shape(authority_text.encode("utf-8"), "Probe5 authority"),
        "probe6_integrated_candidate": integrated_info,
        "result": result_info,
        "component_helpers": {
            name: {"path": path.as_posix(), "sha256": sha256(path.read_bytes())}
            for name, path in helpers.paths.items()
        },
        "component_proof": proof,
        "canonical_forward_order": [component.name for component in COMPONENTS],
        "canonical_inverse_order": [component.name for component in reversed(COMPONENTS)],
        "inverse_byte_equal": True,
        "trust_counts": after_trust,
        "trust_delta_zero": True,
        "diff": diff_stats(patch_text),
        "execution": {
            "lean": False,
            "lake": False,
            "remote": False,
            "repository_source_mutation": False,
        },
    }
    rendered = json.dumps(audit, ensure_ascii=False, indent=2, sort_keys=True) + "\n"
    args.output.write_bytes(result)
    args.audit.write_text(rendered, encoding="utf-8", newline="\n")
    args.patch.write_text(patch_text, encoding="utf-8", newline="\n")
    print(rendered, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
