#!/usr/bin/env python3
"""Compose the three exact Probe4 QYM transformers, with collision proof.

This helper is deliberately tied to the terminal Probe3 authority.  It loads
the sealed early, mid, and late helpers from explicit paths, verifies their
raw-byte identities and authority constants, checks each helper's standalone
round trip, and proves collision freedom by requiring all six forward
permutations to produce the same bytes and every corresponding reverse order
to restore the exact input.

It does not invoke Lean, Lake, Git, or the network.
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

SCHEMA = "qym-probe4-integrated-transform-v1"
AUTHORITY_HEAD = "f76313a011bf47054863883eeef29aa2310b689f"
AUTHORITY_LOG_SHA256 = (
    "501029e514ba6bc875527e1bc96fb9f571afda222e53e633078736dccaa71f56"
)
EXPECTED_INPUT_SHA256 = (
    "9e82073bdaf6339feb1ca09d70ab371947c6e07294ae01895a33c75f978bd780"
)
EXPECTED_INPUT_GIT_BLOB = "652a6b11899db967ec19c2f32ca7aa1ad2044c7a"
EXPECTED_INPUT_BYTES = 2_906_639
EXPECTED_INPUT_LF = 61_479

# Filled only after the three independently sealed transformers compose and
# all six permutation/round-trip gates pass.
EXPECTED_OUTPUT_SHA256 = (
    "fb9d451c88d55e71398f3e3a4b38b3cc9ff5e0a37273115579fc2351d1fdad9c"
)
EXPECTED_OUTPUT_GIT_BLOB = "b08d7bb621d8acc8338f3afa3f12ac2ff2c7e6d1"
EXPECTED_OUTPUT_BYTES = 2_910_229
EXPECTED_OUTPUT_LF = 61_523

EXPECTED_HELPER_SHA256 = {
    "early": "a7ee4a8ca00ef161ca38d9f48e4e2a876aee3bc6badcb8e075e0b1b4ccfe1ffb",
    "mid": "057e6be5ac748be10bcb1c6e7ee129c8232ceed87e5c2c22bf932c105cc08ed9",
    "late": "ec184eb92a1dbb5455519ca802452a64909c43f3600a42579e5c59ff028eb0f9",
}

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
    name: str
    path: Path
    raw_sha256: str
    module: ModuleType


def sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def git_blob(raw: bytes) -> str:
    return hashlib.sha1(
        f"blob {len(raw)}\0".encode("ascii") + raw
    ).hexdigest()


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


def require_exact(
    info: dict[str, Any], expected: tuple[str, str, int, int], label: str
) -> None:
    actual = (info["sha256"], info["git_blob"], info["bytes"], info["lf"])
    if actual != expected:
        raise RuntimeError(f"{label}: exact identity mismatch: {actual!r} != {expected!r}")


def load_component(name: str, path: Path) -> Component:
    raw = path.read_bytes()
    actual_sha = sha256(raw)
    expected_sha = EXPECTED_HELPER_SHA256[name]
    if expected_sha.startswith("__"):
        raise RuntimeError(f"{name}: unsealed helper SHA placeholder")
    if actual_sha != expected_sha:
        raise RuntimeError(
            f"{name}: helper SHA256 {actual_sha}, expected {expected_sha}"
        )
    spec = importlib.util.spec_from_file_location(f"qym_probe4_{name}_sealed", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"{name}: cannot create import spec for {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    if not callable(getattr(module, "transform", None)):
        raise RuntimeError(f"{name}: required transform(text, inverse=...) API missing")
    if getattr(module, "EXPECTED_INPUT_SHA256", None) != EXPECTED_INPUT_SHA256:
        raise RuntimeError(f"{name}: authority candidate constant mismatch")
    log_constant = getattr(
        module, "AUTHORITY_LOG_SHA256", getattr(module, "EXPECTED_LOG_SHA256", None)
    )
    if log_constant != AUTHORITY_LOG_SHA256:
        raise RuntimeError(f"{name}: authority log constant mismatch")
    output_constant = getattr(module, "EXPECTED_OUTPUT_SHA256", None)
    if not isinstance(output_constant, str) or len(output_constant) != 64:
        raise RuntimeError(f"{name}: sealed standalone output constant missing")
    return Component(name=name, path=path, raw_sha256=actual_sha, module=module)


def apply_component(
    component: Component, text: str, *, inverse: bool
) -> tuple[str, Any]:
    result = component.module.transform(text, inverse=inverse)
    if not isinstance(result, tuple) or len(result) != 2 or not isinstance(result[0], str):
        raise RuntimeError(f"{component.name}: invalid transform return contract")
    return result


def occurrence_total(value: Any) -> int:
    if isinstance(value, dict):
        if set(value) >= {"occurrences"} and isinstance(value["occurrences"], int):
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
        expected = getattr(component.module, "EXPECTED_OUTPUT_SHA256")
        if sha256(forward_raw) != expected:
            raise RuntimeError(f"{component.name}: standalone output SHA mismatch")
        restored, _ = apply_component(component, forward, inverse=True)
        if restored != source_text:
            raise RuntimeError(f"{component.name}: standalone inverse is not byte exact")
        standalone[component.name] = {
            "helper_path": component.path.as_posix(),
            "helper_sha256": component.raw_sha256,
            "output": shape(forward_raw, f"{component.name} standalone output"),
            "active_occurrences": occurrence_total(detail),
            "detail": detail,
            "inverse_byte_equal": True,
        }

    permutation_rows: list[dict[str, Any]] = []
    common_output: str | None = None
    for order in itertools.permutations(components):
        current = source_text
        forward_details: list[dict[str, Any]] = []
        for component in order:
            current, detail = apply_component(component, current, inverse=False)
            forward_details.append(
                {
                    "component": component.name,
                    "active_occurrences": occurrence_total(detail),
                }
            )
        if common_output is None:
            common_output = current
        elif current != common_output:
            raise RuntimeError(
                "component collision: forward permutations do not produce identical bytes"
            )
        restored = current
        for component in reversed(order):
            restored, _ = apply_component(component, restored, inverse=True)
        if restored != source_text:
            raise RuntimeError(
                f"component collision: inverse failed for order {[c.name for c in order]}"
            )
        permutation_rows.append(
            {
                "forward_order": [component.name for component in order],
                "inverse_order": [component.name for component in reversed(order)],
                "output_sha256": sha256(current.encode("utf-8")),
                "inverse_byte_equal": True,
                "details": forward_details,
            }
        )
    if common_output is None:
        raise RuntimeError("no components supplied")
    return common_output, {
        "standalone": standalone,
        "permutations_checked": len(permutation_rows),
        "permutations": permutation_rows,
        "collision_free": True,
    }


def render_patch(before: str, after: str) -> str:
    return "".join(
        difflib.unified_diff(
            before.splitlines(keepends=True),
            after.splitlines(keepends=True),
            fromfile="QYM.candidate-probe3.lean",
            tofile="QYM.candidate-probe4.lean",
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
    parser.add_argument("--early-transformer", type=Path, required=True)
    parser.add_argument("--mid-transformer", type=Path, required=True)
    parser.add_argument("--late-transformer", type=Path, required=True)
    args = parser.parse_args()

    components = tuple(
        load_component(name, path)
        for name, path in (
            ("early", args.early_transformer),
            ("mid", args.mid_transformer),
            ("late", args.late_transformer),
        )
    )
    source = args.input.read_bytes()
    source_info = shape(source, "source")

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
    if EXPECTED_OUTPUT_SHA256.startswith("__"):
        raise RuntimeError("integrated output seal placeholder is still active")

    if args.mode == "forward":
        require_exact(source_info, expected_input, "Probe3 input")
        authority_text = source.decode("utf-8")
    else:
        require_exact(source_info, expected_output, "Probe4 input")
        current = source.decode("utf-8")
        for component in reversed(components):
            current, _ = apply_component(component, current, inverse=True)
        authority_text = current
        authority_info = shape(authority_text.encode("utf-8"), "restored authority")
        require_exact(authority_info, expected_input, "restored Probe3 authority")

    integrated_text, proof = compose_and_prove(authority_text, components)
    integrated = integrated_text.encode("utf-8")
    integrated_info = shape(integrated, "integrated Probe4 output")
    require_exact(integrated_info, expected_output, "integrated Probe4 output")

    before_trust = trust_counts(authority_text)
    after_trust = trust_counts(integrated_text)
    if before_trust != after_trust:
        raise RuntimeError(f"trust-marker inventory changed: {before_trust} -> {after_trust}")
    if any(before_trust.values()):
        raise RuntimeError(f"authority trust-marker inventory is not zero: {before_trust}")

    patch = render_patch(authority_text, integrated_text)
    if args.mode == "forward":
        result = integrated
        result_info = integrated_info
    else:
        result = authority_text.encode("utf-8")
        result_info = shape(result, "inverse output")
        require_exact(result_info, expected_input, "inverse output")

    audit = {
        "schema": SCHEMA,
        "status": "STATIC_INTEGRATION_PASS_NOT_LEAN_EXECUTED",
        "mode": args.mode,
        "authority": {
            "head": AUTHORITY_HEAD,
            "probe3_log_sha256": AUTHORITY_LOG_SHA256,
            "probe3_error_headers": 777,
            "probe3_candidate": shape(authority_text.encode("utf-8"), "authority"),
        },
        "probe4_candidate": integrated_info,
        "result": result_info,
        "component_proof": proof,
        "canonical_forward_order": ["early", "mid", "late"],
        "canonical_inverse_order": ["late", "mid", "early"],
        "inverse_byte_equal": True,
        "trust_counts": after_trust,
        "trust_delta_zero": before_trust == after_trust,
        "diff": diff_stats(patch),
        "lean_executed": False,
        "lake_executed": False,
        "remote_accessed": False,
    }
    rendered = json.dumps(audit, ensure_ascii=False, indent=2, sort_keys=True) + "\n"
    args.output.write_bytes(result)
    args.audit.write_text(rendered, encoding="utf-8", newline="\n")
    args.patch.write_text(patch, encoding="utf-8", newline="\n")
    print(rendered, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
