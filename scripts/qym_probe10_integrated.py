#!/usr/bin/env python3
"""Compose the four exact-P9 Probe10 repair components.

This is a byte-locked, add-only static integrator.  It verifies the immutable
terminal Probe9 authority, every component helper identity and standalone
seal, all 4! forward orders, every corresponding reverse inverse, cross-rule
collisions, text hygiene, and the trust inventory.  It never invokes Lean,
Lake, Git, or the network and refuses to overwrite its outputs.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import re
import runpy
import sys
from pathlib import Path
from typing import Any


sys.dont_write_bytecode = True

SCHEMA = "qym-probe10-integrated-transform-v1-exact-probe9"

INPUT_SHA256 = "fb37854ff158ae20a2acebe7722847726eb651ba9c716eff6b903cb4f32e8029"
INPUT_GIT_BLOB = "d29c6aff411f93b3c44d7d866fe2b2558f616a87"
INPUT_BYTES = 2_921_397
INPUT_LF = 61_746

LOG_SHA256 = "e8315f541ddcd8d9f99a395caddbcf57ceb3a1457a900bcefb45422dff81cd0f"
HEADERS_SHA256 = "e8b25cc78d4f2a9915cd25c6c7700f7f80ca73c7f01229fe531e3ef13386186f"
DIAGNOSTICS_SHA256 = "a34f5b424f8aac739ac05ce4375003fe9da7f0ee4689050d4d712c9816f66580"

OUTPUT_SHA256 = "ef19b4f666bd7238164aec7795e10c3f802d9a3e49e5d5f617cc09d4cbe617dc"
OUTPUT_GIT_BLOB = "496c24e5a90d1f72c66bb03fcc9d3565a06f4b2e"
OUTPUT_BYTES = 2_923_612
OUTPUT_LF = 61_783

CANONICAL_ORDER = ("earlytail", "midlate", "late", "extendofnorm")

COMPONENT_HELPER_SHA256 = {
    "earlytail": "5d7c848db8b8ec238bbdaad29bc5532ae0020f134846d16be064a78372c58434",
    "midlate": "42d8f76c68b19aac520d15659c71d02db2e1beb397cfe0865bcdaf436e885be0",
    "late": "d1c9aef94af3efac77ab5b9b87b2851adbc3eac3fcf7f18e5cc9695a61b7bccd",
    "extendofnorm": "b7942ba8d0ae94dd2827f5a59560a81a291482880c8716df299cc13dbac246bb",
}

COMPONENT_OUTPUT = {
    "earlytail": {
        "sha256": "8c0aa79e298a243690d9cdcfbbfa388deec940dd095787d4c1df1e7180e740e5",
        "git_blob": "5a9304ad8c59300f91a01928f6596bb94d58d463",
        "bytes": 2_922_043,
        "lf": 61_765,
    },
    "midlate": {
        "sha256": "b1f11b801fc665643e728b6083bbea22384e5f4794da512f368b52f8a126cfc4",
        "git_blob": "788601940f92830920aa80bcaa0726322c52c7a4",
        "bytes": 2_921_367,
        "lf": 61_747,
    },
    "late": {
        "sha256": "f31c5aeaf56f8b751cc92b7be4ba0685601f05c55a351ac8695fcb970fb36d78",
        "git_blob": "781f4aff16af80292dfa1a0fccec74514377949f",
        "bytes": 2_922_171,
        "lf": 61_754,
    },
    "extendofnorm": {
        "sha256": "2051f6833163c46631431dda9187aed9f869eaadb4662f43e26c2cecb7cb3006",
        "git_blob": "6b578ba82b4accccf90552bdc21d61197e2226f0",
        "bytes": 2_922_222,
        "lf": 61_755,
    },
}

# No current Probe10 component intentionally refines another component's
# anchor.  The representation is explicit so a future refinement must be
# declared by exact component/rule/field identity before it can be admitted.
DECLARED_REFINEMENTS: frozenset[tuple[str, str, str, str, str, str]] = frozenset()


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git_blob(data: bytes) -> str:
    return hashlib.sha1(
        b"blob " + str(len(data)).encode("ascii") + b"\0" + data
    ).hexdigest()


def shape(data: bytes) -> dict[str, object]:
    data.decode("utf-8", errors="strict")
    return {
        "sha256": sha256(data),
        "git_blob": git_blob(data),
        "bytes": len(data),
        "lf": data.count(b"\n"),
        "cr": b"\r" in data,
        "nul": b"\0" in data,
        "bom": data.startswith(b"\xef\xbb\xbf"),
        "terminal_lf": data.endswith(b"\n"),
    }


def exact_shape(*, output: bool) -> tuple[str, str, int, int]:
    if output:
        return OUTPUT_SHA256, OUTPUT_GIT_BLOB, OUTPUT_BYTES, OUTPUT_LF
    return INPUT_SHA256, INPUT_GIT_BLOB, INPUT_BYTES, INPUT_LF


def check_shape(actual: dict[str, object], wanted: tuple[str, str, int, int]) -> None:
    for key, value in zip(("sha256", "git_blob", "bytes", "lf"), wanted, strict=True):
        if actual[key] != value:
            raise RuntimeError(f"{key}: {actual[key]} != {value}")
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


def verify_authority(log: bytes, headers: bytes, diagnostics: bytes) -> dict[str, int]:
    if sha256(log) != LOG_SHA256:
        raise RuntimeError("terminal Probe9 log identity mismatch")
    if sha256(headers) != HEADERS_SHA256:
        raise RuntimeError("terminal Probe9 error-header identity mismatch")
    if sha256(diagnostics) != DIAGNOSTICS_SHA256:
        raise RuntimeError("terminal Probe9 diagnostics identity mismatch")

    log_lines = log.decode("utf-8", errors="strict").splitlines()
    header_lines = headers.decode("utf-8", errors="strict").splitlines()
    extracted_errors = [
        line
        for line in log_lines
        if re.match(
            r"^PrimalitySheafVerification/QYM\.lean:\d+:\d+: "
            r"error(?:\([^)]*\))?: ",
            line,
        )
    ]
    if extracted_errors != header_lines or len(header_lines) != 287:
        raise RuntimeError("terminal Probe9 exact error-header extraction mismatch")

    rows = [
        json.loads(line)
        for line in diagnostics.decode("utf-8", errors="strict").splitlines()
    ]
    errors = sum(row.get("severity") == "error" for row in rows)
    warnings = sum(row.get("severity") == "warning" for row in rows)
    if errors != 287 or warnings != 361 or len(rows) != 648:
        raise RuntimeError(
            f"terminal Probe9 diagnostic counts mismatch: {errors}/{warnings}/{len(rows)}"
        )
    return {"errors": errors, "warnings": warnings, "rows": len(rows)}


def load_component(name: str, path: Path) -> dict[str, Any]:
    raw = path.read_bytes()
    actual_helper = sha256(raw)
    wanted_helper = COMPONENT_HELPER_SHA256[name]
    if actual_helper != wanted_helper:
        raise RuntimeError(f"{name} helper sha256 {actual_helper} != {wanted_helper}")

    module = runpy.run_path(str(path))
    standalone = COMPONENT_OUTPUT[name]
    expected = (
        ("INPUT_SHA256", INPUT_SHA256),
        ("INPUT_GIT_BLOB", INPUT_GIT_BLOB),
        ("INPUT_BYTES", INPUT_BYTES),
        ("INPUT_LF", INPUT_LF),
        ("LOG_SHA256", LOG_SHA256),
        ("OUTPUT_SHA256", standalone["sha256"]),
        ("OUTPUT_GIT_BLOB", standalone["git_blob"]),
        ("OUTPUT_BYTES", standalone["bytes"]),
        ("OUTPUT_LF", standalone["lf"]),
    )
    for key, wanted in expected:
        if module.get(key) != wanted:
            raise RuntimeError(f"{name} {key}: {module.get(key)!r} != {wanted!r}")
    module_headers = module.get("HEADERS_SHA256", module.get("ERROR_HEADERS_SHA256"))
    if module_headers != HEADERS_SHA256:
        raise RuntimeError(f"{name} headers identity mismatch")
    if "DIAGNOSTICS_SHA256" in module and module["DIAGNOSTICS_SHA256"] != DIAGNOSTICS_SHA256:
        raise RuntimeError(f"{name} diagnostics identity mismatch")
    if not callable(module.get("transform")) or not callable(module.get("verify_authority")):
        raise RuntimeError(f"{name} helper API incomplete")
    rules = module.get("RULES")
    if not isinstance(rules, tuple) or not rules:
        raise RuntimeError(f"{name} RULES must be a nonempty tuple")
    if any(not isinstance(getattr(rule, "occurrences", 1), int) for rule in rules):
        raise RuntimeError(f"{name} occurrence metadata is not integral")
    return module


def spans(text: str, needle: str) -> list[tuple[int, int]]:
    found: list[tuple[int, int]] = []
    start = 0
    while True:
        offset = text.find(needle, start)
        if offset < 0:
            return found
        found.append((offset, offset + len(needle)))
        start = offset + 1


def collision_audit(
    baseline: str, endpoint: str, modules: dict[str, dict[str, Any]]
) -> dict[str, object]:
    relations: list[dict[str, object]] = []
    overlaps: list[dict[str, object]] = []

    for left, right in itertools.combinations(CANONICAL_ORDER, 2):
        for left_rule in modules[left]["RULES"]:
            for right_rule in modules[right]["RULES"]:
                for left_field in ("old", "new"):
                    left_value = getattr(left_rule, left_field)
                    for right_field in ("old", "new"):
                        right_value = getattr(right_rule, right_field)
                        relation = None
                        if left_value == right_value:
                            relation = "equal"
                        elif left_value in right_value:
                            relation = "left_in_right"
                        elif right_value in left_value:
                            relation = "right_in_left"
                        if relation is None:
                            continue
                        key = (
                            left,
                            left_rule.label,
                            left_field,
                            right,
                            right_rule.label,
                            right_field,
                        )
                        row = {
                            "left_component": left,
                            "left_rule": left_rule.label,
                            "left_field": left_field,
                            "right_component": right,
                            "right_rule": right_rule.label,
                            "right_field": right_field,
                            "relation": relation,
                            "declared_refinement": key in DECLARED_REFINEMENTS,
                        }
                        relations.append(row)
                        if key not in DECLARED_REFINEMENTS:
                            raise RuntimeError(f"undeclared cross-anchor relation: {row}")

        for stage, text, field in (
            ("baseline", baseline, "old"),
            ("endpoint", endpoint, "new"),
        ):
            left_spans = [
                (start, end, rule.label)
                for rule in modules[left]["RULES"]
                for start, end in spans(text, getattr(rule, field))
            ]
            right_spans = [
                (start, end, rule.label)
                for rule in modules[right]["RULES"]
                for start, end in spans(text, getattr(rule, field))
            ]
            for lstart, lend, llabel in left_spans:
                for rstart, rend, rlabel in right_spans:
                    if max(lstart, rstart) < min(lend, rend):
                        row = {
                            "stage": stage,
                            "left_component": left,
                            "left_rule": llabel,
                            "right_component": right,
                            "right_rule": rlabel,
                            "left_span": [lstart, lend],
                            "right_span": [rstart, rend],
                        }
                        overlaps.append(row)
                        raise RuntimeError(f"cross-component source-span collision: {row}")

    return {
        "declared_refinements": len(DECLARED_REFINEMENTS),
        "observed_anchor_relations": relations,
        "observed_span_overlaps": overlaps,
        "undeclared_collisions": 0,
    }


def compose(
    text: str,
    order: tuple[str, ...],
    modules: dict[str, dict[str, Any]],
    *,
    inverse: bool,
) -> tuple[str, list[dict[str, object]]]:
    applied = tuple(reversed(order)) if inverse else order
    audit: list[dict[str, object]] = []
    for name in applied:
        text, component_rows = modules[name]["transform"](text, inverse)
        audit.append(
            {
                "component": name,
                "direction": "inverse" if inverse else "forward",
                "families": len(component_rows),
                "occurrences": sum(row["occurrences"] for row in component_rows),
            }
        )
    return text, audit


def verify_all_orders(
    baseline: str, modules: dict[str, dict[str, Any]]
) -> tuple[str, list[dict[str, object]]]:
    canonical_endpoint: str | None = None
    rows: list[dict[str, object]] = []
    for order in itertools.permutations(CANONICAL_ORDER):
        endpoint, forward_rows = compose(baseline, order, modules, inverse=False)
        endpoint_raw = endpoint.encode("utf-8")
        check_shape(shape(endpoint_raw), exact_shape(output=True))
        restored, inverse_rows = compose(endpoint, order, modules, inverse=True)
        if restored != baseline:
            raise RuntimeError(f"matching inverse is not exact for order {order}")
        if canonical_endpoint is None:
            canonical_endpoint = endpoint
        elif endpoint != canonical_endpoint:
            raise RuntimeError(f"forward permutation endpoint mismatch: {order}")
        rows.append(
            {
                "order": list(order),
                "endpoint_sha256": sha256(endpoint_raw),
                "endpoint_equal": True,
                "matching_reverse_inverse_exact": True,
                "forward_components": forward_rows,
                "inverse_components": inverse_rows,
            }
        )
    assert canonical_endpoint is not None
    if len(rows) != 24:
        raise RuntimeError("did not enumerate all 4! forward orders")
    return canonical_endpoint, rows


def component_diagnostic_map(
    modules: dict[str, dict[str, Any]],
    log: bytes,
    headers: bytes,
    diagnostics: bytes,
) -> dict[str, dict[str, int]]:
    counts: dict[str, dict[str, int]] = {}
    for name, module in modules.items():
        if "DIAGNOSTICS_SHA256" in module:
            verified = module["verify_authority"](log, headers, diagnostics)
        else:
            verified = module["verify_authority"](log, headers)
        if isinstance(verified, tuple):
            direct_rows, cascade_rows = verified
        else:
            direct_rows = [
                row for row in verified if row.get("kind", "direct") == "direct"
            ]
            cascade_rows = [row for row in verified if row.get("kind") == "cascade"]
        counts[name] = {
            "direct": len(direct_rows),
            "cascade": len(cascade_rows),
        }
    return counts


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--earlytail-helper", type=Path, required=True)
    parser.add_argument("--midlate-helper", type=Path, required=True)
    parser.add_argument("--late-helper", type=Path, required=True)
    parser.add_argument("--extendofnorm-helper", type=Path, required=True)
    parser.add_argument("--probe9-log", type=Path, required=True)
    parser.add_argument("--probe9-error-headers", type=Path, required=True)
    parser.add_argument("--probe9-diagnostics", type=Path, required=True)
    parser.add_argument("--audit", type=Path, required=True)
    parser.add_argument("--mode", choices=("forward", "inverse"), default="forward")
    args = parser.parse_args()

    paths = {
        "earlytail": args.earlytail_helper,
        "midlate": args.midlate_helper,
        "late": args.late_helper,
        "extendofnorm": args.extendofnorm_helper,
    }
    if tuple(paths) != CANONICAL_ORDER:
        raise RuntimeError("canonical component order drift")
    modules = {name: load_component(name, path) for name, path in paths.items()}

    log = args.probe9_log.read_bytes()
    headers = args.probe9_error_headers.read_bytes()
    diagnostics = args.probe9_diagnostics.read_bytes()
    authority_counts = verify_authority(log, headers, diagnostics)
    verified_counts = component_diagnostic_map(
        modules, log, headers, diagnostics
    )

    source_raw = args.input.read_bytes()
    source_shape = shape(source_raw)
    inverse = args.mode == "inverse"
    check_shape(source_shape, exact_shape(output=inverse))
    source = source_raw.decode("utf-8", errors="strict")

    if inverse:
        baseline, component_rows = compose(
            source, CANONICAL_ORDER, modules, inverse=True
        )
        check_shape(shape(baseline.encode("utf-8")), exact_shape(output=False))
    else:
        baseline = source
        component_rows = []

    endpoint, order_rows = verify_all_orders(baseline, modules)
    collision = collision_audit(baseline, endpoint, modules)
    if inverse:
        result = baseline
    else:
        result = endpoint
        _, component_rows = compose(
            baseline, CANONICAL_ORDER, modules, inverse=False
        )

    result_raw = result.encode("utf-8")
    result_shape = shape(result_raw)
    check_shape(result_shape, exact_shape(output=not inverse))
    if trust(baseline) != trust(endpoint) or any(trust(endpoint).values()):
        raise RuntimeError("trust inventory changed or is nonzero")
    if args.output.exists() or args.audit.exists():
        raise RuntimeError("refusing to overwrite output or audit")

    family_counts = {name: len(module["RULES"]) for name, module in modules.items()}
    occurrence_counts = {
        name: sum(getattr(rule, "occurrences", 1) for rule in module["RULES"])
        for name, module in modules.items()
    }
    record = {
        "schema": SCHEMA,
        "status": "STATIC_PASS_EXACT_PROBE9_FOUR_COMPONENT_NOT_LEAN_EXECUTED",
        "activation": True,
        "promotion": False,
        "mode": args.mode,
        "authority": {
            "probe9_run": 31971447929,
            "probe9_job": 95224434420,
            "probe9_artifact_id": 9270002403,
            "probe9_trigger_sha": "3b5e67d81c4d8979f2c4b57c9f2b7839b0806388",
            "probe9_artifact_name": "qym-repair-probe9-integrated-3b5e67d81c4d8979f2c4b57c9f2b7839b0806388-attempt1",
            "probe9_artifact_zip_sha256": "1557150d50cefac45a193610cc6ccc4ffb673005026e4c34ea294895b8a78f49",
            "probe9_result_sha256": "aeda853726579f5a6185b5e3e740bb131f36d9ce73464582c96e0298e057e3d8",
            "probe9_candidate_sha256": INPUT_SHA256,
            "probe9_candidate_git_blob": INPUT_GIT_BLOB,
            "probe9_log_sha256": LOG_SHA256,
            "probe9_error_headers_sha256": HEADERS_SHA256,
            "probe9_diagnostics_sha256": DIAGNOSTICS_SHA256,
            "probe9_error_headers": authority_counts["errors"],
            "probe9_warning_headers": authority_counts["warnings"],
            "probe9_exit": 1,
            "probe9_panic": 0,
        },
        "source": source_shape,
        "result": result_shape,
        "component_helper_sha256": COMPONENT_HELPER_SHA256,
        "component_standalone_output": COMPONENT_OUTPUT,
        "component_families": family_counts,
        "component_occurrences": occurrence_counts,
        "component_verified_headers": verified_counts,
        "repair_families": sum(family_counts.values()),
        "active_occurrences": sum(occurrence_counts.values()),
        "direct_headers_verified": sum(row["direct"] for row in verified_counts.values()),
        "cascade_headers_verified": sum(row["cascade"] for row in verified_counts.values()),
        "canonical_order": list(CANONICAL_ORDER),
        "component_audit": component_rows,
        "collision_audit": collision,
        "complete_order_audit": order_rows,
        "all_24_forward_orders_explicitly_checked": True,
        "all_24_matching_reverse_inverses_exact": True,
        "trust": trust(result),
        "execution": {
            "lean": False,
            "lake": False,
            "git": False,
            "network": False,
            "remote": False,
            "canonical_source_mutation": False,
            "python_bytecode_created": False,
        },
    }
    args.output.write_bytes(result_raw)
    args.audit.write_text(
        json.dumps(record, indent=2) + "\n", encoding="utf-8", newline="\n"
    )
    print(json.dumps(record, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
