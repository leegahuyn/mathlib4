#!/usr/bin/env python3
"""Compose six sealed Probe9 repair components over exact terminal Probe8.

All component helpers are exact-input sealed.  The integrated output seal is
filled after one deterministic bootstrap projection.  Pairwise commutation of
all components proves every complete order equivalent without enumerating 6!.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import re
import runpy
from pathlib import Path


SCHEMA = "qym-probe9-integrated-transform-v1"
INPUT_SHA256 = "63baae8766e3208ac1d8dfa66946ac5ae3cf4a4264d21218a1ccb17aed3c4fd8"
INPUT_GIT_BLOB = "a2d3f4f60018fc2bfebd904db17aa13025c39ed6"
INPUT_BYTES = 2_916_737
INPUT_LF = 61_671
LOG_SHA256 = "4408bf46825d32a935de970904c711510b774ef93026fbee3e20dbc18392beea"
ERROR_HEADERS_SHA256 = "9f0d91787942db9470e307c5a44d8523b2b362ad31f737da0eb48b3f9f2d181f"

COMPONENT_HELPER_SHA256: dict[str, str | None] = {
    "early2": "d644233fcbe2f4bdaa9cbe5d9f0fd5b9c6bc5ce19961ebded59122c9113508a3",
    "frontier_next2": "1e2074beeb236f8099ea227863547d34c52af7ce7ccfbcd10237479b9be5b11c",
    "p50k": "44b17336ea2cfa089c461e8c23cf25d2de95987e106e8473f2765cb2bf5faab4",
    "p55k": "605fc454aea53613082b357004ed182ac1ec12cc813258640d4904cc054e2d6f",
    "tail60k": "d6bf9e829c4bc54528b4abe62b15e631f642ba27e7e699434bc5d548b3630125",
    "extendofnorm": "2d2fadc115ecf9e1eef0d6b5b58637bdc371a27756b5612db8f64ccf1484afe9",
}
COMPONENT_OUTPUT_SHA256: dict[str, str | None] = {
    "early2": "ee93d31d02b79f177d7ce7691f323df27baa1c09da873439089c6eac32d8b966",
    "frontier_next2": "fd8516247b2ea4005bd4f4d40d17ceda23dff33876d7ef47dbda3af455e41f7a",
    "p50k": "a88a419b821e5128ad97ff3d853017bcbe73cfadaa5236064d4104b477343641",
    "p55k": "5fb8300a3fdca11da31577c5c6a176c7d4fa5fcc13fd4b8dca951f521be3f66f",
    "tail60k": "74c51382cf810039c1bec6123724e890a35dd44dae187f4af5a677fce64a088a",
    "extendofnorm": "21a49adb8f3f2b4229161c147293a328d64d0d47be8d0990a9a8b6e4b76b9fb8",
}

OUTPUT_SHA256 = "fb37854ff158ae20a2acebe7722847726eb651ba9c716eff6b903cb4f32e8029"
OUTPUT_GIT_BLOB = "d29c6aff411f93b3c44d7d866fe2b2558f616a87"
OUTPUT_BYTES = 2_921_397
OUTPUT_LF = 61_746


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git_blob(data: bytes) -> str:
    return hashlib.sha1(
        b"blob " + str(len(data)).encode("ascii") + b"\0" + data
    ).hexdigest()


def shape(data: bytes) -> dict[str, object]:
    data.decode("utf-8")
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


def require_complete_seal() -> None:
    pending = [
        name
        for name in COMPONENT_HELPER_SHA256
        if COMPONENT_HELPER_SHA256[name] is None
        or COMPONENT_OUTPUT_SHA256[name] is None
    ]
    if pending:
        raise RuntimeError(
            "Probe9 integrator is activation=false; pending exact-Probe8 "
            f"components: {', '.join(pending)}"
        )


def load_component(name: str, path: Path) -> dict[str, object]:
    wanted_helper = COMPONENT_HELPER_SHA256[name]
    wanted_output = COMPONENT_OUTPUT_SHA256[name]
    assert wanted_helper is not None and wanted_output is not None
    raw = path.read_bytes()
    if sha256(raw) != wanted_helper:
        raise RuntimeError(f"{name} helper sha256 {sha256(raw)} != {wanted_helper}")
    module = runpy.run_path(str(path))
    for key, wanted in (
        ("INPUT_SHA256", INPUT_SHA256),
        ("INPUT_GIT_BLOB", INPUT_GIT_BLOB),
        ("INPUT_BYTES", INPUT_BYTES),
        ("INPUT_LF", INPUT_LF),
        ("LOG_SHA256", LOG_SHA256),
        ("OUTPUT_SHA256", wanted_output),
    ):
        if module[key] != wanted:
            raise RuntimeError(f"{name} {key}: {module[key]} != {wanted}")
    module_headers = module.get(
        "ERROR_HEADERS_SHA256", module.get("HEADERS_SHA256")
    )
    if module_headers != ERROR_HEADERS_SHA256:
        raise RuntimeError(
            f"{name} headers sha256: {module_headers} != {ERROR_HEADERS_SHA256}"
        )
    return module


def compose(
    text: str,
    order: tuple[str, ...],
    modules: dict[str, dict[str, object]],
    *,
    inverse: bool,
) -> tuple[str, list[dict[str, object]]]:
    applied = tuple(reversed(order)) if inverse else order
    audit: list[dict[str, object]] = []
    for name in applied:
        text, component_audit = modules[name]["transform"](text, inverse)
        audit.append(
            {
                "component": name,
                "direction": "inverse" if inverse else "forward",
                "rules": len(component_audit),
                "active_occurrences": sum(x["occurrences"] for x in component_audit),
            }
        )
    return text, audit


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--early2-helper", type=Path, required=True)
    parser.add_argument("--frontier-next2-helper", type=Path, required=True)
    parser.add_argument("--p50k-helper", type=Path, required=True)
    parser.add_argument("--p55k-helper", type=Path, required=True)
    parser.add_argument("--tail60k-helper", type=Path, required=True)
    parser.add_argument("--extendofnorm-helper", type=Path, required=True)
    parser.add_argument("--probe8-log", type=Path, required=True)
    parser.add_argument("--probe8-error-headers", type=Path, required=True)
    parser.add_argument("--audit", type=Path, required=True)
    parser.add_argument("--mode", choices=("forward", "inverse"), default="forward")
    parser.add_argument("--bootstrap-seal", action="store_true")
    args = parser.parse_args()

    require_complete_seal()
    paths = {
        "early2": args.early2_helper,
        "frontier_next2": args.frontier_next2_helper,
        "p50k": args.p50k_helper,
        "p55k": args.p55k_helper,
        "tail60k": args.tail60k_helper,
        "extendofnorm": args.extendofnorm_helper,
    }
    modules = {name: load_component(name, path) for name, path in paths.items()}

    log = args.probe8_log.read_bytes()
    headers = args.probe8_error_headers.read_bytes()
    if sha256(log) != LOG_SHA256 or sha256(headers) != ERROR_HEADERS_SHA256:
        raise RuntimeError("exact Probe8 diagnostic authority mismatch")
    verified_counts: dict[str, dict[str, int]] = {}
    for name, module in modules.items():
        verified = module["verify_authority"](log, headers)
        if isinstance(verified, tuple):
            direct_rows, cascade_rows = verified
        else:
            direct_rows = [row for row in verified if row.get("kind", "direct") == "direct"]
            cascade_rows = [row for row in verified if row.get("kind") == "cascade"]
        verified_counts[name] = {
            "direct": len(direct_rows),
            "cascade": len(cascade_rows),
        }

    inverse = args.mode == "inverse"
    source_raw = args.input.read_bytes()
    source_shape = shape(source_raw)
    source_expected = OUTPUT_SHA256 if inverse else INPUT_SHA256
    if source_shape["sha256"] != source_expected:
        raise RuntimeError(
            f"input sha256 {source_shape['sha256']} != {source_expected}"
        )
    if source_shape["cr"] or source_shape["nul"] or source_shape["bom"]:
        raise RuntimeError(f"input hygiene failure: {source_shape}")
    source = source_raw.decode("utf-8")

    canonical_order = tuple(paths)
    result, component_audit = compose(
        source, canonical_order, modules, inverse=inverse
    )
    result_raw = result.encode("utf-8")
    result_shape = shape(result_raw)
    result_expected = INPUT_SHA256 if inverse else OUTPUT_SHA256
    if not args.bootstrap_seal and result_shape["sha256"] != result_expected:
        raise RuntimeError(
            f"output sha256 {result_shape['sha256']} != {result_expected}"
        )

    # Prove all 6! complete orders equivalent by checking every unordered pair
    # in both directions.  Also check every component's standalone inverse,
    # the canonical full forward/reverse path, and deterministic full samples.
    baseline = source if not inverse else result
    expected_endpoint = result if not inverse else source
    standalone_audit: list[dict[str, object]] = []
    for name in canonical_order:
        projected, _ = compose(baseline, (name,), modules, inverse=False)
        restored, _ = compose(projected, (name,), modules, inverse=True)
        if restored != baseline:
            raise RuntimeError(f"standalone inverse mismatch: {name}")
        standalone_audit.append({"component": name, "inverse_exact": True})

    pair_audit: list[dict[str, object]] = []
    for left, right in itertools.combinations(canonical_order, 2):
        lr, _ = compose(baseline, (left, right), modules, inverse=False)
        rl, _ = compose(baseline, (right, left), modules, inverse=False)
        if lr != rl:
            raise RuntimeError(f"pair does not commute: {left}, {right}")
        lr_restored, _ = compose(lr, (left, right), modules, inverse=True)
        rl_restored, _ = compose(rl, (right, left), modules, inverse=True)
        if lr_restored != baseline or rl_restored != baseline:
            raise RuntimeError(f"pair inverse mismatch: {left}, {right}")
        pair_audit.append(
            {
                "pair": [left, right],
                "both_orders_equal": True,
                "both_matching_inverses_exact": True,
            }
        )

    canonical_endpoint, _ = compose(
        baseline, canonical_order, modules, inverse=False
    )
    canonical_restored, _ = compose(
        canonical_endpoint, canonical_order, modules, inverse=True
    )
    if canonical_endpoint != expected_endpoint or canonical_restored != baseline:
        raise RuntimeError("canonical full composition/inverse mismatch")

    samples = (
        canonical_order,
        tuple(reversed(canonical_order)),
        canonical_order[1:] + canonical_order[:1],
        canonical_order[2:] + canonical_order[:2],
        canonical_order[::2] + canonical_order[1::2],
        canonical_order[1::2] + canonical_order[::2],
    )
    sample_audit: list[dict[str, object]] = []
    for order in samples:
        alternate, _ = compose(baseline, order, modules, inverse=False)
        restored, _ = compose(alternate, order, modules, inverse=True)
        if alternate != expected_endpoint or restored != baseline:
            raise RuntimeError(f"sample order mismatch: {order}")
        sample_audit.append(
            {"order": list(order), "endpoint_equal": True, "inverse_exact": True}
        )

    if trust(source) != trust(result) or any(trust(result).values()):
        raise RuntimeError("trust inventory changed or is nonzero")
    if args.output.exists() or args.audit.exists():
        raise RuntimeError("refusing to overwrite output or audit")
    family_counts = {name: len(module["RULES"]) for name, module in modules.items()}
    occurrence_counts = {
        name: sum(rule.occurrences for rule in module["RULES"])
        for name, module in modules.items()
    }
    record = {
        "schema": SCHEMA,
        "status": "STATIC_PASS_EXACT_PROBE8_SIX_COMPONENT_NOT_LEAN_EXECUTED",
        "activation": True,
        "promotion": False,
        "mode": args.mode,
        "authority": {
            "probe8_run": 31969310662,
            "probe8_github_sha": "a973fa165427d73a143d30cbe58a06405d88996c",
            "probe8_candidate_sha256": INPUT_SHA256,
            "probe8_log_sha256": LOG_SHA256,
            "probe8_error_headers_sha256": ERROR_HEADERS_SHA256,
            "probe8_error_headers": 344,
            "probe8_warning_headers": 374,
            "probe8_exit": 1,
            "probe8_panic": 0,
        },
        "source": source_shape,
        "result": result_shape,
        "component_helper_sha256": COMPONENT_HELPER_SHA256,
        "component_output_sha256": COMPONENT_OUTPUT_SHA256,
        "component_families": family_counts,
        "component_occurrences": occurrence_counts,
        "component_verified_headers": verified_counts,
        "repair_families": sum(family_counts.values()),
        "active_occurrences": sum(occurrence_counts.values()),
        "direct_headers_verified": sum(x["direct"] for x in verified_counts.values()),
        "cascade_headers_verified": sum(x["cascade"] for x in verified_counts.values()),
        "component_audit": component_audit,
        "standalone_inverse_audit": standalone_audit,
        "pair_commutation_audit": pair_audit,
        "pairs_checked": len(pair_audit),
        "sample_complete_orders": sample_audit,
        "sample_complete_orders_checked": len(sample_audit),
        "all_720_orders_implied_by_pairwise_commutation": True,
        "trust": trust(result),
        "execution": {
            "lean": False,
            "lake": False,
            "git_mutation": False,
            "network": False,
            "remote": False,
            "canonical_source_mutation": False,
        },
    }
    args.output.write_bytes(result_raw)
    args.audit.write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(record, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
