#!/usr/bin/env python3
"""Compose the sealed early, mid, and late Probe8 static repair tranches."""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import re
import runpy
from pathlib import Path


SCHEMA = "qym-probe8-integrated-transform-v1"
INPUT_SHA256 = "342eb7aab3d5e71fc242706188abdb7cb1804cd04c79ed254e1715fe0876f3eb"
INPUT_GIT_BLOB = "9b53049115afcc674fac88f998b6716abddb0162"
INPUT_BYTES = 2_913_545
INPUT_LF = 61_593
LOG_SHA256 = "c31e12c9b5a47358a5128295f9c05d90783e9c5af79f63576c22f2e0a30120ee"
ERROR_HEADERS_SHA256 = "9384ab9fc971ade6ec6f5817c560f87b01fa9ddc1603630dae85199e79962a10"

TRANCHE_HELPER_SHA256 = {
    "early": "67843a8608038295f570bb15feb8f08cbb6d90f9c166d078fecde9e1ba215cf4",
    "mid": "b529f1df682a1e9b1588399f3a951914452d1d9afb049dd7be22cef1d8570dbf",
    "late": "4b3470fa2296d61002460e6f8532402f0509ae8c3385f36b512a732ad55c8f9f",
}
TRANCHE_OUTPUT_SHA256 = {
    "early": "f3e39898781be3d2199cb297b5bc3fabcc782ae1adc0e971f3360f4aa3a9f4ca",
    "mid": "40f7f1712acafa095860bd28194cc8e239a6165b2810cbf38b9a1887c173000a",
    "late": "af8938858fd710f486601994f31a215bf718c894b44e4c867a3d959d02b4dbb7",
}

# Sealed after the six-order bootstrap projection.
OUTPUT_SHA256 = "63baae8766e3208ac1d8dfa66946ac5ae3cf4a4264d21218a1ccb17aed3c4fd8"
OUTPUT_GIT_BLOB = "a2d3f4f60018fc2bfebd904db17aa13025c39ed6"
OUTPUT_BYTES = 2_916_737
OUTPUT_LF = 61_671


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


def expected(inverse: bool, result: bool) -> tuple[str, str, int, int]:
    source = (INPUT_SHA256, INPUT_GIT_BLOB, INPUT_BYTES, INPUT_LF)
    output = (OUTPUT_SHA256, OUTPUT_GIT_BLOB, OUTPUT_BYTES, OUTPUT_LF)
    if inverse:
        source, output = output, source
    return output if result else source


def check_shape(
    actual: dict[str, object],
    wanted: tuple[str, str, int, int],
    *,
    allow_unsealed: bool = False,
) -> None:
    if wanted[0] != "__TO_SEAL__" or not allow_unsealed:
        for key, value in zip(("sha256", "git_blob", "bytes", "lf"), wanted, strict=True):
            if actual[key] != value:
                raise RuntimeError(f"{key}: {actual[key]} != {value}")
    if actual["cr"] or actual["nul"] or actual["bom"] or not actual["terminal_lf"]:
        raise RuntimeError(f"text hygiene failure: {actual}")


def load_tranche(name: str, path: Path) -> dict[str, object]:
    data = path.read_bytes()
    if sha256(data) != TRANCHE_HELPER_SHA256[name]:
        raise RuntimeError(
            f"{name} helper sha256 {sha256(data)} != {TRANCHE_HELPER_SHA256[name]}"
        )
    module = runpy.run_path(str(path))
    for key, expected_value in (
        ("INPUT_SHA256", INPUT_SHA256),
        ("INPUT_GIT_BLOB", INPUT_GIT_BLOB),
        ("INPUT_BYTES", INPUT_BYTES),
        ("INPUT_LF", INPUT_LF),
        ("LOG_SHA256", LOG_SHA256),
        ("OUTPUT_SHA256", TRANCHE_OUTPUT_SHA256[name]),
    ):
        if module[key] != expected_value:
            raise RuntimeError(f"{name} {key}: {module[key]} != {expected_value}")
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
        text, tranche_audit = modules[name]["transform"](text, inverse)
        audit.append(
            {
                "tranche": name,
                "direction": "inverse" if inverse else "forward",
                "rules": len(tranche_audit),
                "active_occurrences": sum(x["occurrences"] for x in tranche_audit),
            }
        )
    return text, audit


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--early-helper", type=Path, required=True)
    parser.add_argument("--mid-helper", type=Path, required=True)
    parser.add_argument("--late-helper", type=Path, required=True)
    parser.add_argument("--probe7-log", type=Path, required=True)
    parser.add_argument("--probe7-error-headers", type=Path, required=True)
    parser.add_argument("--audit", type=Path, required=True)
    parser.add_argument("--mode", choices=("forward", "inverse"), default="forward")
    parser.add_argument("--bootstrap-seal", action="store_true")
    args = parser.parse_args()
    inverse = args.mode == "inverse"

    modules = {
        "early": load_tranche("early", args.early_helper),
        "mid": load_tranche("mid", args.mid_helper),
        "late": load_tranche("late", args.late_helper),
    }
    log = args.probe7_log.read_bytes()
    headers = args.probe7_error_headers.read_bytes()
    if sha256(log) != LOG_SHA256:
        raise RuntimeError(f"Probe7 log sha256 {sha256(log)} != {LOG_SHA256}")
    if sha256(headers) != ERROR_HEADERS_SHA256:
        raise RuntimeError(
            f"Probe7 headers sha256 {sha256(headers)} != {ERROR_HEADERS_SHA256}"
        )
    verified = {
        "early": modules["early"]["verify_log"](log),
        "mid": modules["mid"]["verify_log"](log),
        "late": modules["late"]["verify_log"](log),
    }
    modules["mid"]["verify_header_artifact"](log, headers)

    source = args.input.read_bytes()
    source_shape = shape(source)
    check_shape(
        source_shape,
        expected(inverse, False),
        allow_unsealed=args.bootstrap_seal and inverse,
    )
    source_text = source.decode("utf-8")
    before_trust = trust(source_text)

    canonical_order = ("early", "mid", "late")
    result_text, tranche_audit = compose(
        source_text, canonical_order, modules, inverse=inverse
    )
    result = result_text.encode("utf-8")
    result_shape = shape(result)
    check_shape(
        result_shape,
        expected(inverse, True),
        allow_unsealed=args.bootstrap_seal and not inverse,
    )

    # Exhaust the 3! tranche orders, and reverse each exact order for its
    # inverse.  All six paths must have the same endpoint and source restore.
    order_audit: list[dict[str, object]] = []
    baseline_source = source_text if not inverse else result_text
    expected_endpoint = result_text if not inverse else source_text
    for order in itertools.permutations(canonical_order):
        if inverse:
            alternate, _ = compose(source_text, order, modules, inverse=True)
            restored, _ = compose(alternate, order, modules, inverse=False)
            assert alternate == result_text
            assert restored == source_text
        else:
            alternate, _ = compose(source_text, order, modules, inverse=False)
            restored, _ = compose(alternate, order, modules, inverse=True)
            assert alternate == result_text
            assert restored == source_text
        order_audit.append(
            {"order": list(order), "endpoint_equal": True, "inverse_exact": True}
        )

    after_trust = trust(result_text)
    if before_trust != after_trust or any(after_trust.values()):
        raise RuntimeError(f"trust inventory changed or nonzero: {before_trust} -> {after_trust}")
    if args.output.exists() or args.audit.exists():
        raise RuntimeError("refusing to overwrite output or audit")

    family_counts = {name: len(module["RULES"]) for name, module in modules.items()}
    occurrence_counts = {
        name: sum(rule.occurrences for rule in module["RULES"])
        for name, module in modules.items()
    }
    direct_header_counts = {
        "early": len(verified["early"]),
        "mid": sum(1 for x in verified["mid"] if x["kind"] == "direct"),
        "late": len(verified["late"]),
    }
    record = {
        "schema": SCHEMA,
        "status": "STATIC_PASS_EXACT_PROBE7_THREE_TRANCHE_NOT_LEAN_EXECUTED",
        "activation": True,
        "promotion": False,
        "mode": args.mode,
        "authority": {
            "parent_commit": "7717b9f958937ade0c99dd8b8f1147ddc185801b",
            "probe7_run_id": 31967530559,
            "probe7_job_id": 95214871166,
            "probe7_artifact_id": 9268991946,
            "probe7_result_sha256": "5f63c123667c452b0d0b83cab03863ecdb849501bccff6bd95d787e89abb95c9",
            "probe7_candidate_sha256": INPUT_SHA256,
            "probe7_log_sha256": LOG_SHA256,
            "probe7_error_headers_sha256": ERROR_HEADERS_SHA256,
            "probe7_error_headers": 414,
            "probe7_warning_headers": 378,
            "probe7_panic": 0,
            "probe7_exit": 1,
        },
        "source": source_shape,
        "result": result_shape,
        "tranche_helper_sha256": TRANCHE_HELPER_SHA256,
        "tranche_families": family_counts,
        "tranche_occurrences": occurrence_counts,
        "tranche_direct_headers": direct_header_counts,
        "repair_families": sum(family_counts.values()),
        "active_occurrences": sum(occurrence_counts.values()),
        "direct_headers_verified": sum(direct_header_counts.values()),
        "cascade_headers_verified": sum(
            1 for x in verified["mid"] if x["kind"] == "cascade"
        ),
        "canonical_order": list(canonical_order),
        "canonical_tranche_audit": tranche_audit,
        "all_six_orders": order_audit,
        "six_orders_equal": True,
        "six_inverse_paths_exact": True,
        "trust": after_trust,
        "execution": {
            "lean": False,
            "lake": False,
            "git_mutation": False,
            "network": False,
            "remote": False,
            "canonical_source_mutation": False,
        },
    }
    args.output.write_bytes(result)
    args.audit.write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(record, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
