#!/usr/bin/env python3
"""Exact reversible repair for the observed realPartForm constructor roots."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path


EXPECTED_INPUT_SHA256 = "fb9d451c88d55e71398f3e3a4b38b3cc9ff5e0a37273115579fc2351d1fdad9c"
EXPECTED_INPUT_GIT_BLOB = "b08d7bb621d8acc8338f3afa3f12ac2ff2c7e6d1"
EXPECTED_INPUT_BYTES = 2_910_229
EXPECTED_INPUT_LF = 61_523
EXPECTED_LOG_SHA256 = "3ce6d19d831d1723b19fb15181e9561cb1e6b8744e130812838469a03011ddc6"
EXPECTED_OUTPUT_SHA256 = "f4e4eca05adf0adb62f4881acacdaaeff9a8b61834651ecaf181620399c7f2e4"
EXPECTED_OUTPUT_GIT_BLOB = "46e9829e6daabebe466fc8a131c509804543b497"
EXPECTED_OUTPUT_BYTES = 2_910_186
EXPECTED_OUTPUT_LF = 61_524

LABEL = "realPartForm_explicit_add_and_real_smul_maps"
ERROR_LINES = (23220, 23221, 23226)

OLD = """      (fun u w v => by simp only [ContinuousLinearMap.map_add₂, map_add])
      (fun r u v => by
        simp only [RCLike.real_smul_eq_coe_smul,
          ContinuousLinearMap.map_smulₛₗ₂, starRingEnd_apply,
          RCLike.conj_ofReal, smul_eq_mul, RCLike.re_ofReal_mul])
      (fun u v w => by simp only [map_add, map_add])
      (fun r u v => by
        simp only [RCLike.real_smul_eq_coe_smul, map_smul,
          smul_eq_mul, RCLike.re_ofReal_mul]))
"""

NEW = """      (fun u w v => by
        rw [map_add, add_apply, map_add])
      (fun r u v => by
        rw [RCLike.real_smul_eq_coe_smul, map_smulₛₗ,
          smul_apply, starRingEnd_apply, RCLike.conj_ofReal,
          smul_eq_mul, RCLike.re_ofReal_mul])
      (fun u v w => by rw [map_add, map_add])
      (fun r u v => by
        rw [RCLike.real_smul_eq_coe_smul, map_smul,
          smul_eq_mul, RCLike.re_ofReal_mul]))
"""


def sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def git_blob(raw: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest()


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


def trust_counts(text: str) -> dict[str, int]:
    return {
        "sorry": len(re.findall(r"\bsorry\b", text)),
        "admit": len(re.findall(r"\badmit\b", text)),
        "native_decide": len(re.findall(r"\bnative_decide\b", text)),
        "Lean.ofReduceBool": text.count("Lean.ofReduceBool"),
        "axiom_declaration": len(re.findall(r"(?m)^\s*axiom\s+", text)),
        "unsafe_declaration": len(re.findall(r"(?m)^\s*unsafe\s+", text)),
        "maxHeartbeats_zero": len(re.findall(r"set_option\s+maxHeartbeats\s+0\b", text)),
    }


def transform(text: str, *, inverse: bool = False) -> tuple[str, list[dict[str, object]]]:
    old, new = (NEW, OLD) if inverse else (OLD, NEW)
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f"{LABEL}: {count} exact occurrences, expected 1")
    if text.count(new) != 0:
        raise RuntimeError(f"{LABEL}: opposite block already present")
    return text.replace(old, new), [{
        "label": LABEL,
        "probe4_error_lines": list(ERROR_LINES),
        "occurrences": 1,
        "direction": "inverse" if inverse else "forward",
    }]


def expected(*, output: bool) -> tuple[str, str, int, int]:
    if output:
        return EXPECTED_OUTPUT_SHA256, EXPECTED_OUTPUT_GIT_BLOB, EXPECTED_OUTPUT_BYTES, EXPECTED_OUTPUT_LF
    return EXPECTED_INPUT_SHA256, EXPECTED_INPUT_GIT_BLOB, EXPECTED_INPUT_BYTES, EXPECTED_INPUT_LF


def assert_shape(actual: dict[str, object], wanted: tuple[str, str, int, int], allow: bool) -> None:
    if wanted[0] == "__TO_SEAL__" and allow:
        return
    for key, value in zip(("sha256", "git_blob", "bytes", "lf"), wanted, strict=True):
        if actual[key] != value:
            raise RuntimeError(f"{key}: {actual[key]} != {value}")
    if actual["cr"] or actual["nul"] or actual["bom"] or not actual["terminal_lf"]:
        raise RuntimeError(f"text hygiene: {actual}")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--audit", type=Path, required=True)
    parser.add_argument("--mode", choices=("forward", "inverse"), default="forward")
    parser.add_argument("--allow-unsealed", action="store_true")
    args = parser.parse_args()
    inverse = args.mode == "inverse"
    raw = args.input.read_bytes()
    before = shape(raw)
    assert_shape(before, expected(output=inverse), args.allow_unsealed)
    text = raw.decode("utf-8")
    projected_text, rules = transform(text, inverse=inverse)
    projected = projected_text.encode("utf-8")
    after = shape(projected)
    assert_shape(after, expected(output=not inverse), args.allow_unsealed)
    if trust_counts(text) != trust_counts(projected_text):
        raise RuntimeError("trust delta")
    args.output.write_bytes(projected)
    audit = {
        "schema": "qym-probe5-realpartform23220-transform-v1",
        "status": "STATIC_OBSERVED_NOT_LEAN_EXECUTED",
        "direction": "inverse" if inverse else "forward",
        "input": before,
        "output": after,
        "rules": rules,
        "trust_before": trust_counts(text),
        "trust_after": trust_counts(projected_text),
        "ready_for_probe5_inclusion": True,
        "promotion_authorized": False,
        "execution": {"lean": False, "lake": False, "remote": False},
    }
    args.audit.write_text(json.dumps(audit, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(audit, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
