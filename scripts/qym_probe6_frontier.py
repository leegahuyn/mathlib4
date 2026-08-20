#!/usr/bin/env python3
"""Exact reversible Probe6 frontier repair over Probe5 authority 30edb320.

This helper performs only byte-exact, count-guarded text transformations.  It
does not invoke Lean/Lake, access the network, mutate repository source, or
authorize promotion.  Forward and inverse modes are both identity locked.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from dataclasses import dataclass
from pathlib import Path


INPUT_SHA256 = "30edb320b25eadbfda284160016a5a23cc28a95d6228cbd061161d4ec615de7c"
INPUT_GIT_BLOB = "9ea2ef7d03555cca4e82cbeeb01cba033dff6b99"
INPUT_BYTES = 2_911_806
INPUT_LF = 61_557
LOG_SHA256 = "c9a9799987cb18047c580777841d5cd4f0e32c592d5ab72062d05b0b9022acae"
OUTPUT_SHA256 = "12a402e6f61451a6c58fa5f9ebc7f7f58458758bcbef5b4727dc5aa8a84729c7"
OUTPUT_GIT_BLOB = "e851e30295928cec2ef35ffdb48ead092f7643ff"
OUTPUT_BYTES = 2_912_179
OUTPUT_LF = 61_565


@dataclass(frozen=True)
class Rule:
    label: str
    error_lines: tuple[int, ...]
    old: str
    new: str


RULES: tuple[Rule, ...] = (
    Rule(
        "use_correct_add_side_for_neg_abs_bound",
        (21858,),
        "      exact add_le_add_left\n"
        "        (neg_abs_le (inner ℝ (B (x : H₀)) (x : H₀)))\n"
        "        (inner ℝ (A x) (x : H₀))\n",
        "      exact add_le_add_right\n"
        "        (neg_abs_le (inner ℝ (B (x : H₀)) (x : H₀)))\n"
        "        (inner ℝ (A x) (x : H₀))\n",
    ),
    Rule(
        "install_explicit_restrict_scalars_towers",
        (23237, 23241),
        "local instance instRealInnerH : InnerProductSpace ℝ H :=\n"
        "  InnerProductSpace.rclikeToReal 𝕜 H\n"
        "\n"
        "/-- Continuous forms conjugate-linear in the first variable and linear in\n",
        "local instance instRealInnerH : InnerProductSpace ℝ H :=\n"
        "  InnerProductSpace.rclikeToReal 𝕜 H\n"
        "\n"
        "local instance instRealScalarTowerV : IsScalarTower ℝ 𝕜 V :=\n"
        "  RestrictScalars.isScalarTower _ _ _\n"
        "\n"
        "local instance instRealScalarTowerH : IsScalarTower ℝ 𝕜 H :=\n"
        "  RestrictScalars.isScalarTower _ _ _\n"
        "\n"
        "/-- Continuous forms conjugate-linear in the first variable and linear in\n",
    ),
    Rule(
        "pin_rclike_scalar_and_normalize_real_rhs",
        (23237, 23241),
        "      (fun r u v => by\n"
        "        rw [RCLike.real_smul_eq_coe_smul, map_smulₛₗ,\n"
        "          smul_apply, starRingEnd_apply, RCLike.conj_ofReal,\n"
        "          smul_eq_mul, RCLike.re_ofReal_mul])\n"
        "      (fun u v w => by rw [map_add, map_add])\n"
        "      (fun r u v => by\n"
        "        rw [RCLike.real_smul_eq_coe_smul, map_smul,\n"
        "          smul_eq_mul, RCLike.re_ofReal_mul]))\n",
        "      (fun r u v => by\n"
        "        change RCLike.re (C (r • u) v) = r * RCLike.re (C u v)\n"
        "        rw [RCLike.real_smul_eq_coe_smul (K := 𝕜) r u, map_smulₛₗ,\n"
        "          smul_apply, starRingEnd_apply, RCLike.conj_ofReal,\n"
        "          smul_eq_mul, RCLike.re_ofReal_mul])\n"
        "      (fun u v w => by rw [map_add, map_add])\n"
        "      (fun r u v => by\n"
        "        change RCLike.re (C u (r • v)) = r * RCLike.re (C u v)\n"
        "        rw [RCLike.real_smul_eq_coe_smul (K := 𝕜) r v, map_smul,\n"
        "          smul_eq_mul, RCLike.re_ofReal_mul]))\n",
    ),
)


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
        "axiom": len(re.findall(r"(?m)^\s*axiom\s+", text)),
        "unsafe": len(re.findall(r"(?m)^\s*unsafe\s+", text)),
        "maxHeartbeats_zero": len(
            re.findall(r"set_option\s+maxHeartbeats\s+0\b", text)
        ),
    }


def expected(inverse: bool, result: bool) -> tuple[str, str, int, int]:
    input_shape = (INPUT_SHA256, INPUT_GIT_BLOB, INPUT_BYTES, INPUT_LF)
    output_shape = (OUTPUT_SHA256, OUTPUT_GIT_BLOB, OUTPUT_BYTES, OUTPUT_LF)
    return (input_shape if inverse else output_shape) if result else (
        output_shape if inverse else input_shape
    )


def check_shape(actual: dict[str, object], wanted: tuple[str, str, int, int], *,
                allow_unsealed_result: bool = False) -> None:
    if wanted[0] == "__TO_SEAL__":
        if allow_unsealed_result:
            return
        raise RuntimeError("output identity is not sealed")
    for key, value in zip(("sha256", "git_blob", "bytes", "lf"), wanted, strict=True):
        if actual[key] != value:
            raise RuntimeError(f"{key}: {actual[key]} != {value}")
    if actual["cr"] or actual["nul"] or actual["bom"] or not actual["terminal_lf"]:
        raise RuntimeError(f"text hygiene failure: {actual}")


def transform(text: str, inverse: bool) -> tuple[str, list[dict[str, object]]]:
    audit: list[dict[str, object]] = []
    rules = tuple(reversed(RULES)) if inverse else RULES
    for rule in rules:
        old, new = (rule.new, rule.old) if inverse else (rule.old, rule.new)
        count = text.count(old)
        if count != 1:
            raise RuntimeError(f"{rule.label}: exact count {count}, expected 1")
        text = text.replace(old, new)
        audit.append({
            "label": rule.label,
            "error_lines": list(rule.error_lines),
            "occurrences": count,
            "direction": "inverse" if inverse else "forward",
        })
    return text, audit


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--audit", type=Path, required=True)
    parser.add_argument("--mode", choices=("forward", "inverse"), default="forward")
    parser.add_argument("--bootstrap-seal", action="store_true")
    args = parser.parse_args()
    inverse = args.mode == "inverse"

    source = args.input.read_bytes()
    source_shape = shape(source)
    check_shape(source_shape, expected(inverse, False))
    before_trust = trust(source.decode("utf-8"))
    result_text, rules = transform(source.decode("utf-8"), inverse)
    result = result_text.encode("utf-8")
    result_shape = shape(result)
    check_shape(
        result_shape,
        expected(inverse, True),
        allow_unsealed_result=args.bootstrap_seal and not inverse,
    )
    after_trust = trust(result_text)
    if before_trust != after_trust:
        raise RuntimeError(f"trust inventory changed: {before_trust} -> {after_trust}")
    restored, _ = transform(result_text, not inverse)
    if restored.encode("utf-8") != source:
        raise RuntimeError("opposite transform did not recover input byte-for-byte")
    if args.output.exists() or args.audit.exists():
        raise RuntimeError("refusing to overwrite output or audit")
    args.output.write_bytes(result)
    record = {
        "schema": "qym-probe6-frontier-transform-v1",
        "status": "STATIC_ONLY_NOT_LEAN_EXECUTED_NOT_PROMOTED",
        "mode": args.mode,
        "authority": {
            "probe5_candidate_sha256": INPUT_SHA256,
            "probe5_candidate_git_blob": INPUT_GIT_BLOB,
            "probe5_log_sha256": LOG_SHA256,
            "probe5_error_count": 517,
            "first_error_line": 21858,
        },
        "source": source_shape,
        "result": result_shape,
        "rules": rules,
        "active_occurrences": sum(r["occurrences"] for r in rules),
        "inverse_byte_equal": True,
        "trust": after_trust,
        "execution": {"lean": False, "lake": False, "remote": False,
                      "repository_source_mutation": False},
        "promotion_authorized": False,
    }
    args.audit.write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(record, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
