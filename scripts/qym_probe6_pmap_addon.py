#!/usr/bin/env python3
"""Optional exact Probe6 repair for the direct pmap-eigenvalue survivor."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path


INPUT_SHA256 = "12a402e6f61451a6c58fa5f9ebc7f7f58458758bcbef5b4727dc5aa8a84729c7"
INPUT_GIT_BLOB = "e851e30295928cec2ef35ffdb48ead092f7643ff"
INPUT_BYTES = 2_912_179
INPUT_LF = 61_565
OUTPUT_SHA256 = "df5b72cf703cc246baf0eeb54e77a3676aff42f6b36370e76ca7904ea9c2d92f"
OUTPUT_GIT_BLOB = "7c483a662608871c278afeab7ab92f7b76f0977e"
OUTPUT_BYTES = 2_912_255
OUTPUT_LF = 61_567

OLD = (
    "  let xd : T.domain := ⟨x, hxDomain⟩\n"
    "  have hinner : inner 𝕜 x x ≠ 0 := inner_self_ne_zero.mpr hxne\n"
    "  apply mul_right_cancel₀ hinner\n"
    "  simpa only [hxEq, inner_smul_left, inner_smul_right] using hsymm xd xd\n"
)
NEW = (
    "  let xd : T.domain := ⟨x, hxDomain⟩\n"
    "  have hxd : T xd = lambda • (xd : H) := by\n"
    "    simpa only [xd] using hxEq\n"
    "  have hinner : inner 𝕜 x x ≠ 0 := inner_self_ne_zero.mpr hxne\n"
    "  apply mul_right_cancel₀ hinner\n"
    "  simpa only [hxd, inner_smul_left, inner_smul_right] using hsymm xd xd\n"
)


def shape(data: bytes) -> dict[str, object]:
    data.decode("utf-8")
    return {
        "sha256": hashlib.sha256(data).hexdigest(),
        "git_blob": hashlib.sha1(
            b"blob " + str(len(data)).encode() + b"\0" + data
        ).hexdigest(),
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
        "maxHeartbeats_zero": len(re.findall(r"set_option\s+maxHeartbeats\s+0\b", text)),
    }


def expected(output: bool) -> tuple[str, str, int, int]:
    return (
        (OUTPUT_SHA256, OUTPUT_GIT_BLOB, OUTPUT_BYTES, OUTPUT_LF)
        if output else
        (INPUT_SHA256, INPUT_GIT_BLOB, INPUT_BYTES, INPUT_LF)
    )


def check(actual: dict[str, object], wanted: tuple[str, str, int, int], bootstrap: bool) -> None:
    if wanted[0] == "__TO_SEAL__" and bootstrap:
        return
    for key, value in zip(("sha256", "git_blob", "bytes", "lf"), wanted, strict=True):
        if actual[key] != value:
            raise RuntimeError(f"{key}: {actual[key]} != {value}")
    if actual["cr"] or actual["nul"] or actual["bom"] or not actual["terminal_lf"]:
        raise RuntimeError(f"hygiene failure: {actual}")


def main() -> int:
    p = argparse.ArgumentParser()
    p.add_argument("input", type=Path)
    p.add_argument("output", type=Path)
    p.add_argument("--audit", type=Path, required=True)
    p.add_argument("--mode", choices=("forward", "inverse"), default="forward")
    p.add_argument("--bootstrap-seal", action="store_true")
    a = p.parse_args()
    inverse = a.mode == "inverse"
    source = a.input.read_bytes()
    check(shape(source), expected(inverse), False)
    old, new = (NEW, OLD) if inverse else (OLD, NEW)
    text = source.decode("utf-8")
    if text.count(old) != 1:
        raise RuntimeError(f"pmap block exact count {text.count(old)}, expected 1")
    before = trust(text)
    result = text.replace(old, new).encode("utf-8")
    after = trust(result.decode("utf-8"))
    if before != after:
        raise RuntimeError(f"trust changed: {before} -> {after}")
    check(shape(result), expected(not inverse), a.bootstrap_seal and not inverse)
    back_old, back_new = (OLD, NEW) if inverse else (NEW, OLD)
    result_text = result.decode("utf-8")
    if result_text.count(back_old) != 1:
        raise RuntimeError("opposite exact block count is not one")
    if result_text.replace(back_old, back_new).encode("utf-8") != source:
        raise RuntimeError("roundtrip failure")
    if a.output.exists() or a.audit.exists():
        raise RuntimeError("refusing overwrite")
    a.output.write_bytes(result)
    record = {
        "schema": "qym-probe6-pmap-addon-v1",
        "status": "STATIC_ONLY_NOT_LEAN_EXECUTED_NOT_PROMOTED",
        "mode": a.mode,
        "source": shape(source),
        "result": shape(result),
        "rule": "bind_let_domain_eigen_equation_before_formal_adjoint_simplification",
        "probe5_error_line": 24559,
        "occurrences": 1,
        "inverse_byte_equal": True,
        "trust": after,
        "execution": {"lean": False, "lake": False, "remote": False,
                      "repository_source_mutation": False},
        "promotion_authorized": False,
    }
    a.audit.write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(record, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
