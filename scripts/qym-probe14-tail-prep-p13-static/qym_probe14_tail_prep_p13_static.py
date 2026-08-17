#!/usr/bin/env python3
"""Activation-disabled exact-Probe13 tail preparation for QYM.

This helper owns only five diagnostics which survived the four frozen Probe13
components.  It is an exact-counted static projection, not a semantic verdict.
No Lean/Lake/Git/network action is performed here.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from types import ModuleType


sys.dont_write_bytecode = True

SCHEMA = "qym-probe14-tail-prep-exact-p13-static-v1"
INPUT_SHA256 = "92e91734eb4b1d406d854a6021c815636eff6cf0aa2f4924e710249a583ebe3b"
INPUT_GIT_BLOB = "5c895f906b516366653aaf6fc459825e89045076"
INPUT_BYTES = 2_938_395
INPUT_LF = 62_112
LOG_SHA256 = "e2a675d67ef304dbbf6b3800b9e1a8c2fd1183ff16a82eb7f46b5a64fdef0826"
HEADERS_SHA256 = "74e4c1505182503c4acc9dfe6be6a4316e44b821ec7897b377597af12c07bf02"
DIAGNOSTICS_SHA256 = "0dbe572bed4860fd6f843045d3fbc9b11edab1931f63d6b5acb70bfd88d85dcb"

# Sealed after one deterministic bootstrap projection.
OUTPUT_SHA256 = "1f51eab0e820b9a4370433bb2c42554fe9cf7afbe52c03a2b940f7b31dc6fcbd"
OUTPUT_GIT_BLOB = "cbaeecbd534c0bb22bd4b92882cf1dcd36148432"
OUTPUT_BYTES = 2_938_852
OUTPUT_LF = 62_125


def sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def git_blob(raw: bytes) -> str:
    return hashlib.sha1(f"blob {len(raw)}\0".encode("ascii") + raw).hexdigest()


@dataclass(frozen=True)
class Header:
    line: int
    column: int
    message: str
    code: str | None = None


@dataclass(frozen=True)
class Rule:
    label: str
    old: str
    new: str
    headers: tuple[Header, ...]
    rationale: str
    evidence: str
    occurrences: int = 1


RULES: tuple[Rule, ...] = (
    Rule(
        "discriminant_form_nonnegative_bridge_complex_re_to_rclike_re",
        "  rw [← integral_re (𝕜 := ℂ)\n"
        "    (MeasureTheory.L2.integrable_inner u\n"
        "      (actualStageDiscriminantPotentialOperator Y u))]\n",
        "  rw [← RCLike.re_eq_complex_re]\n"
        "  rw [← integral_re (𝕜 := ℂ)\n"
        "    (MeasureTheory.L2.integrable_inner u\n"
        "      (actualStageDiscriminantPotentialOperator Y u))]\n",
        (Header(53387, 6, "Tactic `rewrite` failed: Did not find an occurrence of the pattern"),),
        "Bridge concrete Complex.re to the generic RCLike.re used by integral_re before rewriting.",
        "The diagnostic prints an RCLike.re rewrite pattern while the target keeps the concrete `.re` projection.",
    ),
    Rule(
        "inverse_eta_rank_one_energy_use_complex_conj_mul_norm_sq",
        "  exact star_mul' (actualInverseEtaAnalysisFunctional Y u)\n",
        "  simpa only [starRingEnd_apply, Complex.star_def] using\n"
        "    (Complex.conj_mul'\n"
        "      (inner ℂ (actualInverseEtaTestVector Y) u))\n",
        (Header(55655, 2, "Type mismatch"),),
        "Use the norm-square identity for conjugate-times-self, not the multiplicativity theorem for star.",
        "After the two preceding rewrites the exact goal is conj(z) * z = (norm z)^2 with z the displayed inner product.",
    ),
    Rule(
        "hamiltonian_form_hermitian_swap_inner_conj_orientation",
        "  rw [inner_conj_symm (covariantDerivative v)\n"
        "      (covariantDerivative u),\n"
        "    inner_conj_symm (groundProjection v) (groundProjection u)]\n",
        "  rw [inner_conj_symm (covariantDerivative u)\n"
        "      (covariantDerivative v),\n"
        "    inner_conj_symm (groundProjection u) (groundProjection v)]\n",
        (Header(59004, 6, "Tactic `rewrite` failed: Did not find an occurrence of the pattern"),),
        "Instantiate inner_conj_symm in the orientation actually present on the normalized right-hand side.",
        "inner_conj_symm x y rewrites star(inner y x) to inner x y; the old arguments were reversed.",
    ),
    Rule(
        "hamiltonian_form_representation_transport_idempotent_symmetries",
        "  rw [← covariantDerivative_isSymmetric (covariantDerivative u) v,\n"
        "    covariantDerivative_apply_apply]\n"
        "  rw [← groundProjection_isSymmetric (groundProjection u) v,\n"
        "    groundProjection_apply_apply]\n",
        "  have hDerivative :=\n"
        "    (covariantDerivative_isSymmetric (covariantDerivative u) v).symm\n"
        "  rw [covariantDerivative_apply_apply] at hDerivative\n"
        "  have hProjection :=\n"
        "    (groundProjection_isSymmetric (groundProjection u) v).symm\n"
        "  rw [groundProjection_apply_apply] at hProjection\n"
        "  exact congrArg₂\n"
        "    (fun a b : ℂ =>\n"
        "      a + (((1 : ℝ) / 4 : ℝ) : ℂ) * b)\n"
        "    hDerivative hProjection\n",
        (Header(59018, 6, "Tactic `rewrite` failed: Did not find an occurrence of the pattern"),),
        "Normalize the two proved symmetry equalities independently, then transport them through the displayed sum.",
        "The exact residual is A + quarter*B = C + quarter*D; symmetry plus idempotence proves A=C and B=D.",
    ),
    Rule(
        "coordinate_l2_pin_inner_product_derived_normed_space",
        "/-- A genuine compact resolvent at the explicit point `-1`. -/\n"
        "theorem coordinateFriedrichsHamiltonian_hasCompactResolventAt_negOne :\n",
        "local instance coordinateL2NormedSpaceFromInnerProduct :\n"
        "    NormedSpace ℂ CoordinateL2 :=\n"
        "  (PiLp.innerProductSpace fun _ : Fin 2 => ℂ).toNormedSpace\n"
        "\n"
        "/-- A genuine compact resolvent at the explicit point `-1`. -/\n"
        "theorem coordinateFriedrichsHamiltonian_hasCompactResolventAt_negOne :\n",
        (Header(59135, 2, "Type mismatch: After simplification, term"),),
        "Pin the local NormedSpace diamond to the exact instance carried by the generic Friedrichs theorem.",
        "The terminal diagnostic differs only between PiLp.innerProductSpace.toNormedSpace and PiLp.normedSpace; the operator and shift are identical.",
    ),
)


# All active Probe12 components plus all four frozen Probe13 components.
FOREIGN_HELPERS: tuple[tuple[str, str, str], ...] = (
    ("p12_early", "qym-probe12-early-frontier-p11-conditional/qym_probe12_early_frontier_p11_conditional.py", "35b5ccf5f04899c810ca798cbcf700230fdfc4b930d16ab5d9cf646584954215"),
    ("p12_36k42k", "qym-probe12-36k42k-p11-reanchored/qym_probe12_36k42k_p11_reanchored.py", "5bd02f57232ac30c336b3e13574b7cba4dc4b0998f159e3fdebd41ed6354a365"),
    ("p12_43k49k", "qym-probe12-43k49k-p11-conditional/qym_probe12_43k49k_p11_conditional.py", "5070ada686ac425b76403ae53210e586bda305a8a70606d6d3bc6529ff2b2523"),
    ("p12_50k53k", "qym-probe12-50k53k-p11-conditional/qym_probe12_50k53k_p11_conditional.py", "5352b37ec754a5131164e91649b54a277b5d257258bc316f653b6d218bfb63c8"),
    ("p12_52k61k", "qym-probe12-52k61k-p11-conditional/qym_probe12_52k61k_p11_conditional.py", "7066e3297bd171ec58a4547ed426a8d9a6228abf4de78bf3ad203d880ef7f795"),
    ("p13_early", "qym-probe13-early-p12-conditional/qym_probe13_early_p12_conditional.py", "5462da0d1e49fc9f5769eeaf9052515cc905cdd55740dc55c3d930992d878210"),
    ("p13_direct50", "qym-probe13-50k50599-p12-reanchored/qym_probe13_50k50599_p12_reanchored.py", "a2eacbaebd1f3fddcb865a551613ea8ebbcdf12d74869be2b61c663a0891ed50"),
    ("p13_mid", "qym-probe13-highleverage-instances/qym_probe13_highleverage_instances.py", "e29672a27f2e6421426b73350655b3bae5dca187a8ab2fe39ea023cdf19ec47e"),
    ("p13_tail", "qym-probe13-tail-p12-direct/qym_probe13_tail_p12_direct.py", "11f19ecfabdde4da519321e133fd1a2265bedc7784cdd729e8dd05fbf310cc48"),
)


def shape(raw: bytes) -> dict[str, object]:
    raw.decode("utf-8", errors="strict")
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


def trust(text: str) -> dict[str, int]:
    return {
        "sorry": len(re.findall(r"\bsorry\b", text)),
        "admit": len(re.findall(r"\badmit\b", text)),
        "native_decide": len(re.findall(r"\bnative_decide\b", text)),
        "Lean.ofReduceBool": text.count("Lean.ofReduceBool"),
        "axiom_declaration": len(re.findall(r"(?m)^\s*axiom\s+", text)),
        "unsafe_declaration": len(re.findall(r"(?m)^\s*unsafe\s+", text)),
        "maxHeartbeats_zero": len(re.findall(r"set_option\s+maxHeartbeats\s+0\b", text)),
    }


def expected_input() -> dict[str, object]:
    return {"sha256": INPUT_SHA256, "git_blob": INPUT_GIT_BLOB,
            "bytes": INPUT_BYTES, "lf": INPUT_LF, "cr": False, "nul": False,
            "bom": False, "terminal_lf": True}


def expected_output() -> dict[str, object]:
    return {"sha256": OUTPUT_SHA256, "git_blob": OUTPUT_GIT_BLOB,
            "bytes": OUTPUT_BYTES, "lf": OUTPUT_LF, "cr": False, "nul": False,
            "bom": False, "terminal_lf": True}


def unsealed() -> bool:
    return not OUTPUT_SHA256 and not OUTPUT_GIT_BLOB and OUTPUT_BYTES == 0 and OUTPUT_LF == 0


def check_shape(actual: dict[str, object], expected: dict[str, object], bootstrap: bool) -> None:
    keys = ("cr", "nul", "bom", "terminal_lf") if bootstrap else tuple(expected)
    if any(actual[key] != expected[key] for key in keys):
        raise RuntimeError(f"shape mismatch: {actual} != {expected}")


def verify_authority(log: bytes, headers: bytes, diagnostics: bytes) -> list[dict[str, object]]:
    for label, raw, expected in (
        ("log", log, LOG_SHA256),
        ("headers", headers, HEADERS_SHA256),
        ("diagnostics", diagnostics, DIAGNOSTICS_SHA256),
    ):
        if sha256(raw) != expected:
            raise RuntimeError(f"Probe13 {label} identity mismatch")
    header_lines = headers.decode("utf-8").splitlines()
    rows = [json.loads(line) for line in diagnostics.decode("utf-8").splitlines()]
    if len(header_lines) != 151 or sum(row.get("severity") == "error" for row in rows) != 151:
        raise RuntimeError("terminal Probe13 error count mismatch")
    mapped: list[dict[str, object]] = []
    for rule in RULES:
        for header in rule.headers:
            prefix = (
                f"PrimalitySheafVerification/QYM.lean:{header.line}:{header.column}: error"
                + (f"({header.code})" if header.code else "")
                + f": {header.message}"
            )
            hm = [line for line in header_lines if line.startswith(prefix)]
            dm = [row for row in rows if row.get("severity") == "error"
                  and row.get("line") == header.line and row.get("column") == header.column
                  and row.get("code") == header.code
                  and str(row.get("message", "")).startswith(header.message)]
            if len(hm) != 1 or len(dm) != 1:
                raise RuntimeError(f"diagnostic mismatch: {rule.label} {header.line}:{header.column}")
            mapped.append({"rule": rule.label, **header.__dict__})
    return mapped


def spans(text: str, needle: str) -> list[tuple[int, int]]:
    result: list[tuple[int, int]] = []
    start = 0
    while True:
        found = text.find(needle, start)
        if found < 0:
            return result
        result.append((found, found + len(needle)))
        start = found + 1


def load_foreign(name: str, relative: str, expected_sha: str) -> ModuleType:
    path = Path(__file__).resolve().parent.parent / relative
    raw = path.read_bytes()
    if sha256(raw) != expected_sha:
        raise RuntimeError(f"foreign helper drift: {name}")
    module_name = "_qym_probe14_tail_prep_" + name
    spec = importlib.util.spec_from_file_location(module_name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot import foreign helper: {name}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[module_name] = module
    spec.loader.exec_module(module)
    return module


def collision_audit(text: str, inverse: bool) -> dict[str, object]:
    own: list[tuple[int, int, str]] = []
    for rule in RULES:
        active = rule.new if inverse else rule.old
        found = spans(text, active)
        if len(found) != rule.occurrences:
            raise RuntimeError(f"active anchor count: {rule.label}: {len(found)}")
        for start, end in found:
            line = text.count("\n", 0, start) + 1
            if not 48_000 <= line <= 59_999:
                raise RuntimeError(f"scope violation: {rule.label}: line {line}")
            own.append((start, end, rule.label))
    own_sorted = sorted(own)
    own_overlaps = [(left[2], right[2]) for left, right in zip(own_sorted, own_sorted[1:])
                    if left[1] > right[0]]
    exact_equalities: list[tuple[str, str, str, str, str]] = []
    foreign_overlaps: list[tuple[str, str, str]] = []
    identities: dict[str, str] = {}
    for name, relative, expected_sha in FOREIGN_HELPERS:
        foreign_module = load_foreign(name, relative, expected_sha)
        identities[name] = expected_sha
        for foreign in foreign_module.RULES:
            for foreign_variant, anchor in (("old", foreign.old), ("new", foreign.new)):
                for own_rule in RULES:
                    for own_variant, own_anchor in (("old", own_rule.old), ("new", own_rule.new)):
                        if own_anchor == anchor:
                            exact_equalities.append(
                                (own_rule.label, own_variant, name, foreign.label, foreign_variant)
                            )
                for fstart, fend in spans(text, anchor):
                    for ostart, oend, own_label in own:
                        if max(fstart, ostart) < min(fend, oend):
                            foreign_overlaps.append(
                                (own_label, f"{name}:{foreign.label}", foreign_variant)
                            )
    if own_overlaps or exact_equalities or foreign_overlaps:
        raise RuntimeError(
            "collision0 failure: "
            f"own={own_overlaps}, equalities={exact_equalities}, foreign={foreign_overlaps}"
        )
    return {
        "foreign_helper_sha256": identities,
        "own_spans_checked": len(own),
        "own_span_overlaps": [],
        "exact_anchor_equalities": [],
        "foreign_span_overlaps": [],
        "undeclared_collisions": 0,
    }


def transform(text: str, inverse: bool = False) -> tuple[str, list[dict[str, object]]]:
    records: list[dict[str, object]] = []
    ordered = tuple(reversed(RULES)) if inverse else RULES
    for rule in ordered:
        old, new = (rule.new, rule.old) if inverse else (rule.old, rule.new)
        count = text.count(old)
        if count != rule.occurrences:
            raise RuntimeError(f"anchor count: {rule.label}: {count}")
        text = text.replace(old, new)
        records.append({
            "label": rule.label,
            "direction": "inverse" if inverse else "forward",
            "occurrences": count,
            "headers": [header.__dict__ for header in rule.headers],
            "rationale": rule.rationale,
            "evidence": rule.evidence,
        })
    return text, records


apply_rules = transform


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--probe13-log", type=Path, required=True)
    parser.add_argument("--probe13-error-headers", type=Path, required=True)
    parser.add_argument("--probe13-diagnostics", type=Path, required=True)
    parser.add_argument("--audit", type=Path, required=True)
    parser.add_argument("--mode", choices=("forward", "inverse"), default="forward")
    parser.add_argument("--bootstrap-seal", action="store_true")
    args = parser.parse_args()
    inverse = args.mode == "inverse"
    if args.bootstrap_seal != unsealed():
        raise RuntimeError("bootstrap/seal state mismatch")
    source = args.input.read_bytes()
    source_shape = shape(source)
    check_shape(source_shape, expected_output() if inverse else expected_input(), args.bootstrap_seal)
    mapped = verify_authority(
        args.probe13_log.read_bytes(),
        args.probe13_error_headers.read_bytes(),
        args.probe13_diagnostics.read_bytes(),
    )
    text = source.decode("utf-8", errors="strict")
    collisions = collision_audit(text, inverse)
    before = trust(text)
    result_text, records = transform(text, inverse)
    result = result_text.encode("utf-8")
    result_shape = shape(result)
    check_shape(result_shape, expected_input() if inverse else expected_output(), args.bootstrap_seal)
    after = trust(result_text)
    if before != after or any(after.values()):
        raise RuntimeError(f"trust0 failure: {before} -> {after}")
    restored, _ = transform(result_text, not inverse)
    if restored.encode("utf-8") != source:
        raise RuntimeError("opposite transform failed byte-exact restoration")
    if args.output.exists() or args.audit.exists():
        raise RuntimeError("refusing to overwrite output or audit")
    record = {
        "schema": SCHEMA,
        "status": "STATIC_PASS_EXACT_TERMINAL_PROBE13_NOT_LEAN_EXECUTED",
        "activation": False,
        "promotion": False,
        "mode": args.mode,
        "authority": {
            "candidate_sha256": INPUT_SHA256,
            "candidate_git_blob": INPUT_GIT_BLOB,
            "log_sha256": LOG_SHA256,
            "headers_sha256": HEADERS_SHA256,
            "diagnostics_sha256": DIAGNOSTICS_SHA256,
            "errors": 151,
            "warnings": 341,
            "panic": 0,
            "exit": 1,
        },
        "scope": {
            "candidate_lines": [48_000, 59_999],
            "probe13_owned_diagnostics_excluded": True,
            "structural_inverse_eta_bridge_excluded": True,
            "reanchor_after_probe13_terminal_required": False,
            "excluded_uncertain_roots": [
                50315, 50330, 50333, 50336, 50342, 50365, 50428, 50437,
                50449, 50450, 50456, 50457, 50459, 50462, 50464, 50466,
                50473, 50475, 50483, 50499, 50553, 50557, 50613, 50682,
                50686, 50720, 51389, 51404, 51410, 51418, 51423, 51488,
                51571, 51605, 51608, 51611, 51633, 51652, 51702, 52128,
            ],
            "excluded_active_probe12_span": [51183],
        },
        "source": source_shape,
        "result": result_shape,
        "repair_families": len(RULES),
        "repair_occurrences": sum(item["occurrences"] for item in records),
        "direct_diagnostics": len(mapped),
        "selected_exact_probe13_lines": sorted(
            {header.line for rule in RULES for header in rule.headers}
        ),
        "diagnostic_map": mapped,
        "rules": records,
        "collision_audit": collisions,
        "inverse_byte_equal": True,
        "trust": after,
        "execution": {
            "lean": False,
            "lake": False,
            "git": False,
            "network": False,
            "remote": False,
            "repository_source_mutation": False,
        },
    }
    args.output.write_bytes(result)
    args.audit.write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(json.dumps(record, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
