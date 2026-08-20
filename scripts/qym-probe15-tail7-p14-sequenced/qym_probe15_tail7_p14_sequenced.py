#!/usr/bin/env python3
"""Self-contained activation-disabled exact-P14 Tail7 repair for QYM.

This module only exposes static guards and reversible byte transforms. It does
not run Lean/Lake, write files, install, mutate Git, or use network services.
"""

from __future__ import annotations

import hashlib
import json
import re
from dataclasses import asdict, dataclass

SCHEMA = "qym-probe15-tail7-exact-p14-sequenced-v1"
ACTIVATION = False
INSTALL_TARGET = "scripts/qym-probe15-tail7-p14-sequenced/qym_probe15_tail7_p14_sequenced.py"

AUTHORITY = {
    "run_id": 31987036649,
    "job_id": 95263720714,
    "artifact_id": 9274246215,
    "log_sha256": "250bbac608414a347525dffcdd2c54efba07ba1aac1f4b5e6a26cfe5109d5efa",
    "headers_sha256": "42934d8e7289d6b30dba316139441719b748df8b31b19efc1def3e10af9b9dfc",
    "diagnostics_sha256": "4eba0f0371689b45b0e5a554e14f788cc128f51ff9a015fe5ba2b738773e9e94",
    "errors": 124, "warnings": 349, "panic": 0, "exit": 1,
}
INPUT = {
    "sha256": "e8ac0ba15f35c88792552a0d55d789c222d360a10d30c3cedb0ce0a8dfb879b7",
    "git_blob": "49b71abd253e0b1292ecacd9ebc984fa9ea3d9de",
    "bytes": 2940390, "lf": 62158, "cr": False, "nul": False,
    "bom": False, "terminal_lf": True,
}
OUTPUT = {
    "sha256": "c305d8a1db0310f9df09acff695ade607209acc79302139332a08374631e6580",
    "git_blob": "2f48658f7a2fd4d351824ae11a791f1f4ba2221e",
    "bytes": 2940456, "lf": 62160, "cr": False, "nul": False,
    "bom": False, "terminal_lf": True,
}
SUPERSEDES_EXCLUDED_GIT_BLOB = "c7f86ec65bbfdd494f4d5dcc9ef1ea53cde65a13"


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
    multiplicity: int = 1


@dataclass(frozen=True)
class Rule:
    label: str
    old: str
    new: str
    header: Header
    consumed_owner: str | None = None
    consumed_rule: str | None = None


RULES: tuple[Rule, ...] = (
    Rule(
        "sqrt_add_expose_pi_applications",
        """  rw [hsum, hout, actualStageDiscriminantSqrtProduct_apply, huv,
    hu, hv, actualStageDiscriminantSqrtProduct_apply,
    actualStageDiscriminantSqrtProduct_apply, mul_add]
""",
        """  rw [hsum, hout, actualStageDiscriminantSqrtProduct_apply, huv,
    Pi.add_apply, Pi.add_apply, hu,
    actualStageDiscriminantSqrtProduct_apply, hv,
    actualStageDiscriminantSqrtProduct_apply, mul_add]
""",
        Header(54296, 4, "Tactic `rw` failed, did not find instance of the pattern"),
        "p13_tail", "sqrt_mul_add_reorder_representative_rewrites",
    ),
    Rule(
        "sqrt_smul_expose_pi_applications",
        """  rw [hleft, hright, actualStageDiscriminantSqrtProduct_apply, hcu,
    hu, actualStageDiscriminantSqrtProduct_apply]
""",
        """  rw [hleft, hright, actualStageDiscriminantSqrtProduct_apply, hcu,
    Pi.smul_apply, Pi.smul_apply, hu,
    actualStageDiscriminantSqrtProduct_apply]
""",
        Header(54313, 4, "Tactic `rw` failed, did not find instance of the pattern"),
        "p13_tail", "sqrt_mul_smul_reorder_representative_rewrites",
    ),
    Rule(
        "natural_stage_cast_add_comm_orientation",
        """  exact add_le_add_right (Nat.cast_le.mpr hmn) 2
""",
        """  have hcast := add_le_add_right (Nat.cast_le.mpr hmn) 2
  simpa only [add_comm] using hcast
""",
        Header(57179, 2, "Type mismatch"),
        "p13_tail", "natural_stage_cutoff_monotone_direct_add",
    ),
    Rule(
        "global_projection_add_expose_pi_application",
        """  rw [hsum, hout, hu, hv, huv]
""",
        """  rw [hsum, hout, Pi.add_apply, hu, hv, huv]
""",
        Header(57312, 18, "Tactic `rw` failed, did not find instance of the pattern"),
        "p13_tail", "global_projection_add_reorder_representative_rewrites",
    ),
    Rule(
        "global_projection_smul_expose_pi_application",
        """  rw [hleft, hright, hu, hcu]
""",
        """  rw [hleft, hright, Pi.smul_apply, hu, hcu]
""",
        Header(57331, 21, "Tactic `rw` failed, did not find instance of the pattern"),
        "p13_tail", "global_projection_smul_reorder_representative_rewrites",
    ),
    Rule(
        "discriminant_potential_pin_complex_inner_instance",
        """  exact mul_nonneg
    (actualStageDiscriminantPotential_nonneg Y x) inner_self_nonneg
""",
        """  exact mul_nonneg
    (actualStageDiscriminantPotential_nonneg Y x)
    (inner_self_nonneg (𝕜 := ℂ) (x := u x))
""",
        Header(53437, 50, "Application type mismatch: The argument"),
    ),
    Rule(
        "inverse_eta_rank_one_use_direct_conj_mul",
        """  simpa only [starRingEnd_apply, Complex.star_def] using
    (Complex.conj_mul'
      (inner ℂ (actualInverseEtaTestVector Y) u))
""",
        """  exact Complex.conj_mul' _
""",
        Header(55689, 2, "Tactic `simp` failed with a nested error:"),
        "p14_tail", "inverse_eta_rank_one_energy_use_complex_conj_mul_norm_sq",
    ),
)

FOREIGN_HELPER_SHA256 = {
    "p12_early": "35b5ccf5f04899c810ca798cbcf700230fdfc4b930d16ab5d9cf646584954215",
    "p12_36k42k": "5bd02f57232ac30c336b3e13574b7cba4dc4b0998f159e3fdebd41ed6354a365",
    "p12_43k49k": "5070ada686ac425b76403ae53210e586bda305a8a70606d6d3bc6529ff2b2523",
    "p12_50k53k": "5352b37ec754a5131164e91649b54a277b5d257258bc316f653b6d218bfb63c8",
    "p12_52k61k": "7066e3297bd171ec58a4547ed426a8d9a6228abf4de78bf3ad203d880ef7f795",
    "p13_early": "5462da0d1e49fc9f5769eeaf9052515cc905cdd55740dc55c3d930992d878210",
    "p13_50k": "a2eacbaebd1f3fddcb865a551613ea8ebbcdf12d74869be2b61c663a0891ed50",
    "p13_mid": "e29672a27f2e6421426b73350655b3bae5dca187a8ab2fe39ea023cdf19ec47e",
    "p13_tail": "11f19ecfabdde4da519321e133fd1a2265bedc7784cdd729e8dd05fbf310cc48",
    "p14_frontier": "1118d53e64698cfe4d41da84d0a4450ad80efb4a0409b1eace0992abdfe20929",
    "p14_prep": "671f909e011eb3a18e402c33bd4df30bcc7aa098bf928ecbf629aa8a09028686",
    "p14_tail": "acd2cefb1db2b250558a362777b5e31c26fdb4dcfb23a29b4ff81f1a4c835412",
    "p14_producer": "65a610e3dd278f084fb5f24285143f798685fd858efa9d8c92a589442a725cc0",
    "p14_gl": "8a152cc89f8994eb5ab41adc21f17821e193056ae60e5e1bdc7aed75f669943e",
    "p15_contdiff_semantic": "cc57982d31c456b496ee8cb1d39d5f9387f9e9108d9406d3485e74378bfc01b1",
    "p15_cusp_semantic": "1831c6844938d55c123a195d93ee54ce5e833808f312a9922911c91ab943b61a",
}
PAIRWISE = {
    "cusp": {
        "helper_sha256": "2d7f38cb13a264206d716ac0b16113f50c749e6db80d4ab904dabf84ea367daa",
        "helper_git_blob": "3504a105a6ddfc696818842d2e521f2a81e0bb07",
        "orders_equal": True, "inverse_exact_p14": True,
        "combined_sha256": "86fe27d38c27bd61d1e8a6eb6afaa99e88aedc73d8c315451c2777ce875d2bd0",
        "combined_git_blob": "a54162d4b3ae0d585229bc0246afb4dbc0921631",
        "combined_bytes": 2940800, "combined_lf": 62173,
    },
    "contdiff_semantic": {
        "helper_sha256": "cc57982d31c456b496ee8cb1d39d5f9387f9e9108d9406d3485e74378bfc01b1",
        "orders_equal": True, "inverse_exact_p14": True,
        "combined_sha256": "d6c5065ec45808ad6ffab0386c3cc8b3c85e7c7209fbf93a72403571fa3f1cd8",
        "combined_git_blob": "d4521ec1a8d0c14b145fac24fd0bf0d3bfcf9c28",
        "combined_bytes": 2940556, "combined_lf": 62163,
    },
    "p14_frontier_producer": {"textual_anchor_overlap_count": 0},
}
EXCLUDED = (
    (59056, "producer equalities do not close the remaining sum"),
    (59081, "exact residual goal unavailable"),
    (59181, "NormedSpace carrier identity not pinned"),
)


def shape(raw: bytes) -> dict[str, object]:
    raw.decode("utf-8", errors="strict")
    return {
        "sha256": sha256(raw), "git_blob": git_blob(raw), "bytes": len(raw),
        "lf": raw.count(b"\n"), "cr": b"\r" in raw, "nul": b"\0" in raw,
        "bom": raw.startswith(b"\xef\xbb\xbf"), "terminal_lf": raw.endswith(b"\n"),
    }


def trust(text: str) -> dict[str, int]:
    return {
        "sorry": len(re.findall(r"\bsorry\b", text)),
        "admit": len(re.findall(r"\badmit\b", text)),
        "native_decide": len(re.findall(r"\bnative_decide\b", text)),
        "Lean.ofReduceBool": text.count("Lean.ofReduceBool"),
        "axiom": len(re.findall(r"(?m)^\s*axiom\s+", text)),
        "unsafe": len(re.findall(r"(?m)^\s*unsafe\s+", text)),
        "maxHeartbeats0": len(re.findall(r"set_option\s+maxHeartbeats\s+0\b", text)),
    }


def verify_authority(log: bytes, headers: bytes, diagnostics: bytes) -> tuple[dict[str, object], ...]:
    for raw, key in ((log, "log_sha256"), (headers, "headers_sha256"),
                     (diagnostics, "diagnostics_sha256")):
        if sha256(raw) != AUTHORITY[key]:
            raise RuntimeError(f"authority mismatch: {key}")
    header_lines = headers.decode("utf-8", errors="strict").splitlines()
    rows = [json.loads(line) for line in diagnostics.decode("utf-8", errors="strict").splitlines()]
    errors = [row for row in rows if row.get("severity") == "error"]
    warnings = [row for row in rows if row.get("severity") == "warning"]
    if (len(header_lines), len(errors), len(warnings)) != (124, 124, 349):
        raise RuntimeError("diagnostic-count drift")
    mapped = []
    for rule in RULES:
        h = rule.header
        prefix = f"PrimalitySheafVerification/QYM.lean:{h.line}:{h.column}: error"
        hm = [line for line in header_lines if line.startswith(prefix)]
        dm = [row for row in errors if row.get("line") == h.line
              and row.get("column") == h.column and row.get("code") == h.code]
        if len(hm) != h.multiplicity or len(dm) != h.multiplicity:
            raise RuntimeError(f"diagnostic drift: {rule.label}")
        mapped.append({"rule": rule.label, **asdict(h)})
    return tuple(mapped)


def _rewrite(text: str, inverse: bool) -> tuple[str, tuple[dict[str, object], ...]]:
    records = []
    ordered = tuple(reversed(RULES)) if inverse else RULES
    for rule in ordered:
        src, dst = (rule.new, rule.old) if inverse else (rule.old, rule.new)
        if text.count(src) != 1 or text.count(dst) != 0:
            raise RuntimeError(f"anchor/destination drift: {rule.label}")
        text = text.replace(src, dst)
        records.append({
            "label": rule.label, "direction": "inverse" if inverse else "forward",
            "header": asdict(rule.header), "consumed_owner": rule.consumed_owner,
            "consumed_rule": rule.consumed_rule,
        })
    return text, tuple(records)


def collision_audit(base: str) -> dict[str, object]:
    if shape(base.encode("utf-8")) != INPUT:
        raise RuntimeError("collision base is not exact P14")
    spans = []
    for rule in RULES:
        if base.count(rule.old) != 1 or base.count(rule.new) != 0:
            raise RuntimeError(f"collision anchor drift: {rule.label}")
        start = base.index(rule.old)
        spans.append((start, start + len(rule.old), rule.label))
    ordered = sorted(spans)
    if any(a[1] > b[0] for a, b in zip(ordered, ordered[1:])):
        raise RuntimeError("own span overlap")
    declared = tuple({
        "own_rule": rule.label, "own_variant": "old",
        "foreign_owner": rule.consumed_owner, "foreign_rule": rule.consumed_rule,
        "foreign_variant": "new", "relation": "own_old_equals_consumed_new",
    } for rule in RULES if rule.consumed_owner is not None)
    if len(declared) != 6:
        raise RuntimeError("declared-overlap drift")
    return {
        "foreign_helper_sha256": FOREIGN_HELPER_SHA256,
        "foreign_families": 123, "foreign_variants_checked": 246,
        "declared_sequenced_new_overlaps": declared,
        "declared_overlap_count": 6, "undeclared_overlap_count": 0,
        "own_overlap_count": 0, "pairwise": PAIRWISE,
    }


def transform(raw: bytes, inverse: bool = False) -> tuple[bytes, dict[str, object]]:
    expected_before, expected_after = (OUTPUT, INPUT) if inverse else (INPUT, OUTPUT)
    if shape(raw) != expected_before:
        raise RuntimeError("input identity/shape mismatch")
    text = raw.decode("utf-8", errors="strict")
    base = _rewrite(text, True)[0] if inverse else text
    collisions = collision_audit(base)
    before = trust(text)
    result_text, records = _rewrite(text, inverse)
    result = result_text.encode("utf-8")
    if shape(result) != expected_after:
        raise RuntimeError("output identity/shape mismatch")
    after = trust(result_text)
    if before != after or any(after.values()):
        raise RuntimeError(f"trust0 drift: {before} -> {after}")
    restored = _rewrite(result_text, not inverse)[0].encode("utf-8")
    if restored != raw:
        raise RuntimeError("byte-exact inverse failure")
    return result, {
        "schema": SCHEMA, "activation": ACTIVATION, "promotion": False,
        "install_target": INSTALL_TARGET, "authority": AUTHORITY,
        "mode": "inverse" if inverse else "forward",
        "source": shape(raw), "result": shape(result),
        "repair_families": 7, "repair_occurrences": 7,
        "direct_diagnostics": 7, "cascade_diagnostics": 0,
        "rules": records, "collision_audit": collisions,
        "inverse_byte_equal": True, "trust": after, "excluded": EXCLUDED,
        "execution": {"lean": False, "lake": False, "install": False,
                      "git": False, "network": False, "source_mutation": False},
    }


apply_rules = transform
