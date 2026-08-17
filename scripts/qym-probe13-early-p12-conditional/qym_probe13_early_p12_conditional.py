#!/usr/bin/env python3
"""Exact-P12, activation-disabled repairs for the five surviving early roots.

This helper is byte-locked to terminal Probe12.  It performs five exact-counted
downstream refinements, proves byte-exact inversion, preserves trust0, and
statically verifies the two frozen Probe12 owner helpers without importing or
executing them.  It never invokes Lean, Lake, Git, or the network and never
mutates a repository source.
"""

from __future__ import annotations

import argparse
import ast
import hashlib
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path


sys.dont_write_bytecode = True

SCHEMA = "qym-probe13-early-p12-conditional-v1"
INPUT_SHA256 = "4a123f69912bd7ce2ab070433f8cad0ecc284652a9cbab634def1936e9037212"
INPUT_GIT_BLOB = "76dd931638b9a6ad50ee764c65cd14489e8be310"
INPUT_BYTES = 2_936_558
INPUT_LF = 62_068
LOG_SHA256 = "62ce7c1b4ec23a23d690c64d49e45901faec66ff751d86e314e669b8c876c398"
HEADERS_SHA256 = "0cebf8d7bbcb923165a13f68f2afbbef1843bb26d77e072252c570b8e77b0dd9"
DIAGNOSTICS_SHA256 = "16b69f25e53f28d028cbefca21d5401e25dbfaa2847bdfdc8f7532034690ca23"

# Sealed after one deterministic --bootstrap-seal projection.
OUTPUT_SHA256 = "96bec0509b3aa2d598450f15c9f691a99f26f82b4674fb3bb1e0e5ff04e6dc56"
OUTPUT_GIT_BLOB = "b8914964ee5414841fae0c13d88e7fac7e765d56"
OUTPUT_BYTES = 2_936_544
OUTPUT_LF = 62_069

OWNER_HELPERS: tuple[tuple[str, str, str], ...] = (
    (
        "probe12_early",
        "qym-probe12-early-frontier-p11-conditional/qym_probe12_early_frontier_p11_conditional.py",
        "35b5ccf5f04899c810ca798cbcf700230fdfc4b930d16ab5d9cf646584954215",
    ),
    (
        "probe12_36k42k",
        "qym-probe12-36k42k-p11-reanchored/qym_probe12_36k42k_p11_reanchored.py",
        "5bd02f57232ac30c336b3e13574b7cba4dc4b0998f159e3fdebd41ed6354a365",
    ),
)

DECLARED_REFINEMENTS = {
    "raw_differential_deck_use_mfderiv_comp_apply":
        ("probe12_early", "raw_differential_deck_split_eq_trans"),
    "raw_differential_smul_expose_pointwise_mul":
        ("probe12_early", "raw_differential_smul_pin_eq_carrier"),
    "safe_matter_norm_use_norm_smul_equality":
        ("probe12_early", "safe_matter_norm_smul_pin_both_arguments"),
    "safe_matter_inner_pin_field_and_vector":
        ("probe12_early", "safe_matter_inner_self_pin_complex_real_goal"),
    "smooth_compact_covariance_allow_action_simp":
        ("probe12_36k42k", "smooth_compact_covariance_bridge_gamma_two_action"),
}


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
    header: Header
    rationale: str
    occurrences: int = 1


RULES: tuple[Rule, ...] = (
    Rule(
        "raw_differential_deck_use_mfderiv_comp_apply",
        """  have hchain :
      (rawDifferential g (γ • τ)).comp (manifoldDeckDerivative γ τ) =
        (mvfderiv 𝓘(ℂ) (g.1 ∘ manifoldDeckMap γ) τ :
          ScalarOneFormValue) := by
    symm
    simpa only [rawDifferential, manifoldDeckDerivative, manifoldDeckMap]
      using mvfderiv_comp τ hgAt hdeckAt
""",
        """  have hchain :
      (rawDifferential g (γ • τ)).comp (manifoldDeckDerivative γ τ) =
        (mvfderiv 𝓘(ℂ) (g.1 ∘ manifoldDeckMap γ) τ :
          ScalarOneFormValue) := by
    symm
    apply ContinuousLinearMap.ext
    intro v
    simpa only [rawDifferential, manifoldDeckDerivative, manifoldDeckMap,
      mvfderiv, Function.comp_apply, ContinuousLinearMap.comp_apply] using
      congrArg
        (NormedSpace.fromTangentSpace (g.1 (γ • τ)))
        (mfderiv_comp_apply τ hgAt hdeckAt v)
""",
        Header(28362, 12, "Unknown identifier `mvfderiv_comp`", "lean.unknownIdentifier"),
        "Use the existing mfderiv chain rule pointwise and transport it through the exact value-space tangent equivalence.",
    ),
    Rule(
        "raw_differential_smul_expose_pointwise_mul",
        """  change @Eq ScalarOneFormValue _ _
  simpa [rawDifferential, mvfderiv_const] using
    (mvfderiv_smul hc hg)
""",
        """  change mvfderiv 𝓘(ℂ) ((fun _ : H => c) * g.1) τ =
    c • mvfderiv 𝓘(ℂ) g.1 τ
  simpa [mvfderiv_const] using
    (mvfderiv_smul hc hg)
""",
        Header(28390, 2, "Type mismatch: After simplification, term"),
        "Expose the pointwise complex multiplication produced by mvfderiv_smul instead of relying on subtype scalar-action coercion.",
    ),
    Rule(
        "safe_matter_norm_use_norm_smul_equality",
        """theorem safeMatterPotential_norm_le_coefficient
    (sector : QSector) (Y : ℝ) :
    ‖safeMatterPotential sector Y‖ ≤ sectorPotentialCoefficient sector := by
  unfold safeMatterPotential
  calc
    ‖(sectorPotentialCoefficient sector : ℂ) • deltaMatterPotential Y‖
        ≤ ‖(sectorPotentialCoefficient sector : ℂ)‖ *
            ‖deltaMatterPotential Y‖ :=
      norm_smul_le
        (sectorPotentialCoefficient sector : ℂ)
        (deltaMatterPotential Y :
          EtaMatterCarrier Y →L[ℂ] EtaMatterCarrier Y)
    _ ≤ ‖(sectorPotentialCoefficient sector : ℂ)‖ * 1 :=
      mul_le_mul_of_nonneg_left (deltaMatterPotential_norm_le_one Y)
        (norm_nonneg _)
    _ = sectorPotentialCoefficient sector := by
      simp [abs_of_nonneg (sectorPotentialCoefficient_nonneg sector)]
""",
        """theorem safeMatterPotential_norm_le_coefficient
    (sector : QSector) (Y : ℝ) :
    ‖safeMatterPotential sector Y‖ ≤ sectorPotentialCoefficient sector := by
  rw [safeMatterPotential, norm_smul]
  calc
    ‖(sectorPotentialCoefficient sector : ℂ)‖ *
          ‖deltaMatterPotential Y‖
        ≤ ‖(sectorPotentialCoefficient sector : ℂ)‖ * 1 :=
      mul_le_mul_of_nonneg_left (deltaMatterPotential_norm_le_one Y)
        (norm_nonneg _)
    _ = sectorPotentialCoefficient sector := by
      simp [abs_of_nonneg (sectorPotentialCoefficient_nonneg sector)]
""",
        Header(32094, 6, "failed to synthesize instance of type class", "lean.synthInstanceFailed"),
        "Rewrite by the exact norm_smul equality, avoiding the weaker theorem's unresolved IsBoundedSMul parameter.",
    ),
    Rule(
        "safe_matter_inner_pin_field_and_vector",
        """  exact mul_nonneg (sectorPotentialCoefficient_nonneg sector)
    (inner_self_nonneg : 0 ≤ (⟪u, u⟫_ℂ).re)
""",
        """  exact mul_nonneg (sectorPotentialCoefficient_nonneg sector)
    (inner_self_nonneg (𝕜 := ℂ) (x := u))
""",
        Header(32132, 4, "Type mismatch"),
        "Supply both explicit parameters of inner_self_nonneg rather than an expected-type ascription that leaves its instances metavariables.",
    ),
    Rule(
        "smooth_compact_covariance_allow_action_simp",
        """  simpa only [Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.gammaTwoToSL2Real] using hCov
""",
        """  simpa [Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.gammaTwoToSL2Real] using hCov
""",
        Header(34187, 2, "Type mismatch: After simplification, term"),
        "Permit the standard action/coercion simp lemmas required by the already-proved GammaTwo bridge.",
    ),
)

EXPECTED_RANGE_ROOTS = {
    (28362, 12), (28390, 2), (32094, 6), (32132, 4), (34187, 2),
}


def sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def git_blob(raw: bytes) -> str:
    return hashlib.sha1(f"blob {len(raw)}\0".encode() + raw).hexdigest()


def shape(raw: bytes) -> dict[str, object]:
    raw.decode("utf-8", errors="strict")
    return {
        "sha256": sha256(raw), "git_blob": git_blob(raw), "bytes": len(raw),
        "lf": raw.count(b"\n"), "cr": b"\r" in raw, "nul": b"\0" in raw,
        "bom": raw.startswith(b"\xef\xbb\xbf"), "terminal_lf": raw.endswith(b"\n"),
    }


def expected_input() -> dict[str, object]:
    return {"sha256": INPUT_SHA256, "git_blob": INPUT_GIT_BLOB,
            "bytes": INPUT_BYTES, "lf": INPUT_LF, "cr": False, "nul": False,
            "bom": False, "terminal_lf": True}


def expected_output() -> dict[str, object]:
    return {"sha256": OUTPUT_SHA256, "git_blob": OUTPUT_GIT_BLOB,
            "bytes": OUTPUT_BYTES, "lf": OUTPUT_LF, "cr": False, "nul": False,
            "bom": False, "terminal_lf": True}


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


def check_shape(actual: dict[str, object], expected: dict[str, object], bootstrap: bool = False) -> None:
    keys = ("cr", "nul", "bom", "terminal_lf") if bootstrap else tuple(expected)
    if any(actual[k] != expected[k] for k in keys):
        raise RuntimeError(f"shape mismatch: {actual} != {expected}")


def verify_authority(log: bytes, headers: bytes, diagnostics: bytes) -> list[dict[str, object]]:
    for label, raw, expected in (("log", log, LOG_SHA256),
                                 ("headers", headers, HEADERS_SHA256),
                                 ("diagnostics", diagnostics, DIAGNOSTICS_SHA256)):
        if sha256(raw) != expected:
            raise RuntimeError(f"Probe12 {label} identity mismatch")
    rows = [json.loads(line) for line in diagnostics.decode().splitlines() if line]
    if sum(r.get("severity") == "error" for r in rows) != 183:
        raise RuntimeError("Probe12 error count mismatch")
    if sum(r.get("severity") == "warning" for r in rows) != 350:
        raise RuntimeError("Probe12 warning count mismatch")
    range_rows = [r for r in rows if r.get("severity") == "error"
                  and 28_000 <= int(r.get("line", -1)) < 36_000]
    keys = {(int(r["line"]), int(r["column"])) for r in range_rows}
    if keys != EXPECTED_RANGE_ROOTS or len(range_rows) != 5:
        raise RuntimeError(f"early authority mismatch: {sorted(keys)}")
    mapped = []
    for rule in RULES:
        h = rule.header
        matches = [r for r in range_rows if r.get("line") == h.line
                   and r.get("column") == h.column and r.get("code") == h.code
                   and str(r.get("message", "")).startswith(h.message)]
        if len(matches) != 1:
            raise RuntimeError(f"{rule.label}: diagnostic mapping mismatch")
        mapped.append({"owner": rule.label, **h.__dict__})
    return mapped


def literal(node: ast.AST) -> str:
    value = ast.literal_eval(node)
    if not isinstance(value, str):
        raise RuntimeError("owner helper string is not literal")
    return value


def owner_rules(path: Path) -> dict[str, tuple[str, str]]:
    tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
    for node in tree.body:
        if isinstance(node, ast.AnnAssign) and isinstance(node.target, ast.Name) \
                and node.target.id == "RULES" and isinstance(node.value, (ast.Tuple, ast.List)):
            return {literal(e.args[0]): (literal(e.args[1]), literal(e.args[2]))
                    for e in node.value.elts if isinstance(e, ast.Call)}
    raise RuntimeError(f"static owner RULES not found: {path}")


def audit_collisions(text: str, inverse: bool) -> dict[str, object]:
    active = [(r.label, r.new if inverse else r.old) for r in RULES]
    spans = []
    for label, anchor in active:
        starts = [m.start() for m in re.finditer(re.escape(anchor), text)]
        if len(starts) != 1:
            raise RuntimeError(f"{label}: active count {len(starts)}")
        start = starts[0]
        line = text.count("\n", 0, start) + 1
        if not 28_000 <= line < 36_000:
            raise RuntimeError(f"{label}: scope violation {line}")
        spans.append((start, start + len(anchor), label))
    overlaps = [(a[2], b[2]) for a, b in zip(sorted(spans), sorted(spans)[1:]) if a[1] > b[0]]
    if overlaps:
        raise RuntimeError(f"own overlap: {overlaps}")

    base = Path(__file__).resolve().parent.parent
    owners: dict[str, dict[str, object]] = {}
    owner_map: dict[tuple[str, str], tuple[str, str]] = {}
    for name, rel, expected_sha in OWNER_HELPERS:
        path = base / rel
        raw = path.read_bytes()
        if sha256(raw) != expected_sha:
            raise RuntimeError(f"owner identity mismatch: {name}")
        rules = owner_rules(path)
        owners[name] = {"sha256": expected_sha, "rules": len(rules), "executed": False}
        for label, pair in rules.items():
            owner_map[(name, label)] = pair
    relationships = []
    for rule in RULES:
        owner_key = DECLARED_REFINEMENTS[rule.label]
        _, owner_new = owner_map[owner_key]
        if rule.old in owner_new:
            relationship = "probe13_old_contained_in_active_probe12_new"
        elif owner_new in rule.old:
            relationship = "active_probe12_new_contained_in_probe13_old"
        else:
            raise RuntimeError(f"{rule.label}: not an exact active-owner refinement")
        relationships.append({"rule": rule.label, "owner": ":".join(owner_key),
                              "relationship": relationship})
    return {"pass": True, "own_overlap_count": 0, "undeclared_collision_count": 0,
            "declared_refinements": relationships, "owners": owners,
            "owner_imported": False, "owner_executed": False}


def apply_rules(text: str, inverse: bool = False) -> tuple[str, list[dict[str, object]]]:
    audit = []
    ordered = tuple(reversed(RULES)) if inverse else RULES
    for rule in ordered:
        old, new = (rule.new, rule.old) if inverse else (rule.old, rule.new)
        count = text.count(old)
        if count != rule.occurrences:
            raise RuntimeError(f"{rule.label}: exact anchor count {count}")
        text = text.replace(old, new)
        audit.append({"label": rule.label, "direction": "inverse" if inverse else "forward",
                      "occurrences": count, "header": rule.header.__dict__,
                      "rationale": rule.rationale})
    return text, audit


transform = apply_rules


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--probe12-log", type=Path, required=True)
    parser.add_argument("--probe12-error-headers", type=Path, required=True)
    parser.add_argument("--probe12-diagnostics", type=Path, required=True)
    parser.add_argument("--audit", type=Path, required=True)
    parser.add_argument("--mode", choices=("forward", "inverse"), default="forward")
    parser.add_argument("--bootstrap-seal", action="store_true")
    args = parser.parse_args()
    inverse = args.mode == "inverse"
    unsealed = not OUTPUT_SHA256 and not OUTPUT_GIT_BLOB and OUTPUT_BYTES == OUTPUT_LF == 0
    if args.bootstrap_seal != unsealed:
        raise RuntimeError("bootstrap/seal state mismatch")
    out_resolved = args.output.resolve()
    audit_resolved = args.audit.resolve()
    if out_resolved == audit_resolved or args.output.exists() or args.audit.exists():
        raise RuntimeError("output/audit must be fresh and distinct")
    if not args.output.parent.is_dir() or not args.audit.parent.is_dir():
        raise RuntimeError("output/audit parent missing")

    source = args.input.read_bytes()
    source_shape = shape(source)
    check_shape(source_shape, expected_output() if inverse else expected_input(),
                bootstrap=args.bootstrap_seal and inverse)
    mapped = verify_authority(args.probe12_log.read_bytes(),
                              args.probe12_error_headers.read_bytes(),
                              args.probe12_diagnostics.read_bytes())
    source_text = source.decode("utf-8")
    collision = audit_collisions(source_text, inverse)
    before_trust = trust(source_text)
    result_text, rules = apply_rules(source_text, inverse)
    result = result_text.encode()
    result_shape = shape(result)
    check_shape(result_shape, expected_input() if inverse else expected_output(),
                bootstrap=args.bootstrap_seal and not inverse)
    after_trust = trust(result_text)
    if before_trust != after_trust or any(after_trust.values()):
        raise RuntimeError(f"trust0 failure: {before_trust} -> {after_trust}")
    restored, _ = apply_rules(result_text, not inverse)
    if restored.encode() != source:
        raise RuntimeError("opposite transform did not restore exact bytes")

    record = {
        "schema": SCHEMA, "status": "STATIC_PASS_EXACT_P12_NOT_LEAN_EXECUTED",
        "activation": False, "promotion": False, "mode": args.mode,
        "authority": {"run_id": 31980288161, "candidate_sha256": INPUT_SHA256,
                      "candidate_git_blob": INPUT_GIT_BLOB, "log_sha256": LOG_SHA256,
                      "headers_sha256": HEADERS_SHA256, "diagnostics_sha256": DIAGNOSTICS_SHA256,
                      "errors": 183, "warnings": 350, "panic": 0, "exit": 1},
        "scope": {"candidate_lines": [28_000, 35_999], "range_errors": 5,
                  "selected_direct_roots": 5, "cascade_diagnostics_selected": False,
                  "closed_probe12_roots_selected": False},
        "source": source_shape, "result": result_shape,
        "repair_families": len(RULES), "repair_occurrences": sum(x["occurrences"] for x in rules),
        "selected_diagnostics": mapped, "rules": rules, "collision_audit": collision,
        "inverse_byte_equal": True, "trust": after_trust,
        "execution": {"lean": False, "lake": False, "git": False, "network": False,
                      "remote": False, "repository_source_mutation": False,
                      "owner_import": False, "owner_execution": False},
    }
    args.output.write_bytes(result)
    args.audit.write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(json.dumps(record, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
