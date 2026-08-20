#!/usr/bin/env python3
"""Exact-P11 conditional repairs for the earliest surviving QYM roots.

The terminal Probe11 authority has thirteen errors from lines 28,000 through
36,000.  Two of those errors are refinements owned by the already-sealed
Probe12 P10-midlate helper, so this component excludes them.  The remaining
eleven current diagnostics are independent direct roots covered by eight
exact-counted rules below.

The transformer is byte-locked to exact terminal Probe11, activation-disabled,
trust0, collision-audited against every existing Probe12 transformer without
importing or executing those helpers, and byte-for-byte reversible.  It never
invokes Lean, Lake, Git, the network, a remote service, or a repository source
mutation.
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

SCHEMA = "qym-probe12-early-frontier-p11-conditional-v1-exact-terminal-probe11"
INPUT_SHA256 = "d8290febb2b1c69cc8b911bcb672303beede1b87db290bd37c6608e39356cf25"
INPUT_GIT_BLOB = "9b5ba50acc8e2f3d6f55cf8cef6fc505926410cd"
INPUT_BYTES = 2_928_376
INPUT_LF = 61_891
LOG_SHA256 = "474f153278507d0ead7fe21675f326def15556281bd7b5cf67392836ea5ea97e"
HEADERS_SHA256 = "b0fe7508ba87fc324236cce71b74c59d042a0833ec1c101a1ae625a1f24dd4e6"
DIAGNOSTICS_SHA256 = "d9259b316d1c1317ea7e11f8f0370feaabacb3a2ae6066c3133ab748a2dee504"

# Filled once by --bootstrap-seal, then enforced in both directions.
OUTPUT_SHA256 = "0a6544bc32715b99f4117854073efb4acf6afb4fa1e6293cbb1060033af368da"
OUTPUT_GIT_BLOB = "4d5297c9a839aaf4bf370bf1ff137bc6ba26ade0"
OUTPUT_BYTES = 2_928_721
OUTPUT_LF = 61_894

FOREIGN_PROBE12_HELPERS: tuple[tuple[str, str, str, str], ...] = (
    (
        "probe12_p10_midlate_refinement",
        "qym-probe12-p10-midlate-refinement/qym_probe12_p10_midlate_refinement.py",
        "058dba8e252db0562b7b83ed5d6701445b41f189db0559e06613823f1565207d",
        "applied_new_in_probe11",
    ),
    (
        "probe12_36k42k_p10_conditional",
        "qym-probe12-36k42k-p10-conditional/qym_probe12_36k42k_p10_conditional.py",
        "9c3df7c522538373943cde18e2a788a4fc7feec5412724e37ccfb6a508865095",
        "inactive_old",
    ),
    (
        "probe12_43k49k_p10_conditional",
        "qym-probe12-43k49k-p10-conditional/qym_probe12_43k49k_p10_conditional.py",
        "5cea81a9deb981609655d767487a3cbb5fda032849869902ba074d8729fa976d",
        "inactive_old",
    ),
    (
        "probe12_52k61k_p10_conditional",
        "qym-probe12-52k61k-p10-conditional/qym_probe12_52k61k_p10_conditional.py",
        "dde4c4df0473bbbd1da69bce9968f00b0859d045d254740b5852f72e5b489545",
        "inactive_old",
    ),
)


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
    precedent: str
    occurrences: int = 1


RULES: tuple[Rule, ...] = (
    Rule(
        "raw_differential_deck_split_eq_trans",
        """theorem rawDifferential_deck_comp
    (g : SmoothInvariantScalar) (γ : Gamma2) (τ : H) :
    (rawDifferential g (γ • τ)).comp (manifoldDeckDerivative γ τ) =
      rawDifferential g τ := by
  have hgAt : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) g.1 (γ • τ) :=
    ((SmoothInvariantScalar.smooth g).mdifferentiable (by simp)) (γ • τ)
  have hdeckAt :
      MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (manifoldDeckMap γ) τ :=
    (manifoldDeckMap_smooth γ).mdifferentiable (by simp) τ
  have hfun : g.1 ∘ manifoldDeckMap γ = g.1 := by
    funext σ
    exact SmoothInvariantScalar.invariant g γ σ
  calc
    (rawDifferential g (γ • τ)).comp (manifoldDeckDerivative γ τ) =
        (mvfderiv 𝓘(ℂ) (g.1 ∘ manifoldDeckMap γ) τ :
          ScalarOneFormValue) := by
      symm
      simpa only [rawDifferential, manifoldDeckDerivative, manifoldDeckMap]
        using mvfderiv_comp τ hgAt hdeckAt
    _ = rawDifferential g τ := by
      simpa only [rawDifferential, hfun]
""",
        """theorem rawDifferential_deck_comp
    (g : SmoothInvariantScalar) (γ : Gamma2) (τ : H) :
    (rawDifferential g (γ • τ)).comp (manifoldDeckDerivative γ τ) =
      rawDifferential g τ := by
  have hgAt : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) g.1 (γ • τ) :=
    ((SmoothInvariantScalar.smooth g).mdifferentiable (by simp)) (γ • τ)
  have hdeckAt :
      MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (manifoldDeckMap γ) τ :=
    (manifoldDeckMap_smooth γ).mdifferentiable (by simp) τ
  have hfun : g.1 ∘ manifoldDeckMap γ = g.1 := by
    funext σ
    exact SmoothInvariantScalar.invariant g γ σ
  have hchain :
      (rawDifferential g (γ • τ)).comp (manifoldDeckDerivative γ τ) =
        (mvfderiv 𝓘(ℂ) (g.1 ∘ manifoldDeckMap γ) τ :
          ScalarOneFormValue) := by
    symm
    simpa only [rawDifferential, manifoldDeckDerivative, manifoldDeckMap]
      using mvfderiv_comp τ hgAt hdeckAt
  have htransport :
      (mvfderiv 𝓘(ℂ) (g.1 ∘ manifoldDeckMap γ) τ :
        ScalarOneFormValue) = rawDifferential g τ := by
    simpa only [rawDifferential, hfun]
  exact hchain.trans htransport
""",
        (Header(28363, 4, "invalid 'calc' step, failed to synthesize `Trans` instance"),),
        "Replace the overloaded calc relation chain by two explicitly typed Eq witnesses and Eq.trans.",
        "The first Eq body is exactly the P11 elaborated chain-rule step; only the failing Trans composition is removed.",
    ),
    Rule(
        "raw_differential_smul_pin_eq_carrier",
        """theorem rawDifferential_smul
    (c : ℂ) (g : SmoothInvariantScalar) (τ : H) :
    rawDifferential (c • g) τ = c • rawDifferential g τ := by
  have hg : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) g.1 τ :=
    ((SmoothInvariantScalar.smooth g).mdifferentiable (by simp)) τ
  have hc : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ)
      (fun _ : H => c) τ :=
    mdifferentiableAt_const
  simpa [rawDifferential, mvfderiv_const] using
    (mvfderiv_smul hc hg)
""",
        """theorem rawDifferential_smul
    (c : ℂ) (g : SmoothInvariantScalar) (τ : H) :
    rawDifferential (c • g) τ = c • rawDifferential g τ := by
  have hg : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) g.1 τ :=
    ((SmoothInvariantScalar.smooth g).mdifferentiable (by simp)) τ
  have hc : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ)
      (fun _ : H => c) τ :=
    mdifferentiableAt_const
  change @Eq ScalarOneFormValue _ _
  simpa [rawDifferential, mvfderiv_const] using
    (mvfderiv_smul hc hg)
""",
        (Header(28386, 2, "Type mismatch: After simplification, term"),),
        "Pin the equality carrier before simplifying the value-space manifold derivative theorem.",
        "The exact exit-zero FA source uses the same @Eq carrier pin before dependent Lp linearity theorems at lines 52208-52215.",
    ),
    Rule(
        "safe_matter_norm_smul_pin_both_arguments",
        """      norm_smul_le _ _
""",
        """      norm_smul_le
        (sectorPotentialCoefficient sector : ℂ)
        (deltaMatterPotential Y :
          EtaMatterCarrier Y →L[ℂ] EtaMatterCarrier Y)
""",
        (Header(32090, 6, "Type mismatch"),),
        "Pin both arguments of norm_smul_le so its bounded-smul instance is selected at the exact operator type.",
        "The P11 diagnostic shows both theorem arguments remained metavariables despite the fully concrete expected inequality.",
    ),
    Rule(
        "safe_matter_inner_self_pin_complex_real_goal",
        """  exact mul_nonneg (sectorPotentialCoefficient_nonneg sector) inner_self_nonneg
""",
        """  exact mul_nonneg (sectorPotentialCoefficient_nonneg sector)
    (inner_self_nonneg : 0 ≤ (⟪u, u⟫_ℂ).re)
""",
        (Header(32124, 62, "Application type mismatch: The argument"),),
        "Specialize inner_self_nonneg to the exact complex inner product real-part goal.",
        "P11 inferred a generic RCLike.re theorem while the expected term is syntactically (inner C u u).re.",
    ),
    Rule(
        "eta_horizontal_trace_use_dependent_simp",
        """    unfold etaHorizontalTraceToL2
    rw [hfun]
    exact MemLp.toLp_add
      (etaHorizontalTraceRepresentative_memLp Y g)
      (etaHorizontalTraceRepresentative_memLp Y h)
  map_smul' c g := by
    have hfun :
        etaHorizontalTraceRepresentative Y (c • g) =
          c • etaHorizontalTraceRepresentative Y g := by
      funext x
      simp only [etaHorizontalTraceRepresentative, Submodule.coe_smul,
        etaSection_smul, Pi.smul_apply]
    unfold etaHorizontalTraceToL2
    rw [hfun]
    simpa only [RingHom.id_apply] using
      (MemLp.toLp_const_smul c
        (etaHorizontalTraceRepresentative_memLp Y g))
""",
        """    simpa only [etaHorizontalTraceToL2, hfun] using
      (MemLp.toLp_add
        (etaHorizontalTraceRepresentative_memLp Y g)
        (etaHorizontalTraceRepresentative_memLp Y h))
  map_smul' c g := by
    have hfun :
        etaHorizontalTraceRepresentative Y (c • g) =
          c • etaHorizontalTraceRepresentative Y g := by
      funext x
      simp only [etaHorizontalTraceRepresentative, Submodule.coe_smul,
        etaSection_smul, Pi.smul_apply]
    simpa only [etaHorizontalTraceToL2, hfun, RingHom.id_apply] using
      (MemLp.toLp_const_smul c
        (etaHorizontalTraceRepresentative_memLp Y g))
""",
        (
            Header(34654, 8, "Tactic `rewrite` failed: motive is not type correct:"),
            Header(34666, 8, "Tactic `rewrite` failed: motive is not type correct:"),
        ),
        "Use dependent simp with the proved representative equality instead of rw across the MemLp proof argument.",
        "The P11 diagnostic explicitly recommends simp for proof-dependent motives; MemLp.toLp_add and toLp_const_smul remain unchanged.",
    ),
    Rule(
        "actual_horizontal_trace_use_dependent_simp",
        """    unfold actualFixedPhaseHorizontalTraceToL2
    rw [hfun]
    exact MemLp.toLp_add
      (actualFixedPhaseHorizontalTraceRepresentative_memLp n Y u)
      (actualFixedPhaseHorizontalTraceRepresentative_memLp n Y v)
  map_smul' c u := by
    have hfun :
        actualFixedPhaseHorizontalTraceRepresentative n Y (c • u) =
          c • actualFixedPhaseHorizontalTraceRepresentative n Y u := by
      funext x
      simp only [actualFixedPhaseHorizontalTraceRepresentative,
        InverseEtaFixedPhaseCore.toSmoothQuotientCompactFunction,
        Submodule.coe_smul, Pi.smul_apply]
    unfold actualFixedPhaseHorizontalTraceToL2
    rw [hfun]
    simpa only [RingHom.id_apply] using
      (MemLp.toLp_const_smul c
        (actualFixedPhaseHorizontalTraceRepresentative_memLp n Y u))
""",
        """    simpa only [actualFixedPhaseHorizontalTraceToL2, hfun] using
      (MemLp.toLp_add
        (actualFixedPhaseHorizontalTraceRepresentative_memLp n Y u)
        (actualFixedPhaseHorizontalTraceRepresentative_memLp n Y v))
  map_smul' c u := by
    have hfun :
        actualFixedPhaseHorizontalTraceRepresentative n Y (c • u) =
          c • actualFixedPhaseHorizontalTraceRepresentative n Y u := by
      funext x
      simp only [actualFixedPhaseHorizontalTraceRepresentative,
        InverseEtaFixedPhaseCore.toSmoothQuotientCompactFunction,
        Submodule.coe_smul, Pi.smul_apply]
    simpa only [actualFixedPhaseHorizontalTraceToL2, hfun,
      RingHom.id_apply] using
      (MemLp.toLp_const_smul c
        (actualFixedPhaseHorizontalTraceRepresentative_memLp n Y u))
""",
        (
            Header(35097, 8, "Tactic `rewrite` failed: motive is not type correct:"),
            Header(35110, 8, "Tactic `rewrite` failed: motive is not type correct:"),
        ),
        "Apply the same proof-dependent simp repair to the fixed-phase horizontal L2 map.",
        "The two P11 motives differ from the eta trace only by the representative and measure names.",
    ),
    Rule(
        "actual_named_cusp_trace_use_dependent_simp",
        """    unfold actualFixedPhaseNamedCuspTraceToL2
    rw [hfun]
    exact MemLp.toLp_add
      (actualFixedPhaseNamedCuspTraceRepresentative_memLp n kappa Y u)
      (actualFixedPhaseNamedCuspTraceRepresentative_memLp n kappa Y v)
  map_smul' c u := by
    have hfun :
        actualFixedPhaseNamedCuspTraceRepresentative n kappa Y (c • u) =
          c • actualFixedPhaseNamedCuspTraceRepresentative n kappa Y u := by
      funext x
      simp only [actualFixedPhaseNamedCuspTraceRepresentative,
        InverseEtaFixedPhaseCore.toSmoothQuotientCompactFunction,
        Submodule.coe_smul, Pi.smul_apply]
    unfold actualFixedPhaseNamedCuspTraceToL2
    rw [hfun]
    simpa only [RingHom.id_apply] using
      (MemLp.toLp_const_smul c
        (actualFixedPhaseNamedCuspTraceRepresentative_memLp n kappa Y u))
""",
        """    simpa only [actualFixedPhaseNamedCuspTraceToL2, hfun] using
      (MemLp.toLp_add
        (actualFixedPhaseNamedCuspTraceRepresentative_memLp n kappa Y u)
        (actualFixedPhaseNamedCuspTraceRepresentative_memLp n kappa Y v))
  map_smul' c u := by
    have hfun :
        actualFixedPhaseNamedCuspTraceRepresentative n kappa Y (c • u) =
          c • actualFixedPhaseNamedCuspTraceRepresentative n kappa Y u := by
      funext x
      simp only [actualFixedPhaseNamedCuspTraceRepresentative,
        InverseEtaFixedPhaseCore.toSmoothQuotientCompactFunction,
        Submodule.coe_smul, Pi.smul_apply]
    simpa only [actualFixedPhaseNamedCuspTraceToL2, hfun,
      RingHom.id_apply] using
      (MemLp.toLp_const_smul c
        (actualFixedPhaseNamedCuspTraceRepresentative_memLp n kappa Y u))
""",
        (
            Header(35232, 8, "Tactic `rewrite` failed: motive is not type correct:"),
            Header(35245, 8, "Tactic `rewrite` failed: motive is not type correct:"),
        ),
        "Apply dependent simp to the named-cusp add and scalar representatives.",
        "The P11 error text identifies the same MemLp proof-dependent rewrite failure twice.",
    ),
    Rule(
        "cusp_class_horocycle_open_pointwise_before_doc",
        """/-- Every selected cusp-class horocycle union is closed.  Finiteness of the
right-coset type is essential here. -/
theorem cuspClassHorocycleBoundary_isClosed
""",
        """open scoped Pointwise

/-- Every selected cusp-class horocycle union is closed.  Finiteness of the
right-coset type is essential here. -/
theorem cuspClassHorocycleBoundary_isClosed
""",
        (Header(35759, 7, "failed to synthesize instance of type class", "lean.synthInstanceFailed"),),
        "Open Pointwise before the declaration so Set smul resolves after the already-applied GL cast.",
        "The applied Probe11 refinement correctly pins GL(Fin 2,R); P11 now reports only the missing HSMul GL (Set H) pointwise instance.",
    ),
)


EXCLUDED_EXISTING_PROBE12_ROOTS: tuple[Header, ...] = (
    Header(34075, 17, "unexpected token 'open'; expected 'lemma'"),
    Header(34171, 2, "Type mismatch: After simplification, term"),
)

EXPECTED_RANGE_ROOTS = {
    (28363, 4),
    (28386, 2),
    (32090, 6),
    (32124, 62),
    (34075, 17),
    (34171, 2),
    (34654, 8),
    (34666, 8),
    (35097, 8),
    (35110, 8),
    (35232, 8),
    (35245, 8),
    (35759, 7),
}


def sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def git_blob(raw: bytes) -> str:
    return hashlib.sha1(f"blob {len(raw)}\0".encode("ascii") + raw).hexdigest()


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


def input_expected() -> dict[str, object]:
    return {
        "sha256": INPUT_SHA256,
        "git_blob": INPUT_GIT_BLOB,
        "bytes": INPUT_BYTES,
        "lf": INPUT_LF,
        "cr": False,
        "nul": False,
        "bom": False,
        "terminal_lf": True,
    }


def output_expected() -> dict[str, object]:
    return {
        "sha256": OUTPUT_SHA256,
        "git_blob": OUTPUT_GIT_BLOB,
        "bytes": OUTPUT_BYTES,
        "lf": OUTPUT_LF,
        "cr": False,
        "nul": False,
        "bom": False,
        "terminal_lf": True,
    }


def sentinels_unsealed() -> bool:
    return OUTPUT_SHA256 == "" and OUTPUT_GIT_BLOB == "" and OUTPUT_BYTES == 0 and OUTPUT_LF == 0


def check_shape(actual: dict[str, object], expected: dict[str, object], *, unsealed: bool = False) -> None:
    keys = ("cr", "nul", "bom", "terminal_lf") if unsealed else tuple(expected)
    if any(actual[key] != expected[key] for key in keys):
        raise RuntimeError(f"shape mismatch: {actual} != {expected}")


def verify_authority(log_raw: bytes, headers_raw: bytes, diagnostics_raw: bytes) -> tuple[list[dict[str, object]], list[dict[str, object]]]:
    for label, actual, expected in (
        ("log", sha256(log_raw), LOG_SHA256),
        ("headers", sha256(headers_raw), HEADERS_SHA256),
        ("diagnostics", sha256(diagnostics_raw), DIAGNOSTICS_SHA256),
    ):
        if actual != expected:
            raise RuntimeError(f"Probe11 {label} identity mismatch: {actual} != {expected}")

    log_text = log_raw.decode("utf-8", errors="strict")
    header_lines = headers_raw.decode("utf-8", errors="strict").splitlines()
    rows = [json.loads(line) for line in diagnostics_raw.decode("utf-8", errors="strict").splitlines()]
    extracted = [
        line
        for line in log_text.splitlines()
        if re.match(r"^PrimalitySheafVerification/QYM\.lean:\d+:\d+: error(?:\([^)]*\))?: ", line)
    ]
    if len(header_lines) != 217 or extracted != header_lines:
        raise RuntimeError("exact Probe11 error-header extraction mismatch")
    if sum(row.get("severity") == "error" for row in rows) != 217:
        raise RuntimeError("diagnostic error count is not 217")
    if sum(row.get("severity") == "warning" for row in rows) != 350:
        raise RuntimeError("diagnostic warning count is not 350")

    range_rows = [
        row
        for row in rows
        if row.get("severity") == "error" and 28_000 <= int(row.get("line", -1)) <= 36_000
    ]
    range_keys = {(int(row["line"]), int(row["column"])) for row in range_rows}
    if range_keys != EXPECTED_RANGE_ROOTS or len(range_rows) != len(EXPECTED_RANGE_ROOTS):
        raise RuntimeError(f"28k-36k authority set mismatch: {sorted(range_keys)}")

    def map_one(header: Header, owner: str) -> dict[str, object]:
        code_text = f"\\({re.escape(header.code)}\\)" if header.code else ""
        pattern = re.compile(
            rf"^PrimalitySheafVerification/QYM\.lean:{header.line}:{header.column}: "
            rf"error{code_text}: {re.escape(header.message)}"
        )
        hm = [line for line in header_lines if pattern.match(line)]
        dm = [
            row
            for row in rows
            if row.get("severity") == "error"
            and row.get("line") == header.line
            and row.get("column") == header.column
            and row.get("code") == header.code
            and str(row.get("message", "")).startswith(header.message)
        ]
        if len(hm) != 1 or len(dm) != 1:
            raise RuntimeError(f"{owner}: authority mapping mismatch at {header.line}:{header.column}")
        return {
            "owner": owner,
            "line": header.line,
            "column": header.column,
            "message": header.message,
            "code": header.code,
            "kind": "current_probe11_direct_root",
        }

    selected = [map_one(header, rule.label) for rule in RULES for header in rule.headers]
    excluded = [map_one(header, "existing_probe12_p10_midlate_refinement") for header in EXCLUDED_EXISTING_PROBE12_ROOTS]
    selected_keys = {(item["line"], item["column"]) for item in selected}
    excluded_keys = {(item["line"], item["column"]) for item in excluded}
    if selected_keys & excluded_keys or selected_keys | excluded_keys != EXPECTED_RANGE_ROOTS:
        raise RuntimeError("selected/excluded Probe11 partition mismatch")
    if len(selected) != 11 or len(excluded) != 2:
        raise RuntimeError("expected eleven selected and two excluded roots")
    return selected, excluded


def spans(text: str, needle: str) -> list[tuple[int, int]]:
    result: list[tuple[int, int]] = []
    start = 0
    while True:
        found = text.find(needle, start)
        if found < 0:
            return result
        result.append((found, found + len(needle)))
        start = found + 1


def literal_string(node: ast.AST, constants: dict[str, str]) -> str:
    if isinstance(node, ast.Constant) and isinstance(node.value, str):
        return node.value
    if isinstance(node, ast.Name) and node.id in constants:
        return constants[node.id]
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add):
        return literal_string(node.left, constants) + literal_string(node.right, constants)
    raise RuntimeError(f"non-static string expression in foreign helper: {ast.dump(node)}")


def static_foreign_rules(raw: bytes, path: Path) -> tuple[tuple[str, str, str], ...]:
    tree = ast.parse(raw.decode("utf-8", errors="strict"), filename=str(path))
    constants: dict[str, str] = {}
    changed = True
    while changed:
        changed = False
        for node in tree.body:
            target: ast.expr | None = None
            value: ast.expr | None = None
            if isinstance(node, ast.Assign) and len(node.targets) == 1:
                target, value = node.targets[0], node.value
            elif isinstance(node, ast.AnnAssign):
                target, value = node.target, node.value
            if isinstance(target, ast.Name) and value is not None and target.id not in constants:
                try:
                    constants[target.id] = literal_string(value, constants)
                    changed = True
                except RuntimeError:
                    pass

    rules_node: ast.AST | None = None
    for node in tree.body:
        target = None
        value = None
        if isinstance(node, ast.Assign) and len(node.targets) == 1:
            target, value = node.targets[0], node.value
        elif isinstance(node, ast.AnnAssign):
            target, value = node.target, node.value
        if isinstance(target, ast.Name) and target.id == "RULES":
            rules_node = value
            break
    if not isinstance(rules_node, (ast.Tuple, ast.List)):
        raise RuntimeError(f"foreign helper RULES is not a static tuple: {path.name}")
    result: list[tuple[str, str, str]] = []
    for elt in rules_node.elts:
        if not isinstance(elt, ast.Call) or len(elt.args) < 3:
            raise RuntimeError(f"foreign helper rule is not a static Rule call: {path.name}")
        result.append(
            (
                literal_string(elt.args[0], constants),
                literal_string(elt.args[1], constants),
                literal_string(elt.args[2], constants),
            )
        )
    if not result:
        raise RuntimeError(f"foreign helper has no rules: {path.name}")
    return tuple(result)


def audit_collisions(text: str, *, inverse: bool) -> dict[str, object]:
    own: list[tuple[int, int, str]] = []
    for rule in RULES:
        active = rule.new if inverse else rule.old
        found = spans(text, active)
        if len(found) != rule.occurrences:
            raise RuntimeError(f"{rule.label}: active anchor count {len(found)}")
        for start, end in found:
            line = text.count("\n", 0, start) + 1
            if not 28_000 <= line <= 36_000:
                raise RuntimeError(f"{rule.label}: scope violation at line {line}")
            own.append((start, end, rule.label))
    own_sorted = sorted(own)
    own_overlaps = [
        {"left": left[2], "right": right[2]}
        for left, right in zip(own_sorted, own_sorted[1:])
        if left[1] > right[0]
    ]

    foreign_identities: dict[str, dict[str, object]] = {}
    exact_equalities: list[dict[str, str]] = []
    foreign_overlaps: list[dict[str, object]] = []
    foreign_spans_checked = 0
    base = Path(__file__).resolve().parent.parent
    for name, relative, expected_sha, state in FOREIGN_PROBE12_HELPERS:
        path = base / relative
        raw = path.read_bytes()
        actual_sha = sha256(raw)
        if actual_sha != expected_sha:
            raise RuntimeError(f"foreign Probe12 helper identity mismatch: {name}: {actual_sha}")
        foreign_rules = static_foreign_rules(raw, path)
        foreign_identities[name] = {
            "sha256": actual_sha,
            "state": state,
            "rules": len(foreign_rules),
            "executed": False,
        }
        for foreign_label, foreign_old, foreign_new in foreign_rules:
            for foreign_variant, anchor in (("old", foreign_old), ("new", foreign_new)):
                found = spans(text, anchor)
                foreign_spans_checked += len(found)
                for own_rule in RULES:
                    for own_variant, own_anchor in (("old", own_rule.old), ("new", own_rule.new)):
                        if own_anchor == anchor:
                            exact_equalities.append(
                                {
                                    "own": own_rule.label,
                                    "own_variant": own_variant,
                                    "foreign": f"{name}:{foreign_label}",
                                    "foreign_variant": foreign_variant,
                                }
                            )
                for fstart, fend in found:
                    for ostart, oend, own_label in own:
                        if max(fstart, ostart) < min(fend, oend):
                            foreign_overlaps.append(
                                {
                                    "own": own_label,
                                    "foreign": f"{name}:{foreign_label}",
                                    "foreign_variant": foreign_variant,
                                    "own_span": [ostart, oend],
                                    "foreign_span": [fstart, fend],
                                }
                            )
    if own_overlaps or exact_equalities or foreign_overlaps:
        raise RuntimeError(
            f"collision: own={own_overlaps}, equalities={exact_equalities}, foreign={foreign_overlaps}"
        )
    return {
        "method": "AST_AND_HASH_ONLY_FOREIGN_HELPERS_NEVER_IMPORTED_OR_EXECUTED",
        "foreign_helpers": foreign_identities,
        "own_spans_checked": len(own),
        "foreign_active_spans_checked": foreign_spans_checked,
        "own_span_overlaps": own_overlaps,
        "exact_anchor_equalities": exact_equalities,
        "foreign_span_overlaps": foreign_overlaps,
        "pass": True,
    }


def apply_rules(text: str, inverse: bool = False) -> tuple[str, list[dict[str, object]]]:
    audit: list[dict[str, object]] = []
    ordered = tuple(reversed(RULES)) if inverse else RULES
    for rule in ordered:
        old, new = (rule.new, rule.old) if inverse else (rule.old, rule.new)
        count = text.count(old)
        if count != rule.occurrences:
            raise RuntimeError(f"{rule.label}: exact anchor count {count}, expected {rule.occurrences}")
        text = text.replace(old, new)
        audit.append(
            {
                "label": rule.label,
                "direction": "inverse" if inverse else "forward",
                "occurrences": count,
                "headers": [header.__dict__ for header in rule.headers],
                "rationale": rule.rationale,
                "precedent": rule.precedent,
            }
        )
    return text, audit


transform = apply_rules


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--probe11-log", type=Path, required=True)
    parser.add_argument("--probe11-error-headers", type=Path, required=True)
    parser.add_argument("--probe11-diagnostics", type=Path, required=True)
    parser.add_argument("--audit", type=Path, required=True)
    parser.add_argument("--mode", choices=("forward", "inverse"), default="forward")
    parser.add_argument("--bootstrap-seal", action="store_true")
    args = parser.parse_args()
    inverse = args.mode == "inverse"
    if args.bootstrap_seal and not sentinels_unsealed():
        raise RuntimeError("bootstrap refused: output identity already sealed")
    if not args.bootstrap_seal and sentinels_unsealed():
        raise RuntimeError("output identity unsealed")

    source = args.input.read_bytes()
    source_shape = shape(source)
    check_shape(
        source_shape,
        output_expected() if inverse else input_expected(),
        unsealed=args.bootstrap_seal and inverse,
    )
    selected, excluded = verify_authority(
        args.probe11_log.read_bytes(),
        args.probe11_error_headers.read_bytes(),
        args.probe11_diagnostics.read_bytes(),
    )
    source_text = source.decode("utf-8", errors="strict")
    collision = audit_collisions(source_text, inverse=inverse)
    before_trust = trust(source_text)
    result_text, rule_audit = apply_rules(source_text, inverse=inverse)
    result = result_text.encode("utf-8")
    result_shape = shape(result)
    check_shape(
        result_shape,
        input_expected() if inverse else output_expected(),
        unsealed=args.bootstrap_seal and not inverse,
    )
    after_trust = trust(result_text)
    if before_trust != after_trust or any(after_trust.values()):
        raise RuntimeError(f"trust0 failure: {before_trust} -> {after_trust}")
    restored, _ = apply_rules(result_text, inverse=not inverse)
    if restored.encode("utf-8") != source:
        raise RuntimeError("opposite transform failed byte-exact restoration")
    if args.output.exists() or args.audit.exists():
        raise RuntimeError("refusing to overwrite output or audit")

    record = {
        "schema": SCHEMA,
        "status": "STATIC_PASS_EXACT_TERMINAL_PROBE11_NOT_LEAN_EXECUTED",
        "activation": False,
        "promotion": False,
        "mode": args.mode,
        "authority": {
            "run_id": 31977171554,
            "candidate_sha256": INPUT_SHA256,
            "candidate_git_blob": INPUT_GIT_BLOB,
            "log_sha256": LOG_SHA256,
            "error_headers_sha256": HEADERS_SHA256,
            "diagnostics_sha256": DIAGNOSTICS_SHA256,
            "errors": 217,
            "warnings": 350,
            "panic": 0,
            "exit": 1,
        },
        "scope": {
            "candidate_lines": [28_000, 36_000],
            "current_range_roots": 13,
            "selected_direct_roots": 11,
            "excluded_existing_probe12_roots": 2,
            "closed_probe11_rules_selected": False,
            "cascade_diagnostics_selected": False,
            "existing_probe12_rules_selected": False,
        },
        "source": source_shape,
        "result": result_shape,
        "repair_families": len(RULES),
        "repair_occurrences": sum(item["occurrences"] for item in rule_audit),
        "direct_diagnostics": len(selected),
        "selected_exact_probe11_lines": sorted({int(item["line"]) for item in selected}),
        "selected_diagnostic_map": selected,
        "excluded_diagnostic_map": excluded,
        "rules": rule_audit,
        "collision_audit": collision,
        "inverse_byte_equal": True,
        "trust": after_trust,
        "execution": {
            "lean": False,
            "lake": False,
            "git": False,
            "network": False,
            "remote": False,
            "repository_source_mutation": False,
            "foreign_helper_import": False,
            "foreign_helper_execution": False,
        },
    }
    args.output.write_bytes(result)
    args.audit.write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(json.dumps(record, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
