#!/usr/bin/env python3
"""Declaration-aware fallback strategy pack layered on the persistent v9 engine."""

from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("qym_v9", ROOT / ".github/qym_autorepair_v9.py")
if spec is None or spec.loader is None:
    raise RuntimeError("cannot load qym_autorepair_v9.py")
v9 = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = v9
spec.loader.exec_module(v9)


def corrected_prefix_source(candidate, decl):
    prefix = candidate.source[: decl.by_offset + len(candidate.proof)]
    return prefix.rstrip() + "\n" + v9.closing_commands(prefix)


def specialized_templates():
    return [
        ("exact_mul_inv", "by\n  exact mul_inv_cancel _"),
        ("exact_inv_mul", "by\n  exact inv_mul_cancel _"),
        ("apply_mul_inv", "by\n  apply mul_inv_cancel"),
        ("apply_inv_mul", "by\n  apply inv_mul_cancel"),
        ("simpa_mul_inv", "by\n  simpa using (mul_inv_cancel _)"),
        ("simpa_inv_mul", "by\n  simpa using (inv_mul_cancel _)"),
        (
            "cusp_simpa_mul_inv",
            "by\n  simpa [gammaTwoCuspScaling] using "
            "(mul_inv_cancel (gammaTwoCuspScaling ‹GammaTwoCusp›))",
        ),
        (
            "cusp_simpa_inv_mul",
            "by\n  simpa [gammaTwoCuspScaling] using "
            "(inv_mul_cancel (gammaTwoCuspScaling ‹GammaTwoCusp›))",
        ),
        (
            "cusp_cases_simp_only",
            "by\n  cases ‹GammaTwoCusp› <;>\n"
            "    simp only [gammaTwoCuspScaling, mul_inv_cancel, inv_mul_cancel]",
        ),
        (
            "cusp_cases_change_simp",
            "by\n  cases ‹GammaTwoCusp› <;> change _ <;> simp [gammaTwoCuspScaling]",
        ),
        (
            "cusp_cases_ext_decide",
            "by\n  cases ‹GammaTwoCusp› <;> ext i j <;> fin_cases i <;> fin_cases j <;> decide",
        ),
        (
            "cusp_cases_ext_native",
            "by\n  cases ‹GammaTwoCusp› <;> ext i j <;> fin_cases i <;> fin_cases j <;> native_decide",
        ),
        (
            "cusp_cases_ext_norm_full",
            "by\n  cases ‹GammaTwoCusp› <;> ext i j <;> fin_cases i <;> fin_cases j <;>\n"
            "    norm_num [gammaTwoCuspScaling, Matrix.mul_apply, ModularGroup.S, ModularGroup.T]",
        ),
        (
            "cusp_cases_unfold_simp",
            "by\n  cases ‹GammaTwoCusp› <;> unfold gammaTwoCuspScaling <;> simp",
        ),
        ("classical_exact_search", "by\n  classical\n  exact?"),
        ("classical_simp_search", "by\n  classical\n  simp?"),
        ("classical_aesop_search", "by\n  classical\n  aesop?"),
        ("solve_by_elim", "by\n  solve_by_elim"),
        ("assumption", "by\n  assumption"),
        ("contradiction", "by\n  contradiction"),
        ("tauto", "by\n  tauto"),
        ("linarith", "by\n  linarith"),
        ("nlinarith", "by\n  nlinarith"),
        ("polyrith", "by\n  polyrith"),
        ("field_simp", "by\n  field_simp"),
        ("abel", "by\n  abel"),
        ("ext_norm_num", "by\n  ext <;> norm_num [gammaTwoCuspScaling, Matrix.mul_apply]"),
        ("cases_all_simp", "by\n  aesop (add safe cases GammaTwoCusp)"),
        (
            "classical_all_goals",
            "by\n  classical\n  all_goals simp_all [gammaTwoCuspScaling, Matrix.mul_apply]",
        ),
    ] + v9.proof_templates()


v9.prefix_source = corrected_prefix_source
v9.proof_templates = specialized_templates
v9.MAX_ROUNDS = max(v9.MAX_ROUNDS, 50)
v9.MAX_FULL_CANDIDATES = max(v9.MAX_FULL_CANDIDATES, 6)

if __name__ == "__main__":
    raise SystemExit(v9.main())
