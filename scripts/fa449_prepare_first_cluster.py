#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path
from typing import Callable

ROOT = Path.cwd()
SOURCE = ROOT / "PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean"
EXPECTED_SHA = "1243b2ba563d364a6977cbf9aa867e628de50a28b0f56677dc70456a210e209a"
TARGET_HEADER = "actualEdgeAmbientParam_hasDerivAt"
DECL_RE = re.compile(
    r"^(?:protected\s+|private\s+|noncomputable\s+)?"
    r"(?:theorem|lemma|def|abbrev|instance|structure|class)\s+([^\s(:]+)",
    re.MULTILINE,
)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def declaration_span(text: str, name: str) -> tuple[int, int]:
    matches = list(DECL_RE.finditer(text))
    for index, match in enumerate(matches):
        if match.group(1) == name:
            end = matches[index + 1].start() if index + 1 < len(matches) else len(text)
            return match.start(), end
    raise RuntimeError(f"declaration not found: {name}")


def declaration_header(text: str, name: str) -> str:
    start, end = declaration_span(text, name)
    block = text[start:end]
    marker = block.find(":= by")
    marker_len = len(":= by")
    if marker < 0:
        marker = block.find(":=")
        marker_len = len(":=")
    if marker < 0:
        raise RuntimeError(f"proof marker not found: {name}")
    return block[: marker + marker_len]


def replace_proof(text: str, name: str, proof: str) -> tuple[str, dict[str, object]]:
    start, end = declaration_span(text, name)
    block = text[start:end]
    marker = block.find(":= by")
    if marker < 0:
        raise RuntimeError(f"`:= by` not found in {name}")
    prefix = block[:marker]
    suffix = "\n" if block.endswith("\n") else ""
    new_block = prefix + ":= " + proof.rstrip() + "\n" + suffix
    return text[:start] + new_block + text[end:], {
        "declaration": name,
        "old_block_sha256": sha256(block.encode()),
        "new_block_sha256": sha256(new_block.encode()),
    }


ADD_EXPLICIT = """by
  funext t
  change
    (selectedCuspTraceWeight n q Y t : ℂ) *
        (((u : SmoothQuotientCompactFunction)
          (gammaTwoSelectedHorocycleParam q Y t)) +
         ((v : SmoothQuotientCompactFunction)
          (gammaTwoSelectedHorocycleParam q Y t))) =
      (selectedCuspTraceWeight n q Y t : ℂ) *
          ((u : SmoothQuotientCompactFunction)
            (gammaTwoSelectedHorocycleParam q Y t)) +
        (selectedCuspTraceWeight n q Y t : ℂ) *
          ((v : SmoothQuotientCompactFunction)
            (gammaTwoSelectedHorocycleParam q Y t))
  ring"""

ADD_UNFOLD = """by
  funext t
  simp only [selectedCuspRestrictionRepresentative, Pi.add_apply]
  ring"""

MEMLP_EXACT = """by
  let f := selectedCuspRestrictionRepresentative n q Y u
  have hf : Continuous f :=
    selectedCuspRestrictionRepresentative_continuous n q Y u
  apply (memLp_two_iff_integrable_sq_norm
    hf.aestronglyMeasurable).2
  change IntegrableOn (fun x => ‖f x‖ ^ 2)
    (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) volume
  exact (hf.norm.pow 2).continuousOn.integrableOn_Icc"""

MEMLP_CONVERT = """by
  let f := selectedCuspRestrictionRepresentative n q Y u
  have hf : Continuous f :=
    selectedCuspRestrictionRepresentative_continuous n q Y u
  apply (memLp_two_iff_integrable_sq_norm
    hf.aestronglyMeasurable).2
  change IntegrableOn (fun x => ‖f x‖ ^ 2)
    (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) volume
  convert (hf.norm.pow 2).continuousOn.integrableOn_Icc using 1 <;>
    simp only [Pi.pow_apply]"""

MEMLP_HAVE = """by
  let f := selectedCuspRestrictionRepresentative n q Y u
  have hf : Continuous f :=
    selectedCuspRestrictionRepresentative_continuous n q Y u
  apply (memLp_two_iff_integrable_sq_norm
    hf.aestronglyMeasurable).2
  have hInt : IntegrableOn ((fun x : ℝ => ‖f x‖) ^ 2)
      (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) volume :=
    (hf.norm.pow 2).continuousOn.integrableOn_Icc
  simpa only [Pi.pow_apply] using hInt"""

MEMLP_LETI = """by
  let f := selectedCuspRestrictionRepresentative n q Y u
  have hf : Continuous f :=
    selectedCuspRestrictionRepresentative_continuous n q Y u
  apply (memLp_two_iff_integrable_sq_norm
    hf.aestronglyMeasurable).2
  letI : MeasurableSpace ℝ := Real.measurableSpace
  change IntegrableOn (fun x => ‖f x‖ ^ 2)
    (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) volume
  simpa only [Pi.pow_apply] using
    (hf.norm.pow 2).continuousOn.integrableOn_Icc"""

COEFN_CHANGE = """by
  change
    ⇑((selectedCuspRestrictionRepresentative_memLp n q Y u).toLp
      (selectedCuspRestrictionRepresentative n q Y u)) =ᵐ[
        selectedHorocycleParameterMeasure]
      selectedCuspRestrictionRepresentative n q Y u
  exact MemLp.coeFn_toLp
    (selectedCuspRestrictionRepresentative_memLp n q Y u)"""

REP_ZERO = """by
  rcases (fixedPhaseCore_hasZeroThreeCuspTail n u).eventually_zero_on_horocycleBoundary with
    ⟨Y₀, hY₀, hZero⟩
  refine ⟨Y₀, hY₀, ?_⟩
  intro Z hYZ q
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  have hz := hZero Z hYZ
    (gammaTwoSelectedHorocycleParam q Z t)
    ⟨selectedHorocycleParam_mem_closedCarrier q Z ht,
      selectedHorocycleParam_mem_threeCuspBoundary q Z t⟩
  change
    (selectedCuspTraceWeight n q Z t : ℂ) *
        ((u : SmoothQuotientCompactFunction)
          (gammaTwoSelectedHorocycleParam q Z t)) = 0
  rw [hz.1, mul_zero]"""

TRACE_ZERO = """by
  rcases fixedPhaseCore_eventually_selectedCuspRepresentative_ae_zero n u with
    ⟨Y₀, hY₀, hZero⟩
  refine ⟨Y₀, hY₀, ?_⟩
  intro Z hYZ q
  apply MeasureTheory.Lp.ext
  filter_upwards [coeFn_selectedCuspCoreTrace n q Z u,
    hZero Z hYZ q] with t htrace hrep
  change ((selectedCuspCoreTrace n q Z u : SelectedHorocycleL2) : ℝ → ℂ) t =
    (0 : ℂ)
  exact htrace.trans hrep"""

DERIV_PRODUCT = """by
  have hnorm := (hf y).hasDerivAt.norm_sq
  have hprod := (hasDerivAt_id y).mul hnorm
  have hfun : (fun r : ℝ => r * ‖f r‖ ^ 2) =
      id * (fun x : ℝ => ‖f x‖ ^ 2) := by
    funext x
    rfl
  rw [hfun, hprod.deriv]
  simp only [id_eq, one_mul]
  ring"""

NORM_DERIV_GCONGR = """by
  rw [deriv_height_mul_normSq hf y, Real.norm_eq_abs]
  have hinner : |⟪f y, deriv f y⟫_ℝ| ≤
      ‖f y‖ * ‖deriv f y‖ :=
    abs_real_inner_le_norm _ _
  calc
    |‖f y‖ ^ 2 + 2 * y * ⟪f y, deriv f y⟫_ℝ| ≤
        |‖f y‖ ^ 2| + |2 * y * ⟪f y, deriv f y⟫_ℝ| :=
      abs_add_le _ _
    _ = ‖f y‖ ^ 2 + (2 * y) * |⟪f y, deriv f y⟫_ℝ| := by
      rw [abs_of_nonneg (sq_nonneg _), abs_mul,
        abs_of_nonneg (mul_nonneg (by norm_num) hy)]
    _ ≤ ‖f y‖ ^ 2 + (2 * y) *
        (‖f y‖ * ‖deriv f y‖) := by
      gcongr
    _ ≤ 2 * ‖f y‖ ^ 2 + y ^ 2 * ‖deriv f y‖ ^ 2 := by
      nlinarith [sq_nonneg (‖f y‖ - y * ‖deriv f y‖)]"""


def apply_many(text: str, patches: list[tuple[str, str]]) -> tuple[str, list[dict[str, object]]]:
    records: list[dict[str, object]] = []
    for name, proof in patches:
        text, record = replace_proof(text, name, proof)
        records.append(record)
    return text, records


VARIANTS: dict[str, list[tuple[str, str]]] = {
    "baseline": [],
    "add_explicit": [("selectedCuspRestrictionRepresentative_add", ADD_EXPLICIT)],
    "add_unfold": [("selectedCuspRestrictionRepresentative_add", ADD_UNFOLD)],
    "add_memlp_exact": [
        ("selectedCuspRestrictionRepresentative_add", ADD_EXPLICIT),
        ("selectedCuspRestrictionRepresentative_memLp", MEMLP_EXACT),
    ],
    "add_memlp_convert": [
        ("selectedCuspRestrictionRepresentative_add", ADD_EXPLICIT),
        ("selectedCuspRestrictionRepresentative_memLp", MEMLP_CONVERT),
    ],
    "add_memlp_have": [
        ("selectedCuspRestrictionRepresentative_add", ADD_EXPLICIT),
        ("selectedCuspRestrictionRepresentative_memLp", MEMLP_HAVE),
    ],
    "add_memlp_letI": [
        ("selectedCuspRestrictionRepresentative_add", ADD_EXPLICIT),
        ("selectedCuspRestrictionRepresentative_memLp", MEMLP_LETI),
    ],
    "cluster_exact": [
        ("selectedCuspRestrictionRepresentative_add", ADD_EXPLICIT),
        ("selectedCuspRestrictionRepresentative_memLp", MEMLP_EXACT),
        ("coeFn_selectedCuspCoreTrace", COEFN_CHANGE),
        ("fixedPhaseCore_eventually_selectedCuspRepresentative_ae_zero", REP_ZERO),
        ("fixedPhaseCore_eventually_selectedCuspCoreTrace_eq_zero", TRACE_ZERO),
    ],
    "cluster_convert": [
        ("selectedCuspRestrictionRepresentative_add", ADD_EXPLICIT),
        ("selectedCuspRestrictionRepresentative_memLp", MEMLP_CONVERT),
        ("coeFn_selectedCuspCoreTrace", COEFN_CHANGE),
        ("fixedPhaseCore_eventually_selectedCuspRepresentative_ae_zero", REP_ZERO),
        ("fixedPhaseCore_eventually_selectedCuspCoreTrace_eq_zero", TRACE_ZERO),
    ],
    "cluster_have": [
        ("selectedCuspRestrictionRepresentative_add", ADD_EXPLICIT),
        ("selectedCuspRestrictionRepresentative_memLp", MEMLP_HAVE),
        ("coeFn_selectedCuspCoreTrace", COEFN_CHANGE),
        ("fixedPhaseCore_eventually_selectedCuspRepresentative_ae_zero", REP_ZERO),
        ("fixedPhaseCore_eventually_selectedCuspCoreTrace_eq_zero", TRACE_ZERO),
    ],
    "cluster_letI": [
        ("selectedCuspRestrictionRepresentative_add", ADD_EXPLICIT),
        ("selectedCuspRestrictionRepresentative_memLp", MEMLP_LETI),
        ("coeFn_selectedCuspCoreTrace", COEFN_CHANGE),
        ("fixedPhaseCore_eventually_selectedCuspRepresentative_ae_zero", REP_ZERO),
        ("fixedPhaseCore_eventually_selectedCuspCoreTrace_eq_zero", TRACE_ZERO),
    ],
    "cluster_exact_deriv": [
        ("selectedCuspRestrictionRepresentative_add", ADD_EXPLICIT),
        ("selectedCuspRestrictionRepresentative_memLp", MEMLP_EXACT),
        ("coeFn_selectedCuspCoreTrace", COEFN_CHANGE),
        ("fixedPhaseCore_eventually_selectedCuspRepresentative_ae_zero", REP_ZERO),
        ("fixedPhaseCore_eventually_selectedCuspCoreTrace_eq_zero", TRACE_ZERO),
        ("deriv_height_mul_normSq", DERIV_PRODUCT),
        ("norm_deriv_height_mul_normSq_le", NORM_DERIV_GCONGR),
    ],
    "cluster_convert_deriv": [
        ("selectedCuspRestrictionRepresentative_add", ADD_EXPLICIT),
        ("selectedCuspRestrictionRepresentative_memLp", MEMLP_CONVERT),
        ("coeFn_selectedCuspCoreTrace", COEFN_CHANGE),
        ("fixedPhaseCore_eventually_selectedCuspRepresentative_ae_zero", REP_ZERO),
        ("fixedPhaseCore_eventually_selectedCuspCoreTrace_eq_zero", TRACE_ZERO),
        ("deriv_height_mul_normSq", DERIV_PRODUCT),
        ("norm_deriv_height_mul_normSq_le", NORM_DERIV_GCONGR),
    ],
    "cluster_have_deriv": [
        ("selectedCuspRestrictionRepresentative_add", ADD_EXPLICIT),
        ("selectedCuspRestrictionRepresentative_memLp", MEMLP_HAVE),
        ("coeFn_selectedCuspCoreTrace", COEFN_CHANGE),
        ("fixedPhaseCore_eventually_selectedCuspRepresentative_ae_zero", REP_ZERO),
        ("fixedPhaseCore_eventually_selectedCuspCoreTrace_eq_zero", TRACE_ZERO),
        ("deriv_height_mul_normSq", DERIV_PRODUCT),
        ("norm_deriv_height_mul_normSq_le", NORM_DERIV_GCONGR),
    ],
    "cluster_letI_deriv": [
        ("selectedCuspRestrictionRepresentative_add", ADD_EXPLICIT),
        ("selectedCuspRestrictionRepresentative_memLp", MEMLP_LETI),
        ("coeFn_selectedCuspCoreTrace", COEFN_CHANGE),
        ("fixedPhaseCore_eventually_selectedCuspRepresentative_ae_zero", REP_ZERO),
        ("fixedPhaseCore_eventually_selectedCuspCoreTrace_eq_zero", TRACE_ZERO),
        ("deriv_height_mul_normSq", DERIV_PRODUCT),
        ("norm_deriv_height_mul_normSq_le", NORM_DERIV_GCONGR),
    ],
}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--variant", required=True, choices=sorted(VARIANTS))
    parser.add_argument("--output-dir", required=True)
    args = parser.parse_args()

    output = Path(args.output_dir)
    output.mkdir(parents=True, exist_ok=True)
    original = SOURCE.read_bytes()
    original_sha = sha256(original)
    if original_sha != EXPECTED_SHA:
        raise RuntimeError(f"source SHA mismatch: {original_sha} != {EXPECTED_SHA}")
    text = original.decode("utf-8")
    original_header = declaration_header(text, TARGET_HEADER)
    original_decl_sequence = [m.group(1) for m in DECL_RE.finditer(text)]

    candidate, records = apply_many(text, VARIANTS[args.variant])
    candidate_header = declaration_header(candidate, TARGET_HEADER)
    candidate_decl_sequence = [m.group(1) for m in DECL_RE.finditer(candidate)]
    if candidate_header != original_header:
        raise RuntimeError("authoritative blocker theorem header changed")
    if candidate_decl_sequence != original_decl_sequence:
        raise RuntimeError("declaration sequence changed")

    SOURCE.write_text(candidate, encoding="utf-8")
    data = SOURCE.read_bytes()
    metadata = {
        "variant": args.variant,
        "baseline_sha256": EXPECTED_SHA,
        "candidate_sha256": sha256(data),
        "line_count": len(candidate.splitlines()),
        "baseline_line_count": len(text.splitlines()),
        "target_header_sha256": sha256(original_header.encode()),
        "declaration_sequence_sha256": sha256(
            json.dumps(candidate_decl_sequence, separators=(",", ":")).encode()
        ),
        "declaration_count": len(candidate_decl_sequence),
        "repairs": records,
    }
    (output / "CANDIDATE.json").write_text(
        json.dumps(metadata, indent=2) + "\n", encoding="utf-8"
    )
    (output / "Mock2_FunctionalAnalysis-candidate.lean").write_bytes(data)
    print(json.dumps(metadata, indent=2))


if __name__ == "__main__":
    main()
