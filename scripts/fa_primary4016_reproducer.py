#!/usr/bin/env python3
"""Generate a smallest-valid-prefix reproducer and structurally distinct proofs
for the first unresolved FA declaration on the exact verified 4-error source.

The script never changes theorem statements and never introduces axioms, sorry,
admit, unsafe code, native_decide, or unchecked reduction oracles.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

SOURCE = Path("PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean")
EXPECTED_SOURCE_SHA256 = "1c3d12594a3e8b14f9cf7b7294da7c29221758c72d00a596215198f7623fad8c"
PREFIX_PATH = Path("PrimalitySheafVerification/FA_Blocker_Prefix.lean")
CANDIDATE_DIR = Path("PrimalitySheafVerification/FA_Blocker_Candidates")
START_MARKER = "/-- Pointwise splitting of full multiplication into hard and tail parts,\n"
END_MARKER = "theorem norm_discriminantHardStageOperator_sub_graphPotential_le"

PREAMBLE = """import PrimalitySheafVerification.FA_Blocker_Prefix

namespace Mock2FA.PaperCorrections.AutomorphicSobolev
namespace P5DiscriminantHardTruncation

open Set Function Topology Filter MeasureTheory
open scoped ENNReal NNReal
open DefinitionOneSobolev
open DefinitionOneSobolev.FixedPhasePeterssonCoordinates
open DefinitionOneSobolev.FixedPhaseGraphCompletion
open DefinitionOneSobolev.WeightCorePetersson
open GammaTwoQuotientGeometry
open FixedPhaseClosedOperators
open FixedPhaseClosedOperators.PhysicalLocalL2
open ExplicitDiscriminantPotential
open ExplicitDiscriminantPotential.FixedPhaseGraphPotential
open P5PhysicalHardStageRestriction

"""

POSTAMBLE = """

end P5DiscriminantHardTruncation
end Mock2FA.PaperCorrections.AutomorphicSobolev
"""

WEIGHTED_HELPER = r'''/-- A carrier-only subtraction lemma.  It deliberately avoids rewriting the
literal-stage operator equality under a bundled continuous-map subtraction. -/
theorem weightedFull_sub_weightedHardCarrier_eq_weightedTail
    (N : ℕ) (n : ℤ) :
    weightedGraphOperator n discriminantFullCarrierWeightLp -
      weightedGraphOperator n (discriminantHardCarrierWeightLp N) =
    weightedGraphOperator n (discriminantTailCarrierWeightLp N) := by
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.sub_apply, weightedGraphOperator,
    LinearMap.mkContinuous₂_apply, weightedGraphLinear,
    lpInfinityMultiplier_apply]
  rw [← inner_sub_right]
  congr 2
  apply Lp.ext
  filter_upwards [
    coeFn_discriminantFullCarrierWeightLp,
    coeFn_discriminantTailCarrierWeightLp N,
    coeFn_discriminantHardCarrierWeightLp N,
    MeasureTheory.Lp.coeFn_lpSMul discriminantFullCarrierWeightLp
      (graphEuclideanBase n u),
    MeasureTheory.Lp.coeFn_lpSMul (discriminantTailCarrierWeightLp N)
      (graphEuclideanBase n u)] with z hfull htail hhard hfullmul htailmul
  rw [hfullmul, htailmul, hfull, htail, hhard,
    discriminantFull_eq_hard_add_tail]
  ring
'''

DIRECT_SCALAR_BODY = r'''/-- Pointwise splitting of full multiplication into hard and tail parts,
lifted to the graph weak anti-operator. -/
theorem weightedFull_sub_weightedHard_eq_weightedTail
    (N : ℕ) (n : ℤ) :
    weightedGraphOperator n discriminantFullCarrierWeightLp -
      discriminantHardStageOperator N n =
    weightedGraphOperator n (discriminantTailCarrierWeightLp N) := by
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  have hhard :
      discriminantHardStageOperator N n u v =
        weightedGraphOperator n (discriminantHardCarrierWeightLp N) u v :=
    congrArg
      (fun T : WeakAntiOperator (GraphSobolevCompletion n) ↦ T u v)
      (discriminantHardStageOperator_eq_weightedHard N n)
  simp only [ContinuousLinearMap.sub_apply]
  rw [hhard]
  simp only [weightedGraphOperator, LinearMap.mkContinuous₂_apply,
    weightedGraphLinear, lpInfinityMultiplier_apply]
  rw [← inner_sub_right]
  congr 2
  apply Lp.ext
  filter_upwards [
    coeFn_discriminantFullCarrierWeightLp,
    coeFn_discriminantTailCarrierWeightLp N,
    coeFn_discriminantHardCarrierWeightLp N,
    MeasureTheory.Lp.coeFn_lpSMul discriminantFullCarrierWeightLp
      (graphEuclideanBase n u),
    MeasureTheory.Lp.coeFn_lpSMul (discriminantTailCarrierWeightLp N)
      (graphEuclideanBase n u)] with z hfull htail hhardWeight hfullmul htailmul
  rw [hfullmul, htailmul, hfull, htail, hhardWeight,
    discriminantFull_eq_hard_add_tail]
  ring
'''

CANDIDATES: dict[str, str] = {
    "01": WEIGHTED_HELPER + r'''
/-- Pointwise splitting of full multiplication into hard and tail parts,
lifted to the graph weak anti-operator. -/
theorem weightedFull_sub_weightedHard_eq_weightedTail
    (N : ℕ) (n : ℤ) :
    weightedGraphOperator n discriminantFullCarrierWeightLp -
      discriminantHardStageOperator N n =
    weightedGraphOperator n (discriminantTailCarrierWeightLp N) := by
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  have hhard := congrArg
    (fun T : WeakAntiOperator (GraphSobolevCompletion n) ↦ T u v)
    (discriminantHardStageOperator_eq_weightedHard N n)
  have hweighted := congrArg
    (fun T : WeakAntiOperator (GraphSobolevCompletion n) ↦ T u v)
    (weightedFull_sub_weightedHardCarrier_eq_weightedTail N n)
  simpa only [ContinuousLinearMap.sub_apply, hhard] using hweighted
''',
    "02": WEIGHTED_HELPER + r'''
/-- Pointwise splitting of full multiplication into hard and tail parts,
lifted to the graph weak anti-operator. -/
theorem weightedFull_sub_weightedHard_eq_weightedTail
    (N : ℕ) (n : ℤ) :
    weightedGraphOperator n discriminantFullCarrierWeightLp -
      discriminantHardStageOperator N n =
    weightedGraphOperator n (discriminantTailCarrierWeightLp N) := by
  calc
    weightedGraphOperator n discriminantFullCarrierWeightLp -
        discriminantHardStageOperator N n =
      weightedGraphOperator n discriminantFullCarrierWeightLp -
        weightedGraphOperator n (discriminantHardCarrierWeightLp N) :=
      congrArg
        (fun T : WeakAntiOperator (GraphSobolevCompletion n) ↦
          weightedGraphOperator n discriminantFullCarrierWeightLp - T)
        (discriminantHardStageOperator_eq_weightedHard N n)
    _ = weightedGraphOperator n (discriminantTailCarrierWeightLp N) :=
      weightedFull_sub_weightedHardCarrier_eq_weightedTail N n
''',
    "03": DIRECT_SCALAR_BODY,
    "04": WEIGHTED_HELPER + r'''
/-- Scalar application of the hard-stage operator identity, frozen before the
subtraction theorem is elaborated. -/
theorem discriminantHardStageOperator_apply_apply_eq_weightedHard
    (N : ℕ) (n : ℤ) (u v : GraphSobolevCompletion n) :
    discriminantHardStageOperator N n u v =
      weightedGraphOperator n (discriminantHardCarrierWeightLp N) u v :=
  congrArg
    (fun T : WeakAntiOperator (GraphSobolevCompletion n) ↦ T u v)
    (discriminantHardStageOperator_eq_weightedHard N n)

/-- Pointwise splitting of full multiplication into hard and tail parts,
lifted to the graph weak anti-operator. -/
theorem weightedFull_sub_weightedHard_eq_weightedTail
    (N : ℕ) (n : ℤ) :
    weightedGraphOperator n discriminantFullCarrierWeightLp -
      discriminantHardStageOperator N n =
    weightedGraphOperator n (discriminantTailCarrierWeightLp N) := by
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  have hweighted := congrArg
    (fun T : WeakAntiOperator (GraphSobolevCompletion n) ↦ T u v)
    (weightedFull_sub_weightedHardCarrier_eq_weightedTail N n)
  simpa only [ContinuousLinearMap.sub_apply,
    discriminantHardStageOperator_apply_apply_eq_weightedHard] using hweighted
''',
    "05": WEIGHTED_HELPER + r'''
/-- Pointwise splitting of full multiplication into hard and tail parts,
lifted to the graph weak anti-operator. -/
theorem weightedFull_sub_weightedHard_eq_weightedTail
    (N : ℕ) (n : ℤ) :
    weightedGraphOperator n discriminantFullCarrierWeightLp -
      discriminantHardStageOperator N n =
    weightedGraphOperator n (discriminantTailCarrierWeightLp N) := by
  have hhard : discriminantHardStageOperator N n =
      weightedGraphOperator n (discriminantHardCarrierWeightLp N) :=
    discriminantHardStageOperator_eq_weightedHard N n
  have hreplace :
      weightedGraphOperator n discriminantFullCarrierWeightLp -
          discriminantHardStageOperator N n =
        weightedGraphOperator n discriminantFullCarrierWeightLp -
          weightedGraphOperator n (discriminantHardCarrierWeightLp N) :=
    congrArg
      (fun T : WeakAntiOperator (GraphSobolevCompletion n) ↦
        weightedGraphOperator n discriminantFullCarrierWeightLp - T)
      hhard
  exact hreplace.trans
    (weightedFull_sub_weightedHardCarrier_eq_weightedTail N n)
''',
    "06": WEIGHTED_HELPER + r'''
/-- Pointwise splitting of full multiplication into hard and tail parts,
lifted to the graph weak anti-operator. -/
theorem weightedFull_sub_weightedHard_eq_weightedTail
    (N : ℕ) (n : ℤ) :
    weightedGraphOperator n discriminantFullCarrierWeightLp -
      discriminantHardStageOperator N n =
    weightedGraphOperator n (discriminantTailCarrierWeightLp N) := by
  refine continuous_sesquilinear_ext_of_dense
    (weightedGraphOperator n discriminantFullCarrierWeightLp -
      discriminantHardStageOperator N n)
    (weightedGraphOperator n (discriminantTailCarrierWeightLp N))
    (D := Set.univ) dense_univ ?_
  intro u _ v _
  have hhard := congrArg
    (fun T : WeakAntiOperator (GraphSobolevCompletion n) ↦ T u v)
    (discriminantHardStageOperator_eq_weightedHard N n)
  have hweighted := congrArg
    (fun T : WeakAntiOperator (GraphSobolevCompletion n) ↦ T u v)
    (weightedFull_sub_weightedHardCarrier_eq_weightedTail N n)
  simpa only [ContinuousLinearMap.sub_apply, hhard] using hweighted
''',
    "07": WEIGHTED_HELPER + r'''
/-- Pointwise splitting of full multiplication into hard and tail parts,
lifted to the graph weak anti-operator. -/
theorem weightedFull_sub_weightedHard_eq_weightedTail
    (N : ℕ) (n : ℤ) :
    weightedGraphOperator n discriminantFullCarrierWeightLp -
      discriminantHardStageOperator N n =
    weightedGraphOperator n (discriminantTailCarrierWeightLp N) := by
  refine continuous_sesquilinear_ext_of_dense
    (weightedGraphOperator n discriminantFullCarrierWeightLp -
      discriminantHardStageOperator N n)
    (weightedGraphOperator n (discriminantTailCarrierWeightLp N))
    (D := Set.range (coreMap n)) (denseRange_coreMap n) ?_
  rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
  have hhard := congrArg
    (fun T : WeakAntiOperator (GraphSobolevCompletion n) ↦
      T (coreMap n u) (coreMap n v))
    (discriminantHardStageOperator_eq_weightedHard N n)
  have hweighted := congrArg
    (fun T : WeakAntiOperator (GraphSobolevCompletion n) ↦
      T (coreMap n u) (coreMap n v))
    (weightedFull_sub_weightedHardCarrier_eq_weightedTail N n)
  simpa only [ContinuousLinearMap.sub_apply, hhard] using hweighted
''',
    "08": WEIGHTED_HELPER + r'''
/-- Pointwise splitting of full multiplication into hard and tail parts,
lifted to the graph weak anti-operator. -/
theorem weightedFull_sub_weightedHard_eq_weightedTail
    (N : ℕ) (n : ℤ) :
    weightedGraphOperator n discriminantFullCarrierWeightLp -
      discriminantHardStageOperator N n =
    weightedGraphOperator n (discriminantTailCarrierWeightLp N) := by
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.sub_apply]
  rw [show discriminantHardStageOperator N n u v =
      weightedGraphOperator n (discriminantHardCarrierWeightLp N) u v from
    congrArg
      (fun T : WeakAntiOperator (GraphSobolevCompletion n) ↦ T u v)
      (discriminantHardStageOperator_eq_weightedHard N n)]
  exact congrArg
    (fun T : WeakAntiOperator (GraphSobolevCompletion n) ↦ T u v)
    (weightedFull_sub_weightedHardCarrier_eq_weightedTail N n)
''',
    "09": WEIGHTED_HELPER + r'''
/-- Pointwise splitting of full multiplication into hard and tail parts,
lifted to the graph weak anti-operator. -/
theorem weightedFull_sub_weightedHard_eq_weightedTail
    (N : ℕ) (n : ℤ) :
    weightedGraphOperator n discriminantFullCarrierWeightLp -
      discriminantHardStageOperator N n =
    weightedGraphOperator n (discriminantTailCarrierWeightLp N) := by
  let A : WeakAntiOperator (GraphSobolevCompletion n) :=
    weightedGraphOperator n discriminantFullCarrierWeightLp
  let H : WeakAntiOperator (GraphSobolevCompletion n) :=
    discriminantHardStageOperator N n
  let W : WeakAntiOperator (GraphSobolevCompletion n) :=
    weightedGraphOperator n (discriminantHardCarrierWeightLp N)
  let T : WeakAntiOperator (GraphSobolevCompletion n) :=
    weightedGraphOperator n (discriminantTailCarrierWeightLp N)
  have hHW : H = W := by
    simpa only [H, W] using discriminantHardStageOperator_eq_weightedHard N n
  have hAWT : A - W = T := by
    simpa only [A, W, T] using
      weightedFull_sub_weightedHardCarrier_eq_weightedTail N n
  change A - H = T
  exact (congrArg (fun X : WeakAntiOperator (GraphSobolevCompletion n) ↦ A - X)
    hHW).trans hAWT
''',
    "10": WEIGHTED_HELPER + r'''
/-- Pointwise splitting of full multiplication into hard and tail parts,
lifted to the graph weak anti-operator. -/
theorem weightedFull_sub_weightedHard_eq_weightedTail
    (N : ℕ) (n : ℤ) :
    weightedGraphOperator n discriminantFullCarrierWeightLp -
      discriminantHardStageOperator N n =
    weightedGraphOperator n (discriminantTailCarrierWeightLp N) := by
  have hhard := discriminantHardStageOperator_eq_weightedHard N n
  have hweighted := weightedFull_sub_weightedHardCarrier_eq_weightedTail N n
  exact Eq.trans
    (congrArg
      (fun T : WeakAntiOperator (GraphSobolevCompletion n) ↦
        weightedGraphOperator n discriminantFullCarrierWeightLp - T)
      hhard)
    hweighted
''',
    "11": WEIGHTED_HELPER + r'''
/-- Pointwise splitting of full multiplication into hard and tail parts,
lifted to the graph weak anti-operator. -/
theorem weightedFull_sub_weightedHard_eq_weightedTail
    (N : ℕ) (n : ℤ) :
    weightedGraphOperator n discriminantFullCarrierWeightLp -
      discriminantHardStageOperator N n =
    weightedGraphOperator n (discriminantTailCarrierWeightLp N) := by
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  have hhard := DFunLike.congr_fun
    (DFunLike.congr_fun
      (discriminantHardStageOperator_eq_weightedHard N n) u) v
  have hweighted := DFunLike.congr_fun
    (DFunLike.congr_fun
      (weightedFull_sub_weightedHardCarrier_eq_weightedTail N n) u) v
  simpa only [ContinuousLinearMap.sub_apply, hhard] using hweighted
''',
    "12": WEIGHTED_HELPER + r'''
/-- Pointwise splitting of full multiplication into hard and tail parts,
lifted to the graph weak anti-operator. -/
theorem weightedFull_sub_weightedHard_eq_weightedTail
    (N : ℕ) (n : ℤ) :
    weightedGraphOperator n discriminantFullCarrierWeightLp -
      discriminantHardStageOperator N n =
    weightedGraphOperator n (discriminantTailCarrierWeightLp N) := by
  have hreplace := congrArg
    (fun T : WeakAntiOperator (GraphSobolevCompletion n) ↦
      weightedGraphOperator n discriminantFullCarrierWeightLp - T)
    (discriminantHardStageOperator_eq_weightedHard N n)
  apply hreplace.trans
  exact weightedFull_sub_weightedHardCarrier_eq_weightedTail N n
''',
}


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def load_source() -> tuple[bytes, str]:
    data = SOURCE.read_bytes()
    actual = sha256(data)
    if actual != EXPECTED_SOURCE_SHA256:
        raise SystemExit(
            f"source identity mismatch: expected {EXPECTED_SOURCE_SHA256}, got {actual}"
        )
    text = data.decode("utf-8")
    if text.count(START_MARKER) != 1 or text.count(END_MARKER) != 1:
        raise SystemExit("target markers are not unique")
    return data, text


def generate() -> None:
    data, text = load_source()
    start = text.index(START_MARKER)
    prefix = text[:start].rstrip() + POSTAMBLE
    PREFIX_PATH.write_text(prefix, encoding="utf-8")
    CANDIDATE_DIR.mkdir(parents=True, exist_ok=True)
    rows = []
    for cid, block in sorted(CANDIDATES.items()):
        path = CANDIDATE_DIR / f"Candidate{cid}.lean"
        payload = PREAMBLE + block.rstrip() + POSTAMBLE
        path.write_text(payload, encoding="utf-8")
        rows.append(
            {
                "candidate_id": cid,
                "path": str(path),
                "strategy_sha256": sha256(block.encode("utf-8")),
                "bytes": len(payload.encode("utf-8")),
                "lines": len(payload.splitlines()),
            }
        )
    manifest = {
        "schema": "fa-primary4016-reproducer-v1",
        "source_sha256": sha256(data),
        "prefix_path": str(PREFIX_PATH),
        "prefix_sha256": sha256(PREFIX_PATH.read_bytes()),
        "candidate_count": len(rows),
        "candidates": rows,
    }
    print(json.dumps(manifest, indent=2, ensure_ascii=False))


def materialize(candidate_id: str, output: Path) -> None:
    _, text = load_source()
    try:
        block = CANDIDATES[candidate_id]
    except KeyError as exc:
        raise SystemExit(f"unknown candidate id: {candidate_id}") from exc
    start = text.index(START_MARKER)
    end = text.index(END_MARKER, start)
    patched = text[:start] + block.rstrip() + "\n\n" + text[end:]
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(patched, encoding="utf-8")
    print(
        json.dumps(
            {
                "candidate_id": candidate_id,
                "input_sha256": EXPECTED_SOURCE_SHA256,
                "output_path": str(output),
                "output_sha256": sha256(output.read_bytes()),
                "theorem_statements_changed": False,
                "forbidden_constructs_added": False,
            },
            indent=2,
        )
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--materialize", metavar="ID")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.materialize:
        if args.output is None:
            parser.error("--output is required with --materialize")
        materialize(args.materialize, args.output)
    else:
        generate()


if __name__ == "__main__":
    main()
