from __future__ import annotations

from hashlib import sha256
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
EXPECTED_INPUT_SHA256 = "d9bce9ec296c799fe144786111da5a6e8f7f0232f55fd34df9cf09be8b140b4e"
EXPECTED_OUTPUT_SHA256 = "c562c864be74e94e618ad3ad54dd7ee6442f81d17bc748754782718f4f7ca0e0"


def digest(text: str) -> str:
    return sha256(text.encode("utf-8")).hexdigest()


def replace_exact(
    text: str,
    old: str,
    new: str,
    label: str,
    expected: int = 1,
) -> str:
    count = text.count(old)
    print(f"{label}: expected={expected} actual={count}")
    if count != expected:
        raise RuntimeError(
            f"{label}: expected {expected} occurrence(s), found {count}"
        )
    return text.replace(old, new)


def replace_final_ring(
    text: str,
    theorem_name: str,
    label: str,
) -> str:
    marker = f"theorem {theorem_name}"
    start = text.index(marker)
    end = text.index("\n/--", start + len(marker))
    block = text[start:end]
    count = block.count("  ring\n")
    print(f"{label}: expected=1 actual={count}")
    if count != 1:
        raise RuntimeError(f"{label}: expected one final ring, found {count}")
    repaired = block.replace("  ring\n", "  ring_nf\n")
    return text[:start] + repaired + text[end:]


def main() -> int:
    text = TARGET.read_text(encoding="utf-8")
    input_sha = digest(text)
    print(f"input_sha256={input_sha}")
    if input_sha == EXPECTED_OUTPUT_SHA256:
        print("[pass342] already applied")
        return 0
    if input_sha != EXPECTED_INPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass342 input sha256: {input_sha}; "
            f"expected {EXPECTED_INPUT_SHA256}"
        )

    text = replace_exact(
        text,
        """/- `InverseEtaFixedPhaseCore` is definitionally the subtype of the stable
submodule. Re-expose exactly the canonical subtype instances so the opaque
abbreviation elaborates while retaining definitional compatibility with the
previously constructed core maps. -/
noncomputable local instance fixedPhaseGraphCoreAddCommGroup (n : ℤ) :
    AddCommGroup (InverseEtaFixedPhaseCore n) := by
  change AddCommGroup ↥(inverseEtaFixedPhaseStableCoreSubmodule n)
  exact inferInstanceAs
    (AddCommGroup ↥(inverseEtaFixedPhaseStableCoreSubmodule n))

noncomputable local instance fixedPhaseGraphCoreModule (n : ℤ) :
    Module ℂ (InverseEtaFixedPhaseCore n) := by
  change Module ℂ ↥(inverseEtaFixedPhaseStableCoreSubmodule n)
  exact inferInstanceAs
    (Module ℂ ↥(inverseEtaFixedPhaseStableCoreSubmodule n))
""",
        """/- The stable core was defined while its ambient function space exposed only
an additive monoid instance. Repackage the same carrier as an additive
subgroup, then rebuild the compatible complex-module laws on that carrier. -/
private noncomputable def fixedPhaseGraphCoreAddSubgroup (n : ℤ) :
    AddSubgroup SmoothQuotientCompactFunction where
  carrier := inverseEtaFixedPhaseStableCoreSubmodule n
  zero_mem' := (inverseEtaFixedPhaseStableCoreSubmodule n).zero_mem
  add_mem' := by
    intro x y hx hy
    exact (inverseEtaFixedPhaseStableCoreSubmodule n).add_mem hx hy
  neg_mem' := by
    intro x hx
    have h :=
      (inverseEtaFixedPhaseStableCoreSubmodule n).smul_mem (-1 : ℂ) hx
    simpa only [neg_one_smul] using h

noncomputable local instance fixedPhaseGraphCoreAddCommGroup (n : ℤ) :
    AddCommGroup (InverseEtaFixedPhaseCore n) := by
  let S := fixedPhaseGraphCoreAddSubgroup n
  change AddCommGroup ↥S
  exact S.toAddCommGroup

noncomputable local instance fixedPhaseGraphCoreModule (n : ℤ) :
    Module ℂ (InverseEtaFixedPhaseCore n) where
  one_smul x := by
    apply Subtype.ext
    simp
  mul_smul a b x := by
    apply Subtype.ext
    simp [mul_smul]
  smul_zero a := by
    apply Subtype.ext
    simp
  smul_add a x y := by
    apply Subtype.ext
    simp [smul_add]
  add_smul a b x := by
    apply Subtype.ext
    simp [add_smul]
  zero_smul x := by
    apply Subtype.ext
    simp
""",
        "graph stable-core group and module",
    )

    text = replace_exact(
        text,
        """/- Re-expose the same canonical subtype instances in this namespace. These are
definitionally identical to the instances used by the previously constructed
linear maps, unlike a separately built `Submodule.addCommGroup` family. -/
noncomputable local instance fixedPhaseDensityCoreAddCommGroup (n : ℤ) :
    AddCommGroup (InverseEtaFixedPhaseCore n) := by
  change AddCommGroup ↥(inverseEtaFixedPhaseStableCoreSubmodule n)
  exact inferInstanceAs
    (AddCommGroup ↥(inverseEtaFixedPhaseStableCoreSubmodule n))

noncomputable local instance fixedPhaseDensityCoreModule (n : ℤ) :
    Module ℂ (InverseEtaFixedPhaseCore n) := by
  change Module ℂ ↥(inverseEtaFixedPhaseStableCoreSubmodule n)
  exact inferInstanceAs
    (Module ℂ ↥(inverseEtaFixedPhaseStableCoreSubmodule n))
""",
        """/- Reuse the same carrier repair in the density namespace. -/
private noncomputable def fixedPhaseDensityCoreAddSubgroup (n : ℤ) :
    AddSubgroup SmoothQuotientCompactFunction where
  carrier := inverseEtaFixedPhaseStableCoreSubmodule n
  zero_mem' := (inverseEtaFixedPhaseStableCoreSubmodule n).zero_mem
  add_mem' := by
    intro x y hx hy
    exact (inverseEtaFixedPhaseStableCoreSubmodule n).add_mem hx hy
  neg_mem' := by
    intro x hx
    have h :=
      (inverseEtaFixedPhaseStableCoreSubmodule n).smul_mem (-1 : ℂ) hx
    simpa only [neg_one_smul] using h

noncomputable local instance fixedPhaseDensityCoreAddCommGroup (n : ℤ) :
    AddCommGroup (InverseEtaFixedPhaseCore n) := by
  let S := fixedPhaseDensityCoreAddSubgroup n
  change AddCommGroup ↥S
  exact S.toAddCommGroup

noncomputable local instance fixedPhaseDensityCoreModule (n : ℤ) :
    Module ℂ (InverseEtaFixedPhaseCore n) where
  one_smul x := by
    apply Subtype.ext
    simp
  mul_smul a b x := by
    apply Subtype.ext
    simp [mul_smul]
  smul_zero a := by
    apply Subtype.ext
    simp
  smul_add a x y := by
    apply Subtype.ext
    simp [smul_add]
  add_smul a b x := by
    apply Subtype.ext
    simp [add_smul]
  zero_smul x := by
    apply Subtype.ext
    simp
""",
        "density stable-core group and module",
    )

    text = replace_exact(
        text,
        "rw [← GammaTwoQuotientGeometry.gammaTwoToSL2Real_smul] at hCov",
        "rw [GammaTwoQuotientGeometry.gammaTwoToSL2Real_smul] at hCov",
        "covariance action direction",
        expected=2,
    )

    text = replace_exact(
        text,
        """  exact norm_eq_zero.mpr
    (constantCompactCuspTail_tail_eq_zero C hC n)
""",
        """  calc
    ‖(constantCompactCuspTail C hC).truncation n - C‖ =
        ‖(0 : ContinuousSesquilinearForm H)‖ :=
      congrArg norm (constantCompactCuspTail_tail_eq_zero C hC n)
    _ = 0 :=
      (norm_zero : ‖(0 : ContinuousSesquilinearForm H)‖ = 0)
""",
        "constant compact-tail norm",
    )

    text = replace_exact(
        text,
        """  change
    InverseEtaFixedPhaseCore.raise n (cuspCutoffOperator M n u) -
      cuspCutoffOperator M (n + 1)
        (InverseEtaFixedPhaseCore.raise n u) = 0
  rw [hMu, hMr, sub_self]
""",
        """  simp only [raiseCuspCutoffCommutator, LinearMap.sub_apply,
    LinearMap.comp_apply]
  rw [hMu, hMr, sub_self]
""",
        "raising cutoff commutator",
    )

    text = replace_exact(
        text,
        """  change
    InverseEtaFixedPhaseCore.lower n (cuspCutoffOperator M n u) -
      cuspCutoffOperator M (n - 1)
        (InverseEtaFixedPhaseCore.lower n u) = 0
  rw [hMu, hMl, sub_self]
""",
        """  simp only [lowerCuspCutoffCommutator, LinearMap.sub_apply,
    LinearMap.comp_apply]
  rw [hMu, hMl, sub_self]
""",
        "lowering cutoff commutator",
    )

    text = replace_exact(
        text,
        """noncomputable def hyperbolicDensity (z : ℍ) : NNReal :=
  ((1 : NNReal) / (⟨z.im, z.im_pos.le⟩ : NNReal)) ^ 2

theorem hyperbolicDensity_continuous :
    Continuous hyperbolicDensity := by
  simpa only [hyperbolicDensity] using
    ((continuous_const.div₀
      (UpperHalfPlane.continuous_im.subtype_mk _)
      (fun z => NNReal.ne_iff.mp z.im_ne_zero)).pow 2)
""",
        """noncomputable def hyperbolicDensity (z : ℍ) : NNReal :=
  ⟨(1 / z.im) ^ 2, sq_nonneg _⟩

theorem hyperbolicDensity_continuous :
    Continuous hyperbolicDensity := by
  exact ((continuous_const.div UpperHalfPlane.continuous_im
    (fun z => z.im_ne_zero)).pow 2).subtype_mk _
""",
        "NNReal hyperbolic density and continuity",
    )

    text = replace_exact(
        text,
        """  have hProd :=
    dx_mul (realSmooth_complexHeightRpow (euclideanGaugeExponent n))
      u.1.1.2 z
""",
        """  have huSmooth :
      RealSmooth (((u : SmoothQuotientCompactFunction) : ℍ → ℂ)) :=
    (u : SmoothQuotientCompactFunction).1.2
  have hProd :=
    dx_mul (realSmooth_complexHeightRpow (euclideanGaugeExponent n))
      huSmooth z
""",
        "horizontal derivative coercion",
    )

    text = replace_exact(
        text,
        """  have hProd :=
    dy_mul (realSmooth_complexHeightRpow (euclideanGaugeExponent n))
      u.1.1.2 z
""",
        """  have huSmooth :
      RealSmooth (((u : SmoothQuotientCompactFunction) : ℍ → ℂ)) :=
    (u : SmoothQuotientCompactFunction).1.2
  have hProd :=
    dy_mul (realSmooth_complexHeightRpow (euclideanGaugeExponent n))
      huSmooth z
""",
        "vertical derivative coercion",
    )

    text = replace_final_ring(
        text,
        "fixedPhaseEuclideanGauge_raise",
        "raising gauge ring normalization",
    )
    text = replace_final_ring(
        text,
        "fixedPhaseEuclideanGauge_lowerFromSucc",
        "lowering gauge ring normalization",
    )

    output_sha = digest(text)
    print(f"output_sha256={output_sha}")
    if output_sha != EXPECTED_OUTPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass342 output sha256: {output_sha}; "
            f"expected {EXPECTED_OUTPUT_SHA256}"
        )

    TARGET.write_text(text, encoding="utf-8")
    print(
        "[pass342] stable-core instances, covariance, compact tail, "
        "commutators, NNReal density, and gauge derivatives repaired"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
