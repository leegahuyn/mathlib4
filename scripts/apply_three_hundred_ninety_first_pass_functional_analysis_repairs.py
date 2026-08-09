from __future__ import annotations

from hashlib import sha256
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
EXPECTED_INPUT_SHA256 = "5f2d7615aaad7bb3a232d19829f0f801278e7ab2fa2f66ccb68408b87647e620"
EXPECTED_OUTPUT_SHA256 = "fd3ef32488c4d7de11f7adac75dd9a04ec48734277fc071e6e99662bc48790d9"


def digest(path: Path) -> str:
    return sha256(path.read_bytes()).hexdigest()


def replace_exact(text: str, old: str, new: str, label: str) -> str:
    count = text.count(old)
    print(f"{label}: expected=1 actual={count}")
    if count != 1:
        raise RuntimeError(f"{label}: expected one occurrence, found {count}")
    return text.replace(old, new)


def main() -> int:
    before = digest(TARGET)
    print(f"input_sha256={before}")
    if before == EXPECTED_OUTPUT_SHA256:
        print("[pass391] already applied")
        return 0
    if before != EXPECTED_INPUT_SHA256:
        raise RuntimeError(
            f"unexpected PASS391 input SHA-256: {before}; expected {EXPECTED_INPUT_SHA256}"
        )

    text = TARGET.read_text(encoding="utf-8")
    replacements = [
        (
            """theorem norm_baseExtension_le_one : ‖Q.baseExtension‖ ≤ 1 := by
  letI : NormedSpace ℂ Q.SobolevCompletion :=
    UniformSpace.Completion.instNormedSpace ℂ Q.GraphRange
  exact Q.baseExtension.opNorm_le_bound zero_le_one fun x => by
    simpa only [one_mul] using Q.norm_baseExtension_le x
""",
            """theorem norm_baseExtension_le_one : ‖Q.baseExtension‖ ≤ 1 := by
  exact Q.baseExtension.opNorm_le_bound zero_le_one fun x => by
    simpa only [one_mul] using Q.norm_baseExtension_le x
""",
            "remove duplicate completion NormedSpace in base bound",
        ),
        (
            """theorem norm_raiseExtension_le_one : ‖Q.raiseExtension‖ ≤ 1 := by
  letI : NormedSpace ℂ Q.SobolevCompletion :=
    UniformSpace.Completion.instNormedSpace ℂ Q.GraphRange
  exact Q.raiseExtension.opNorm_le_bound zero_le_one fun x => by
    simpa only [one_mul] using Q.norm_raiseExtension_le x
""",
            """theorem norm_raiseExtension_le_one : ‖Q.raiseExtension‖ ≤ 1 := by
  exact Q.raiseExtension.opNorm_le_bound zero_le_one fun x => by
    simpa only [one_mul] using Q.norm_raiseExtension_le x
""",
            "remove duplicate completion NormedSpace in raising bound",
        ),
        (
            """theorem norm_lowerExtension_le_one : ‖Q.lowerExtension‖ ≤ 1 := by
  letI : NormedSpace ℂ Q.SobolevCompletion :=
    UniformSpace.Completion.instNormedSpace ℂ Q.GraphRange
  exact Q.lowerExtension.opNorm_le_bound zero_le_one fun x => by
    simpa only [one_mul] using Q.norm_lowerExtension_le x
""",
            """theorem norm_lowerExtension_le_one : ‖Q.lowerExtension‖ ≤ 1 := by
  exact Q.lowerExtension.opNorm_le_bound zero_le_one fun x => by
    simpa only [one_mul] using Q.norm_lowerExtension_le x
""",
            "remove duplicate completion NormedSpace in lowering bound",
        ),
        (
            """noncomputable def completionEnergyOperator :
    WeakAntiOperator Q.SobolevCompletion := by
  letI : NormedSpace ℂ Q.SobolevCompletion :=
    UniformSpace.Completion.instNormedSpace ℂ Q.GraphRange
  exact innerSLFlip ℂ
""",
            """noncomputable def completionEnergyOperator :
    WeakAntiOperator Q.SobolevCompletion :=
  innerSLFlip ℂ
""",
            "use canonical completion inner-product instances",
        ),
        (
            """theorem completionEnergyOperator_apply (u v : Q.SobolevCompletion) :
    Q.completionEnergyOperator u v = ⟪v, u⟫_ℂ :=
  innerSLFlip_apply_apply ℂ u v
""",
            """theorem completionEnergyOperator_apply (u v : Q.SobolevCompletion) :
    Q.completionEnergyOperator u v = ⟪v, u⟫_ℂ := by
  change innerSLFlip ℂ u v = ⟪v, u⟫_ℂ
  exact innerSLFlip_apply_apply ℂ u v
""",
            "expose the typed completion innerSLFlip",
        ),
        (
            """  rw [Q.completionEnergyOperator_apply]
  change ⟪Q.coreEmbedding (Q.toGraphRange v),
      Q.coreEmbedding (Q.toGraphRange u)⟫_ℂ = Q.energyForm v u
  rw [Q.coreEmbedding.inner_map_map, Q.inner_toGraphRange]
""",
            """  rw [Q.completionEnergyOperator_apply]
  change ⟪(Q.toGraphRange v : Q.SobolevCompletion),
      (Q.toGraphRange u : Q.SobolevCompletion)⟫_ℂ = Q.energyForm v u
  rw [UniformSpace.Completion.inner_coe, Q.inner_toGraphRange]
""",
            "evaluate the completion pairing through inner_coe",
        ),
        (
            """  FredholmBypass.coerciveForm_injective
    1 Q.completionEnergyOperator Q.completionEnergyOperator_coercive
""",
            """  FredholmBypass.coerciveForm_injective
    (V := Q.SobolevCompletion)
    1 Q.completionEnergyOperator Q.completionEnergyOperator_coercive
""",
            "pin the injectivity carrier",
        ),
        (
            """  FredholmBypass.coerciveForm_surjective
    1 Q.completionEnergyOperator Q.completionEnergyOperator_coercive
""",
            """  FredholmBypass.coerciveForm_surjective
    (V := Q.SobolevCompletion)
    1 Q.completionEnergyOperator Q.completionEnergyOperator_coercive
""",
            "pin the surjectivity carrier",
        ),
        (
            """  FredholmBypass.coerciveFormEquiv
    1 Q.completionEnergyOperator Q.completionEnergyOperator_coercive
""",
            """  FredholmBypass.coerciveFormEquiv
    (V := Q.SobolevCompletion)
    1 Q.completionEnergyOperator Q.completionEnergyOperator_coercive
""",
            "pin the coercive equivalence carrier",
        ),
        (
            """theorem completionEnergyEquiv_apply (u : Q.SobolevCompletion) :
    Q.completionEnergyEquiv u = Q.completionEnergyOperator u :=
  rfl
""",
            """theorem completionEnergyEquiv_apply (u : Q.SobolevCompletion) :
    Q.completionEnergyEquiv u = Q.completionEnergyOperator u := by
  exact FredholmBypass.coerciveFormEquiv_apply
    (V := Q.SobolevCompletion)
    1 Q.completionEnergyOperator Q.completionEnergyOperator_coercive u
""",
            "use the public coercive equivalence application lemma",
        ),
        (
            """  change Q.completionEnergyEquiv
    (Q.completionEnergyEquiv.symm F) = F
  exact Q.completionEnergyEquiv.apply_symm_apply F
""",
            """  rw [← Q.completionEnergyEquiv_apply]
  exact Q.completionEnergyEquiv.apply_symm_apply F
""",
            "transport the solved equation through the equivalence lemma",
        ),
        (
            """    (FredholmBypass.coerciveFormEquiv_symm_norm_le
      1 Q.completionEnergyOperator
      Q.completionEnergyOperator_coercive F)
""",
            """    (FredholmBypass.coerciveFormEquiv_symm_norm_le
      (V := Q.SobolevCompletion)
      1 Q.completionEnergyOperator
      Q.completionEnergyOperator_coercive F)
""",
            "pin the inverse norm estimate carrier",
        ),
    ]

    for old, new, label in replacements:
        text = replace_exact(text, old, new, label)

    TARGET.write_text(text, encoding="utf-8")
    after = digest(TARGET)
    print(f"output_sha256={after}")
    if after != EXPECTED_OUTPUT_SHA256:
        raise RuntimeError(
            f"unexpected PASS391 output SHA-256: {after}; expected {EXPECTED_OUTPUT_SHA256}"
        )
    print("[pass391] completion instance coherence and coercive-equivalence roots repaired")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
