from __future__ import annotations

import re
from pathlib import Path

PATH = Path("PrimalitySheafVerification/Mock1_Advanced.lean")


def replace_once(text: str, old: str, new: str, label: str) -> tuple[str, bool]:
    count = text.count(old)
    if count == 0:
        print(f"{label}: already applied or source changed")
        return text, False
    if count != 1:
        raise RuntimeError(f"{label}: expected one match, found {count}")
    print(f"{label}: applied")
    return text.replace(old, new), True


def main() -> int:
    text = PATH.read_text(encoding="utf-8")
    changed = False

    text, c = replace_once(
        text,
        """structure MultiplierCharacter where
  value : ModularMatrix -> Complex
  value_T : Complex := value ModularMatrix.T
  value_S : Complex := value ModularMatrix.S
""",
        """structure MultiplierCharacter where
  value : ModularMatrix -> Complex
  value_T : Complex := value ModularMatrix.T
  value_S : Complex := value ModularMatrix.S
  value_T_spec : value_T = value ModularMatrix.T := by rfl
  value_S_spec : value_S = value ModularMatrix.S := by rfl
""",
        "Mock1Advanced make multiplier cached values coherent",
    )
    changed |= c

    text, c = replace_once(
        text,
        """theorem value_T_eq (chi : MultiplierCharacter) :
    chi.value_T = chi.value ModularMatrix.T := rfl

 theorem value_S_eq""".replace("\n theorem", "\ntheorem"),
        """theorem value_T_eq (chi : MultiplierCharacter) :
    chi.value_T = chi.value ModularMatrix.T :=
  chi.value_T_spec

theorem value_S_eq""",
        "Mock1Advanced multiplier T theorem",
    )
    changed |= c

    text, c = replace_once(
        text,
        """theorem value_S_eq (chi : MultiplierCharacter) :
    chi.value_S = chi.value ModularMatrix.S := rfl
""",
        """theorem value_S_eq (chi : MultiplierCharacter) :
    chi.value_S = chi.value ModularMatrix.S :=
  chi.value_S_spec
""",
        "Mock1Advanced multiplier S theorem",
    )
    changed |= c

    text, c = replace_once(
        text,
        """theorem symm {M a b : Nat} (h : NatCongruent M a b) :
    NatCongruent M b a := by
  exact h.symm

 theorem trans""".replace("\n theorem", "\ntheorem"),
        """theorem symm {M a b : Nat} (h : NatCongruent M a b) :
    NatCongruent M b a := by
  unfold NatCongruent at h ⊢
  exact Eq.symm h

theorem trans""",
        "Mock1Advanced NatCongruent symmetry",
    )
    changed |= c

    text, c = replace_once(
        text,
        """theorem trans {M a b c : Nat} (hab : NatCongruent M a b)
    (hbc : NatCongruent M b c) : NatCongruent M a c := by
  exact hab.trans hbc
""",
        """theorem trans {M a b c : Nat} (hab : NatCongruent M a b)
    (hbc : NatCongruent M b c) : NatCongruent M a c := by
  unfold NatCongruent at hab hbc ⊢
  exact Eq.trans hab hbc
""",
        "Mock1Advanced NatCongruent transitivity",
    )
    changed |= c

    text, c = replace_once(
        text,
        """theorem arithmeticEqualizer_iff_lcm_dvd (M N x : Nat) :
    ArithmeticEqualizer M N x <-> Dvd.dvd (Nat.lcm M N) x := by
  constructor
  next h =>
    exact Nat.lcm_dvd h.1 h.2
  next h =>
    exact And.intro (dvd_trans (Nat.dvd_lcm_left M N) h)
      (dvd_trans (Nat.dvd_lcm_right M N) h)
""",
        """theorem arithmeticEqualizer_iff_lcm_dvd (M N x : Nat) :
    ArithmeticEqualizer M N x <-> Dvd.dvd (Nat.lcm M N) x := by
  constructor
  · rintro ⟨hM, hN⟩
    exact Nat.lcm_dvd hM hN
  · intro h
    exact And.intro (dvd_trans (Nat.dvd_lcm_left M N) h)
      (dvd_trans (Nat.dvd_lcm_right M N) h)
""",
        "Mock1Advanced arithmetic equalizer cases",
    )
    changed |= c

    text, c = replace_once(
        text,
        """theorem symm {M N a b : Nat} (h : PairCompatible M N a b) :
    PairCompatible M N b a := by
  exact h.symm
""",
        """theorem symm {M N a b : Nat} (h : PairCompatible M N a b) :
    PairCompatible M N b a := by
  unfold PairCompatible at h ⊢
  exact Eq.symm h
""",
        "Mock1Advanced pair compatibility symmetry",
    )
    changed |= c

    text, c = replace_once(
        text,
        """theorem of_gcd_eq_one {M N a b : Nat} (h : Nat.gcd M N = 1) :
    PairCompatible M N a b := by
  simp [PairCompatible, h]
""",
        """theorem of_gcd_eq_one {M N a b : Nat} (h : Nat.gcd M N = 1) :
    PairCompatible M N a b := by
  unfold PairCompatible
  rw [h]
  simp
""",
        "Mock1Advanced gcd-one compatibility",
    )
    changed |= c

    text2, n = re.subn(r"(?m)^(\s*)matches\s*:", r"\1matches_target :", text)
    if n:
        print(f"Mock1Advanced reserved matches fields: renamed {n}")
        text, changed = text2, True
    text2, n = re.subn(r"(?m)^(\s*)matches\s*:=", r"\1matches_target :=", text)
    if n:
        print(f"Mock1Advanced reserved matches constructors: renamed {n}")
        text, changed = text2, True
    text2, n = re.subn(r"\.matches\b", ".matches_target", text)
    if n:
        print(f"Mock1Advanced reserved matches projections: renamed {n}")
        text, changed = text2, True

    text, c = replace_once(
        text,
        """    (h.sub h').congr (fun n => by
      simp [EntropyGrowth, EntropyModel]
      ring)
""",
        """    (h.sub h').congr (fun n => by
      simp [EntropyGrowth, EntropyModel])
""",
        "Mock1Advanced remove tactic after simp closes entropy goal",
    )
    changed |= c

    text, c = replace_once(
        text,
        """  rademacher_tail_envelope_nonneg := C.rademacher_tail_envelope_nonneg
""",
        """  rademacher_tail_envelope_nonneg := by
    intro n
    exact mul_nonneg C.rademacherWitness.tail.C_nonneg (Real.exp_pos _).le
""",
        "Mock1Advanced prove real tail envelope directly",
    )
    changed |= c

    text, c = replace_once(
        text,
        """theorem mem_all (key : RequirementKey) :
    List.Mem key all := by
  cases key <;> simp [all]
""",
        """theorem mem_all (key : RequirementKey) :
    List.Mem key all := by
  cases key <;> decide
""",
        "Mock1Advanced decide finite requirement membership",
    )
    changed |= c

    text, c = replace_once(
        text,
        """def referenceQSeriesEntropyAsymptotic :
    EntropyAsymptoticCertificate referenceQSeries.coeff where
  alpha := 1
  beta := 0
  tendsto_form := by
    simpa [referenceQSeries, referenceObject] using exactEntropyCoeff_growth 1 0
  epsilonN_form := by
    simpa [referenceQSeries, referenceObject] using
      exactEntropyCoeff_growth_epsilonN 1 0
  littleO_one_form := by
    exact
      (entropyGrowthLittleOOne_iff_epsilonN referenceQSeries.coeff 1 0).mpr
        (by
          simpa [referenceQSeries, referenceObject] using
            exactEntropyCoeff_growth_epsilonN 1 0)
""",
        """def referenceQSeriesEntropyAsymptotic :
    EntropyAsymptoticCertificate referenceQSeries.coeff := by
  simpa [referenceQSeries] using referenceEntropyAsymptotic
""",
        "Mock1Advanced reuse the reference entropy certificate",
    )
    changed |= c

    text, c = replace_once(
        text,
        """def referenceQSeriesRademacherExpansion :
    RademacherExpansionCertificate referenceQSeries.coeff where
  expansion := referenceRademacherExpansionData
  cutoff := fun _ => 1
  remainder := fun _ => 0
  coeff_eq_truncation := by
    intro n
    simp [referenceQSeries, referenceRademacherExpansionData,
      RademacherExpansionData.truncation]
  tail := referenceExponentialTail
  tail_eq_remainder := rfl
""",
        """def referenceQSeriesRademacherExpansion :
    RademacherExpansionCertificate referenceQSeries.coeff := by
  simpa [referenceQSeries] using referenceRademacherExpansion
""",
        "Mock1Advanced reuse the reference Rademacher certificate",
    )
    changed |= c

    text2, n = re.subn(
        r"(theorem coverage_targets_[A-Za-z0-9_']+\s*:[\s\S]*?\s*:= by)\n  simp \[targets\]",
        r"\1\n  decide",
        text,
    )
    if n:
        print(f"Mock1Advanced closed audit target membership: changed {n}")
        text, changed = text2, True

    if changed:
        PATH.write_text(text, encoding="utf-8", newline="\n")
        print("Mock1 advanced first-pass repairs changed source.")
    else:
        print("No Mock1 advanced first-pass changes needed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
