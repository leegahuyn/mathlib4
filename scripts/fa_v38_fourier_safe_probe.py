#!/usr/bin/env python3
from pathlib import Path
import hashlib, json, sys

if len(sys.argv) != 3:
    raise SystemExit('usage: fa_v38_fourier_safe_probe.py <v37-source> <out>')
src = Path(sys.argv[1])
out = Path(sys.argv[2])
raw = src.read_bytes()
BASE = 'e17ff90193c6959b15f743ef930446b4cfd45bc6df4d762057c13b4b06602d05'
sha = hashlib.sha256(raw).hexdigest()
assert sha == BASE, (sha, BASE)
s = raw.decode('utf-8')

repls = []
repls.append(('''theorem literalStageFourierScale_pos (Y : ℝ) :
    0 < literalStageFourierScale Y := by
  unfold literalStageFourierScale
  positivity
''','''theorem literalStageFourierScale_pos (Y : ℝ) :
    0 < literalStageFourierScale Y := by
  unfold literalStageFourierScale
  nlinarith [literalStageFourierRadius_pos Y]
'''))
repls.append(('''theorem literalStageFourierBox_measurableSet (Y : ℝ) :
    MeasurableSet (literalStageFourierBox Y) := by
  unfold literalStageFourierBox
  exact MeasurableSet.iInter fun i ↦
    measurableSet_Ioc.preimage
      ((measurable_pi_apply i).comp
        Complex.measurableEquivPi.measurable)
''','''theorem literalStageFourierBox_measurableSet (Y : ℝ) :
    MeasurableSet (literalStageFourierBox Y) := by
  rw [show literalStageFourierBox Y = ⋂ i : Fin 2,
      (fun w : ℂ => Complex.measurableEquivPi w i) ⁻¹'
        Set.Ioc (-(literalStageFourierScale Y / 2))
          (literalStageFourierScale Y / 2) by
    ext w
    simp [literalStageFourierBox]]
  exact MeasurableSet.iInter fun i ↦
    measurableSet_Ioc.preimage
      ((measurable_pi_apply i).comp
        Complex.measurableEquivPi.measurable)
'''))
repls.append(('''  have hcoord : |Complex.measurableEquivPi w i| ≤ ‖w‖ := by
    fin_cases i
    · simpa only [Complex.measurableEquivPi_apply,
        Matrix.cons_val_zero] using Complex.abs_re_le_norm w
    · simpa only [Complex.measurableEquivPi_apply,
        Matrix.cons_val_one, Matrix.head_cons] using
        Complex.abs_im_le_norm w
''','''  have hcoord : |Complex.measurableEquivPi w i| ≤ ‖w‖ := by
    fin_cases i
    · change |w.re| ≤ ‖w‖
      exact Complex.abs_re_le_norm w
    · change |w.im| ≤ ‖w‖
      exact Complex.abs_im_le_norm w
'''))
repls.append(('''      constructor
      · apply (mul_lt_mul_left (literalStageFourierScale_pos Y)).mp
        simpa [x, literalStageFourierScale_ne_zero Y] using hi.1
      · apply (mul_le_mul_left (literalStageFourierScale_pos Y)).mp
        simpa [x, literalStageFourierScale_ne_zero Y] using hi.2
''','''      constructor
      · have h := mul_lt_mul_of_pos_left hi.1
          (inv_pos.mpr (literalStageFourierScale_pos Y))
        simpa [x, literalStageFourierScale_ne_zero Y,
          div_eq_mul_inv, mul_assoc] using h
      · have h := mul_le_mul_of_nonneg_left hi.2
          (inv_pos.mpr (literalStageFourierScale_pos Y)).le
        simpa [x, literalStageFourierScale_ne_zero Y,
          div_eq_mul_inv, mul_assoc] using h
'''))
repls.append(('''    simpa [literalStageFourierScale_pos Y, mul_assoc] using
      (mul_lt_mul_of_pos_left hi.1 (literalStageFourierScale_pos Y)).and
        (mul_le_mul_of_nonneg_left hi.2
          (literalStageFourierScale_pos Y).le)
''','''    constructor
    · have h := mul_lt_mul_of_pos_left hi.1
        (literalStageFourierScale_pos Y)
      simpa [div_eq_mul_inv, mul_assoc] using h
    · have h := mul_le_mul_of_nonneg_left hi.2
        (literalStageFourierScale_pos Y).le
      simpa [div_eq_mul_inv, mul_assoc] using h
'''))
# The same inverse-rescaling root occurs in literalStageTorusPoint_physicalTorusPoint.
repls.append(('''    constructor
    · apply (mul_lt_mul_left (literalStageFourierScale_pos Y)).mp
      simpa [literalStageFourierScale_ne_zero Y] using hi.1
    · apply (mul_le_mul_left (literalStageFourierScale_pos Y)).mp
      simpa [literalStageFourierScale_ne_zero Y] using hi.2
''','''    constructor
    · have h := mul_lt_mul_of_pos_left hi.1
        (inv_pos.mpr (literalStageFourierScale_pos Y))
      simpa [literalStageFourierScale_ne_zero Y,
        div_eq_mul_inv, mul_assoc] using h
    · have h := mul_le_mul_of_nonneg_left hi.2
        (inv_pos.mpr (literalStageFourierScale_pos Y)).le
      simpa [literalStageFourierScale_ne_zero Y,
        div_eq_mul_inv, mul_assoc] using h
'''))

for old, new in repls:
    assert old in s, old[:140]
    s = s.replace(old, new, 1)
full_sha = hashlib.sha256(s.encode()).hexdigest()
prefix = ''.join(s.splitlines(True)[:52985])
out.write_text(prefix)
meta = {
    'base_sha256': sha,
    'full_candidate_sha256': full_sha,
    'prefix_sha256': hashlib.sha256(prefix.encode()).hexdigest(),
    'prefix_lines': len(prefix.splitlines()),
    'repairs': [
        '3871_fourier_scale_positivity',
        '3874_fourier_box_preimage_iInter',
        '3878_complex_coordinate_norm',
        '3917_inverse_and_forward_scale_inequalities',
        '3920_inverse_scale_inequalities',
    ],
}
Path(str(out) + '.json').write_text(json.dumps(meta, indent=2, sort_keys=True) + '\n')
print(json.dumps(meta, indent=2, sort_keys=True))
