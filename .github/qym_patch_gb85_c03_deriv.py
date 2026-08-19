#!/usr/bin/env python3
from pathlib import Path
import hashlib
import json
import re
import sys

BASE_SHA256 = "f4c9b27a297be772cde7183526378ad42ae826053f69cf3ce521670da4f06210"
BASE_BLOB = "bd28d0436230a8f0bcb01806dac01787542256b8"
VARIANTS = {"reducible_simp", "reducible_convert"}

BASE_HEAD = r'''theorem baseEdgeCoordinate_hasDerivAt
    (e : QYM.FullCertification.PolygonTraceExtension.PolygonEdge) {t : ℝ}
    (ht : t ∈ QYM.FullCertification.P2NormalGreenExtension.regularEdgeParameterSet e) :
    HasDerivAt (baseEdgeCoordinate e.2)
      (baseEdgeVelocity e.2 t) t := by
  rcases e with ⟨q, k⟩
  cases k with
  | circularArc =>
      have hx :
          HasDerivAt (fun s : ℝ => ((s / 2 : ℝ) : ℂ))
            (((1 : ℝ) / 2 : ℝ) : ℂ) t :=
        ((hasDerivAt_id t).div_const 2).ofReal_comp
      have hy :
          HasDerivAt
            (fun s : ℝ =>
              ((Real.sqrt (1 - (s / 2) ^ 2) : ℝ) : ℂ))
            ((-t / (4 * Real.sqrt (1 - (t / 2) ^ 2)) : ℝ) : ℂ) t :=
        (hasDerivAt_circularHeight ht).ofReal_comp
'''

BASE_SIMP = BASE_HEAD + r'''      with_reducible_and_instances
        simpa [Complex.mk_eq_add_mul_I] using
          hx.add (hy.mul_const Complex.I)
  | leftVerticalSegment =>
      have hy0 :=
        (hasDerivAt_const t (Real.sqrt 3 / 2)).add (hasDerivAt_id t)
      have hy : HasDerivAt
          (fun s : ℝ => Real.sqrt 3 / 2 + s) 1 t := by
        with_reducible_and_instances
          simpa using hy0
      have h := (hy.ofReal_comp.mul_const Complex.I).const_add
        (-((1 : ℝ) / 2) : ℂ)
      with_reducible_and_instances
        simpa [Complex.mk_eq_add_mul_I] using h
  | rightVerticalSegment =>
      have hy0 :=
        (hasDerivAt_const t (Real.sqrt 3 / 2)).add (hasDerivAt_id t)
      have hy : HasDerivAt
          (fun s : ℝ => Real.sqrt 3 / 2 + s) 1 t := by
        with_reducible_and_instances
          simpa using hy0
      have h := (hy.ofReal_comp.mul_const Complex.I).const_add
        (((1 : ℝ) / 2 : ℝ) : ℂ)
      with_reducible_and_instances
        simpa [Complex.mk_eq_add_mul_I] using h
'''

BASE_CONVERT = BASE_HEAD + r'''      have h := hx.add (hy.mul_const Complex.I)
      with_reducible_and_instances
        convert h using 1 <;> simp [Complex.mk_eq_add_mul_I]
  | leftVerticalSegment =>
      have hy0 :=
        (hasDerivAt_const t (Real.sqrt 3 / 2)).add (hasDerivAt_id t)
      have hy : HasDerivAt
          (fun s : ℝ => Real.sqrt 3 / 2 + s) 1 t := by
        with_reducible_and_instances
          convert hy0 using 1 <;> simp
      have h := (hy.ofReal_comp.mul_const Complex.I).const_add
        (-((1 : ℝ) / 2) : ℂ)
      with_reducible_and_instances
        convert h using 1 <;> simp [Complex.mk_eq_add_mul_I]
  | rightVerticalSegment =>
      have hy0 :=
        (hasDerivAt_const t (Real.sqrt 3 / 2)).add (hasDerivAt_id t)
      have hy : HasDerivAt
          (fun s : ℝ => Real.sqrt 3 / 2 + s) 1 t := by
        with_reducible_and_instances
          convert hy0 using 1 <;> simp
      have h := (hy.ofReal_comp.mul_const Complex.I).const_add
        (((1 : ℝ) / 2 : ℝ) : ℂ)
      with_reducible_and_instances
        convert h using 1 <;> simp [Complex.mk_eq_add_mul_I]
'''

SELECTED_HEAD = r'''theorem selectedRepresentativeChart_hasStrictDerivAt
    (q : Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.GammaTwoRightCoset) (z : ℍ) :
    HasStrictDerivAt (selectedRepresentativeChart q)
      (1 / selectedRepresentativeDenom q (z : ℂ) ^ 2) (z : ℂ) := by
  have hdet : (selectedRepresentativeRealMatrix q).val.det = 1 := by
    change
      (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)
        (Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.gammaTwoCosetRep q)).val.det = 1
    exact
      (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)
        (Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.gammaTwoCosetRep q)).property
  have hpos : 0 < (selectedRepresentativeRealMatrix q).val.det := by
    rw [hdet]
    norm_num
  have hraw := UpperHalfPlane.hasStrictDerivAt_smul
    (g := selectedRepresentativeRealMatrix q) hpos z
'''

SELECTED_SIMP = SELECTED_HEAD + r'''  with_reducible_and_instances
    simpa [selectedRepresentativeChart, selectedRepresentativeCoordinate,
      selectedRepresentativeDenom, selectedRepresentativeRealMatrix,
      hdet, one_div] using hraw
'''

SELECTED_CONVERT = SELECTED_HEAD + r'''  with_reducible_and_instances
    convert hraw using 1 <;>
      simp [selectedRepresentativeChart, selectedRepresentativeCoordinate,
        selectedRepresentativeDenom, selectedRepresentativeRealMatrix,
        hdet, one_div]
'''

TRANSPORT = r'''theorem edgeParameterTransport_hasDerivAt
    (e : QYM.FullCertification.PolygonTraceExtension.PolygonEdge) (t : ℝ) :
    HasDerivAt (QYM.FullCertification.P2NormalGreenExtension.edgeParameterTransport e)
      (e.2.parameterSign : ℝ) t := by
  change HasDerivAt
    (fun x : ℝ => (e.2.parameterSign : ℝ) * x)
    (e.2.parameterSign : ℝ) t
  with_reducible_and_instances
    simpa only [id_eq, mul_one] using
      (hasDerivAt_id t).const_mul (e.2.parameterSign : ℝ)
'''

RE_BASE = re.compile(
    r"(?ms)^theorem baseEdgeCoordinate_hasDerivAt\b.*?(?=^/-! ## 4\.)"
)
RE_SELECTED = re.compile(
    r"(?ms)^theorem selectedRepresentativeChart_hasStrictDerivAt\b.*?"
    r"(?=^/-- Fully explicit complex coordinate)"
)
RE_TRANSPORT = re.compile(
    r"(?ms)^theorem edgeParameterTransport_hasDerivAt\b.*?"
    r"(?=^/-- Exact derivative of the transported target curve)"
)


def git_blob(data: bytes) -> str:
    return hashlib.sha1(
        b"blob " + str(len(data)).encode() + b"\0" + data
    ).hexdigest()


def audit(text: str) -> dict[str, int]:
    return {
        "sorry": len(re.findall(r"\bsorry\b", text)),
        "admit": len(re.findall(r"\badmit\b", text)),
        "native_decide": len(re.findall(r"\bnative_decide\b", text)),
        "Lean.ofReduceBool": text.count("Lean.ofReduceBool"),
        "global_axiom": len(re.findall(r"(?m)^\s*axiom\s+", text)),
        "unsafe": len(re.findall(r"(?m)^\s*unsafe\s+", text)),
        "maxHeartbeats_zero": len(
            re.findall(r"set_option\s+maxHeartbeats\s+0\b", text)
        ),
    }


def main() -> None:
    if len(sys.argv) != 3:
        raise SystemExit("usage: qym_patch_gb85_c03_deriv.py VARIANT QYM.lean")
    variant, filename = sys.argv[1], sys.argv[2]
    if variant not in VARIANTS:
        raise SystemExit(f"unknown variant: {variant}")
    path = Path(filename)
    before = path.read_bytes()
    if hashlib.sha256(before).hexdigest() != BASE_SHA256:
        raise SystemExit("GB85 SHA256 mismatch")
    if git_blob(before) != BASE_BLOB:
        raise SystemExit("GB85 Git blob mismatch")
    text = before.decode("utf-8")
    before_audit = audit(text)
    base = BASE_SIMP if variant == "reducible_simp" else BASE_CONVERT
    selected = SELECTED_SIMP if variant == "reducible_simp" else SELECTED_CONVERT
    text, n_base = RE_BASE.subn(base.rstrip() + "\n\n", text)
    text, n_selected = RE_SELECTED.subn(selected.rstrip() + "\n\n", text)
    text, n_transport = RE_TRANSPORT.subn(TRANSPORT.rstrip() + "\n\n", text)
    if (n_base, n_selected, n_transport) != (1, 1, 1):
        raise SystemExit(
            f"replacement counts: {(n_base, n_selected, n_transport)}"
        )
    after_audit = audit(text)
    if after_audit != before_audit:
        raise SystemExit(f"forbidden-token delta: {before_audit} -> {after_audit}")
    path.write_text(text, encoding="utf-8")
    after = path.read_bytes()
    print(json.dumps({
        "schema": "qym-gb85-c03-deriv-v1",
        "variant": variant,
        "input_sha256": BASE_SHA256,
        "input_blob": BASE_BLOB,
        "candidate_sha256": hashlib.sha256(after).hexdigest(),
        "candidate_blob": git_blob(after),
        "bytes": len(after),
        "lf": after.count(b"\n"),
        "forbidden": after_audit,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
