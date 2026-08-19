#!/usr/bin/env python3
from pathlib import Path
import hashlib, json, re, sys

BASE_SHA256 = "ea7c26fd104104e852a6c678017b1fb0c76abb062edd758228c4bbe506dbe8d1"
ANCHOR = "namespace QYM.FullCertification.P2ExplicitEdgeVelocityExtension\n"
ATTR_ADD = """namespace QYM.FullCertification.P2ExplicitEdgeVelocityExtension\n\nattribute [local instance 1001]\n  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid\n"""
ATTR_ADD_MODULE = """namespace QYM.FullCertification.P2ExplicitEdgeVelocityExtension\n\nattribute [local instance 1001]\n  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid\nattribute [local instance 1001] NormedSpace.toModule\n"""

OLD_SELECTED = r'''theorem selectedRepresentativeChart_hasStrictDerivAt
    (q : Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.GammaTwoRightCoset) (z : ℍ) :
    HasStrictDerivAt (selectedRepresentativeChart q)
      (1 / selectedRepresentativeDenom q (z : ℂ) ^ 2) (z : ℂ) := by
  simpa [selectedRepresentativeChart, selectedRepresentativeCoordinate,
    selectedRepresentativeDenom, selectedRepresentativeRealMatrix,
    one_div] using
      (UpperHalfPlane.hasStrictDerivAt_smul
        (g := selectedRepresentativeRealMatrix q) (by
          change 0 <
            (((Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.gammaTwoCosetRep q :
              SL(2, ℤ)) : GL (Fin 2) ℝ)).val.det
          exact
            Mock2FA.PaperCorrections.AutomorphicSobolev.FixedPhaseIntrinsicAdjointCutoff.integralMoebius_det_pos
              (Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.gammaTwoCosetRep q)) z)
'''

NEW_SELECTED = r'''theorem selectedRepresentativeChart_hasStrictDerivAt
    (q : Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.GammaTwoRightCoset) (z : ℍ) :
    HasStrictDerivAt (selectedRepresentativeChart q)
      (1 / selectedRepresentativeDenom q (z : ℂ) ^ 2) (z : ℂ) := by
  have hdet : (selectedRepresentativeRealMatrix q).det.val = 1 := by
    simp [selectedRepresentativeRealMatrix]
  have h :=
    UpperHalfPlane.hasStrictDerivAt_smul
      (g := selectedRepresentativeRealMatrix q) (by
        change 0 <
          (((Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.gammaTwoCosetRep q :
            SL(2, ℤ)) : GL (Fin 2) ℝ)).val.det
        exact
          Mock2FA.PaperCorrections.AutomorphicSobolev.FixedPhaseIntrinsicAdjointCutoff.integralMoebius_det_pos
            (Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.gammaTwoCosetRep q)) z
  simpa [selectedRepresentativeChart, selectedRepresentativeCoordinate,
    selectedRepresentativeDenom, one_div, hdet] using h
'''

OLD_EDGE = r'''theorem edgeParameterTransport_hasDerivAt
    (e : QYM.FullCertification.PolygonTraceExtension.PolygonEdge) (t : ℝ) :
    HasDerivAt (QYM.FullCertification.P2NormalGreenExtension.edgeParameterTransport e)
      (e.2.parameterSign : ℝ) t := by
  simpa [QYM.FullCertification.P2NormalGreenExtension.edgeParameterTransport] using
    (hasDerivAt_id t).const_mul (e.2.parameterSign : ℝ)
'''

NEW_EDGE = r'''theorem edgeParameterTransport_hasDerivAt
    (e : QYM.FullCertification.PolygonTraceExtension.PolygonEdge) (t : ℝ) :
    HasDerivAt (QYM.FullCertification.P2NormalGreenExtension.edgeParameterTransport e)
      (e.2.parameterSign : ℝ) t := by
  change HasDerivAt (fun x : ℝ => (e.2.parameterSign : ℝ) * x)
    (e.2.parameterSign : ℝ) t
  exact (hasDerivAt_id t).const_mul (e.2.parameterSign : ℝ)
'''

VARIANTS = {
  "addgroup": (ATTR_ADD, False, False),
  "addgroup_module_selected": (ATTR_ADD_MODULE, True, False),
  "addgroup_module_selected_edge": (ATTR_ADD_MODULE, True, True),
}

def audit(s: str):
    return {k: len(re.findall(p, s)) for k,p in {
      "sorry": r"\bsorry\b", "admit": r"\badmit\b",
      "native_decide": r"\bnative_decide\b", "global_axiom": r"(?m)^\s*axiom\s+",
      "unsafe": r"(?m)^\s*unsafe\s+", "maxHeartbeats_zero": r"set_option\s+maxHeartbeats\s+0\b"
    }.items()}

def main():
    if len(sys.argv) != 3 or sys.argv[1] not in VARIANTS:
        raise SystemExit("usage: patch VARIANT QYM.lean")
    variant, fn = sys.argv[1], Path(sys.argv[2])
    raw = fn.read_bytes()
    if hashlib.sha256(raw).hexdigest() != BASE_SHA256:
        raise SystemExit("unexpected GB83 source SHA256")
    text = raw.decode()
    before = audit(text)
    attrs, selected, edge = VARIANTS[variant]
    if text.count(ANCHOR) != 1:
        raise SystemExit("namespace anchor mismatch")
    text = text.replace(ANCHOR, attrs, 1)
    if selected:
        if text.count(OLD_SELECTED) != 1: raise SystemExit("selected theorem mismatch")
        text = text.replace(OLD_SELECTED, NEW_SELECTED, 1)
    if edge:
        if text.count(OLD_EDGE) != 1: raise SystemExit("edge theorem mismatch")
        text = text.replace(OLD_EDGE, NEW_EDGE, 1)
    after = audit(text)
    if after != before:
        raise SystemExit(f"forbidden delta {before} -> {after}")
    fn.write_text(text)
    out = fn.read_bytes()
    print(json.dumps({"variant": variant, "input_sha256": BASE_SHA256,
      "candidate_sha256": hashlib.sha256(out).hexdigest(), "forbidden": after,
      "bytes": len(out)}, indent=2, sort_keys=True))

if __name__ == "__main__": main()
