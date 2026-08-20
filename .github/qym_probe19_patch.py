#!/usr/bin/env python3
from pathlib import Path
import hashlib, re, sys

EXPECTED_INPUT_SHA256 = "971d9fd6c1cba701f6404b6303668b61d3de9f4b5d71281ab7b88f1530009bf7"
EXPECTED_OUTPUT_SHA256 = "069c1476163e3b87670e8eae0960f7975691f83a2ac1440863387eb2036cced5"

p = Path(sys.argv[1])
raw = p.read_bytes()
assert hashlib.sha256(raw).hexdigest() == EXPECTED_INPUT_SHA256
s = raw.decode()

old = """theorem actualFixedPhaseCanonicalTraceClassProjection_opNorm_le
    (n : ℤ) (Y : ℝ) :
    ‖actualFixedPhaseCanonicalTraceClassProjection n Y‖ ≤ 1 :=
  (ActualFixedPhaseCanonicalTraceClass n Y).orthogonalProjection_norm_le
"""
new = """theorem actualFixedPhaseCanonicalTraceClassProjection_opNorm_le
    (n : ℤ) (Y : ℝ) :
    ‖(ActualFixedPhaseCanonicalTraceClass n Y).orthogonalProjectionOnto‖ ≤ 1 :=
  (ActualFixedPhaseCanonicalTraceClass n Y).orthogonalProjectionOnto_norm_le
"""
assert s.count(old) == 1
s = s.replace(old, new)

old = "  letI : AddCommGroup ℂ := Complex.addCommGroup\n"
assert s.count(old) == 1
s = s.replace(old, "")

old = """local instance p2EdgeVelocityCanonicalComplexAddCommGroup : AddCommGroup ℂ :=
  Complex.instNormedAddCommGroup.toAddCommGroup

local def p2EdgeVelocityCanonicalRealAddCommGroup : AddCommGroup ℝ :=
  Real.normedCommRing.toAddCommGroup

local def p2EdgeVelocityCanonicalRealModule : Module ℝ ℝ :=
  (NormedAlgebra.toNormedSpace ℝ).toModule

"""
assert s.count(old) == 1
s = s.replace(old, "")

reps = [
    ("""  simpa [p2EdgeVelocityCanonicalComplexAddCommGroup,
    explicitActualEdgeCoordinate""", """  simpa [explicitActualEdgeCoordinate"""),
    ("""    simpa [p2EdgeVelocityCanonicalComplexAddCommGroup,
      actedSourceCoordinate""", """    simpa [actedSourceCoordinate"""),
    ("""  simpa [p2EdgeVelocityCanonicalComplexAddCommGroup,
    pairedTransportCoordinate""", """  simpa [pairedTransportCoordinate"""),
]
for old, new in reps:
    assert s.count(old) == 1
    s = s.replace(old, new)

p.write_text(s)
raw = p.read_bytes()
assert hashlib.sha256(raw).hexdigest() == EXPECTED_OUTPUT_SHA256

text = raw.decode()
forbidden = {
    "sorry": len(re.findall(r"\bsorry\b", text)),
    "admit": len(re.findall(r"\badmit\b", text)),
    "native_decide": len(re.findall(r"\bnative_decide\b", text)),
    "Lean.ofReduceBool": text.count("Lean.ofReduceBool"),
    "global_axiom": len(re.findall(r"(?m)^\s*axiom\s+", text)),
    "unsafe": len(re.findall(r"(?m)^\s*unsafe\s+", text)),
    "maxHeartbeats_zero": len(re.findall(r"set_option\s+maxHeartbeats\s+0\b", text)),
}
assert not any(forbidden.values()), forbidden
print(EXPECTED_OUTPUT_SHA256)
