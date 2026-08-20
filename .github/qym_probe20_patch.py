#!/usr/bin/env python3
from pathlib import Path
import hashlib, re, sys

EXPECTED_INPUT_SHA256 = "069c1476163e3b87670e8eae0960f7975691f83a2ac1440863387eb2036cced5"
EXPECTED_OUTPUT_SHA256 = "94fceba9313ded915c6e50a17e156699eb48170595b062b1138d04b6abe31534"

p = Path(sys.argv[1])
raw = p.read_bytes()
assert hashlib.sha256(raw).hexdigest() == EXPECTED_INPUT_SHA256
s = raw.decode()

old = "noncomputable def widthTwoHhalfCompletionInnerProductSpace\n"
new = "noncomputable instance widthTwoHhalfCompletionInnerProductSpace\n"
assert s.count(old) == 1
s = s.replace(old, new, 1)

old = """  letI : ContinuousConstSMul Gamma2 H :=
    { continuous_const_smul := inverseEtaDeckAction_continuous }
  change IsOpenQuotientMap
"""
new = """  letI : ContinuousConstSMul Gamma2 H :=
    { continuous_const_smul := inverseEtaDeckAction_continuous }
  letI : Setoid H := MulAction.orbitRel Gamma2 H
  change IsOpenQuotientMap
"""
assert s.count(old) == 1
s = s.replace(old, new, 1)

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
