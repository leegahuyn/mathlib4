#!/usr/bin/env python3
from pathlib import Path
import hashlib
import json
import re
import sys

INPUT_SHA256 = "94fceba9313ded915c6e50a17e156699eb48170595b062b1138d04b6abe31534"
EXPECTED = {
    "simpa-def": {
        "sha256": "79f1cfb0a72fb7095f13c140879bd16426b437e74fa2912943319d764ee8e4bd",
        "blob": "ef9b098b912f92ff70326520560c4a91402684ef",
    },
    "simpa-upperLift": {
        "sha256": "1a87ac6583756d383c44c65988701481c6f10ad514c21f9ac62bb3fda9f2ecb2",
        "blob": "a47f68be14aeb44acfd8b2e1b414016e6d16b957",
    },
    "simpa-coe": {
        "sha256": "8d8db79caad9aff3478a07bf3f09c3577f65266a040591cf86fb3f0ee7a4a029",
        "blob": "14459d408b288f8df3b6d9a1343737f7b9e26b3e",
    },
}

REPLACEMENTS = [
    (
        """theorem actualFixedPhaseCanonicalTraceClassProjection_opNorm_le
    (n : ℤ) (Y : ℝ) :
    ‖(ActualFixedPhaseCanonicalTraceClass n Y).orthogonalProjectionOnto‖ ≤ 1 :=
  (ActualFixedPhaseCanonicalTraceClass n Y).orthogonalProjectionOnto_norm_le
""",
        """theorem actualFixedPhaseCanonicalTraceClassProjection_opNorm_le
    (n : ℤ) (Y : ℝ) : _ :=
  (ActualFixedPhaseCanonicalTraceClass n Y).orthogonalProjectionOnto_norm_le
""",
    ),
    (
        """set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 2000000 in
noncomputable def actualFixedPhaseHhalfTraceCompletionInnerProductSpace
    (n : ℤ) (Y : ℝ) :
    InnerProductSpace ℂ (ActualFixedPhaseHhalfTraceCompletion n Y) :=
  inferInstance
""",
        """noncomputable def actualFixedPhaseHhalfTraceCompletionInnerProductSpace
    (n : ℤ) (Y : ℝ) :
    InnerProductSpace ℂ (ActualFixedPhaseHhalfTraceCompletion n Y) :=
  (ActualFixedPhaseHhalfTraceCompletion n Y).innerProductSpace
""",
    ),
    (
        """  rw [div_eq_mul_inv]
  apply ContDiff.mul
  · fun_prop
  · apply ContDiff.inv
    · fun_prop
    · exact hden
""",
        """  apply ContDiff.div
  · fun_prop
  · fun_prop
  · exact hden
""",
    ),
]

OLD_TRACE = """  change ContDiff ℝ ∞
    (upperLift ((u : SmoothQuotientCompactFunction) : ℍ → ℂ) ∘
      fun x : ℝ =>
        ((actualFixedPhaseCuspHorocyclePoint kappa Y x : ℍ) : ℂ))
  exact hcomp
"""
TRACE_VARIANTS = {
    "simpa-def": """  simpa [actualFixedPhaseNamedCuspTraceRepresentative,
    Function.comp_def] using hcomp
""",
    "simpa-upperLift": """  simpa [actualFixedPhaseNamedCuspTraceRepresentative,
    Function.comp_def, upperLift] using hcomp
""",
    "simpa-coe": """  simpa only [actualFixedPhaseNamedCuspTraceRepresentative,
    Function.comp_apply] using hcomp
""",
}


def replace_once(text: str, old: str, new: str) -> str:
    assert text.count(old) == 1, (old[:100], text.count(old))
    return text.replace(old, new, 1)


def main() -> None:
    variant, file_name = sys.argv[1], sys.argv[2]
    assert variant in EXPECTED
    path = Path(file_name)
    raw = path.read_bytes()
    assert hashlib.sha256(raw).hexdigest() == INPUT_SHA256
    text = raw.decode("utf-8")
    for old, new in REPLACEMENTS:
        text = replace_once(text, old, new)
    text = replace_once(text, OLD_TRACE, TRACE_VARIANTS[variant])
    path.write_text(text, encoding="utf-8")
    result = path.read_bytes()
    sha = hashlib.sha256(result).hexdigest()
    blob = hashlib.sha1(b"blob " + str(len(result)).encode() + b"\0" + result).hexdigest()
    assert sha == EXPECTED[variant]["sha256"], (sha, EXPECTED[variant]["sha256"])
    assert blob == EXPECTED[variant]["blob"], (blob, EXPECTED[variant]["blob"])
    decoded = result.decode("utf-8")
    forbidden = {
        "sorry": len(re.findall(r"\bsorry\b", decoded)),
        "admit": len(re.findall(r"\badmit\b", decoded)),
        "native_decide": len(re.findall(r"\bnative_decide\b", decoded)),
        "Lean.ofReduceBool": decoded.count("Lean.ofReduceBool"),
        "global_axiom": len(re.findall(r"(?m)^\s*axiom\s+", decoded)),
        "unsafe": len(re.findall(r"(?m)^\s*unsafe\s+", decoded)),
        "maxHeartbeats_zero": len(re.findall(r"set_option\s+maxHeartbeats\s+0\b", decoded)),
    }
    assert not any(forbidden.values()), forbidden
    print(json.dumps({
        "schema": "qym-probe31-horocycle-matrix-v1",
        "variant": variant,
        "candidate_sha256": sha,
        "candidate_blob": blob,
        "bytes": len(result),
        "lf": result.count(b"\n"),
        "forbidden": forbidden,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()

# Retrigger the registered Probe31 matrix workflow.
