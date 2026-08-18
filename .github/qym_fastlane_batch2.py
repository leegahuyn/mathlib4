#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import hashlib
import json
import re
import sys

INPUT_SHA256 = "55ae6e4e42654ff1140da04785758724c34e473113b621ec267ecf1d791ac75c"
INPUT_BLOB = "a23c17e4ee6852b23b2e1e1a5ffe8b4b19e12dff"
OUTPUT_SHA256 = "eff40c6634713f17cc4005a93040eeb92322f32c68b20c158d88adf19cdc99a8"
OUTPUT_BLOB = "d10513bb489b8326d516c953a105dd9da05820f1"

OLD_HOROCYCLE = '''  simp only [actualFixedPhaseCuspHorocyclePoint,
    actualFixedPhaseHorizontalHorocyclePoint,
    UpperHalfPlane.coe_specialLinearGroup_apply]
  apply ContDiff.div
  · fun_prop
  · fun_prop
  · exact hden
'''

NEW_HOROCYCLE = '''  have hnum : ContDiff ℝ ∞
      (fun x : ℝ =>
        (algebraMap ℤ ℝ (sigma 0 0) : ℂ) *
            (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ) +
          (algebraMap ℤ ℝ (sigma 0 1) : ℂ)) := by
    fun_prop
  have hdenDiff : ContDiff ℝ ∞
      (fun x : ℝ =>
        (algebraMap ℤ ℝ (sigma 1 0) : ℂ) *
            (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ) +
          (algebraMap ℤ ℝ (sigma 1 1) : ℂ)) := by
    fun_prop
  simpa only [actualFixedPhaseCuspHorocyclePoint,
    UpperHalfPlane.coe_specialLinearGroup_apply, sigma,
    div_eq_mul_inv] using hnum.mul (hdenDiff.inv hden)
'''

OLD_NAMED_TRACE = '''  simpa [actualFixedPhaseNamedCuspTraceRepresentative,
    Function.comp_def] using hcomp
'''

NEW_NAMED_TRACE = '''  change ContDiff ℝ ∞
    (fun x : ℝ =>
      (u : SmoothQuotientCompactFunction)
        (actualFixedPhaseCuspHorocyclePoint kappa Y x))
  exact hcomp
'''


def git_blob(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def main() -> None:
    if len(sys.argv) != 2:
        raise SystemExit("usage: qym_fastlane_batch2.py QYM.lean")
    path = Path(sys.argv[1])
    before = path.read_bytes()
    actual_sha = hashlib.sha256(before).hexdigest()
    actual_blob = git_blob(before)
    if actual_sha != INPUT_SHA256 or actual_blob != INPUT_BLOB:
        raise SystemExit(f"input authority mismatch: {actual_sha} {actual_blob}")

    text = before.decode("utf-8")
    replacements = [
        ("horocycle-complex-quotient", OLD_HOROCYCLE, NEW_HOROCYCLE),
        ("named-trace-defeq", OLD_NAMED_TRACE, NEW_NAMED_TRACE),
    ]
    for label, old, new in replacements:
        count = text.count(old)
        if count != 1:
            raise SystemExit(f"{label} replacement count = {count}, expected 1")
        text = text.replace(old, new, 1)

    path.write_text(text, encoding="utf-8")
    after = path.read_bytes()
    sha256 = hashlib.sha256(after).hexdigest()
    blob = git_blob(after)
    if sha256 != OUTPUT_SHA256 or blob != OUTPUT_BLOB:
        raise SystemExit(f"unexpected output: {sha256} {blob}")

    decoded = after.decode("utf-8")
    forbidden = {
        "sorry": len(re.findall(r"\bsorry\b", decoded)),
        "admit": len(re.findall(r"\badmit\b", decoded)),
        "native_decide": len(re.findall(r"\bnative_decide\b", decoded)),
        "Lean.ofReduceBool": decoded.count("Lean.ofReduceBool"),
        "global_axiom": len(re.findall(r"(?m)^\s*axiom\s+", decoded)),
        "unsafe": len(re.findall(r"(?m)^\s*unsafe\s+", decoded)),
        "maxHeartbeats_zero": len(re.findall(r"set_option\s+maxHeartbeats\s+0\b", decoded)),
    }
    if any(forbidden.values()):
        raise SystemExit(f"forbidden-token audit failed: {forbidden}")

    print(json.dumps({
        "schema": "qym-fastlane-probe35-batch2-v1",
        "input_sha256": INPUT_SHA256,
        "input_blob": INPUT_BLOB,
        "candidate_sha256": sha256,
        "candidate_blob": blob,
        "bytes": len(after),
        "lf": after.count(b"\n"),
        "fixed_producers": [
            "actualFixedPhaseCuspHorocyclePoint_coe_contDiff",
            "actualFixedPhaseNamedCuspTraceRepresentative_contDiff",
        ],
        "forbidden": forbidden,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
