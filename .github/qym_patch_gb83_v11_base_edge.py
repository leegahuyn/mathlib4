#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re
import sys

EXPECTED_SHA256 = "072391f01c07d38fcb3a78436ebe9bcd1adf4f822cb90d7fc08aade8128725ba"
EXPECTED_BLOB = "4253706c8dedd8fcf81b8a8060385afcc52459ba"
START = "/-- Exact ambient derivative of all three base edge constructors. -/\ntheorem baseEdgeCoordinate_hasDerivAt"
END = "\n/-! ## 4. Transport through the selected coset representative -/"
FORBIDDEN = {
    "sorry": re.compile(r"\bsorry\b"),
    "admit": re.compile(r"\badmit\b"),
    "axiom": re.compile(r"(?m)^\s*axiom\b"),
    "unsafe": re.compile(r"\bunsafe\b"),
    "native_decide": re.compile(r"\bnative_decide\b"),
    "maxHeartbeats0": re.compile(r"set_option\s+maxHeartbeats\s+0"),
}

HEADER = r'''/-- Exact ambient derivative of all three base edge constructors. -/
theorem baseEdgeCoordinate_hasDerivAt
    (e : QYM.FullCertification.PolygonTraceExtension.PolygonEdge) {t : ℝ}
    (ht : t ∈ QYM.FullCertification.P2NormalGreenExtension.regularEdgeParameterSet e) :
    HasDerivAt (baseEdgeCoordinate e.2)
      (baseEdgeVelocity e.2 t) t := by
  rcases e with ⟨q, k⟩
  cases k with
'''

CIRCULAR = r'''  | circularArc =>
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

EXPLICIT_BRANCHES = r'''  | leftVerticalSegment =>
      have hyReal :
          HasDerivAt (fun s : ℝ => Real.sqrt 3 / 2 + s) 1 t :=
        (hasDerivAt_const t (Real.sqrt 3 / 2)).add (hasDerivAt_id t)
      have hyComplex :
          HasDerivAt
            (fun s : ℝ => ((Real.sqrt 3 / 2 + s : ℝ) : ℂ))
            (1 : ℂ) t :=
        hyReal.ofReal_comp
      have hConst :
          HasDerivAt
            (fun _ : ℝ => ((-((1 : ℝ) / 2) : ℝ) : ℂ))
            0 t :=
        hasDerivAt_const t _
      have h := hConst.add (hyComplex.mul_const Complex.I)
      simpa only [baseEdgeCoordinate, baseEdgeVelocity, Pi.add_apply,
        Complex.mk_eq_add_mul_I, zero_add, one_mul] using! h
  | rightVerticalSegment =>
      have hyReal :
          HasDerivAt (fun s : ℝ => Real.sqrt 3 / 2 + s) 1 t :=
        (hasDerivAt_const t (Real.sqrt 3 / 2)).add (hasDerivAt_id t)
      have hyComplex :
          HasDerivAt
            (fun s : ℝ => ((Real.sqrt 3 / 2 + s : ℝ) : ℂ))
            (1 : ℂ) t :=
        hyReal.ofReal_comp
      have hConst :
          HasDerivAt
            (fun _ : ℝ => ((((1 : ℝ) / 2 : ℝ) : ℂ)))
            0 t :=
        hasDerivAt_const t _
      have h := hConst.add (hyComplex.mul_const Complex.I)
      simpa only [baseEdgeCoordinate, baseEdgeVelocity, Pi.add_apply,
        Complex.mk_eq_add_mul_I, zero_add, one_mul] using! h
'''

CHANGE_BRANCHES = r'''  | leftVerticalSegment =>
      have hyReal :
          HasDerivAt (fun s : ℝ => Real.sqrt 3 / 2 + s) 1 t :=
        (hasDerivAt_const t (Real.sqrt 3 / 2)).add (hasDerivAt_id t)
      have hyComplex :
          HasDerivAt
            (fun s : ℝ => ((Real.sqrt 3 / 2 + s : ℝ) : ℂ))
            (1 : ℂ) t :=
        hyReal.ofReal_comp
      have hConst :
          HasDerivAt
            (fun _ : ℝ => ((-((1 : ℝ) / 2) : ℝ) : ℂ))
            0 t :=
        hasDerivAt_const t _
      change HasDerivAt
        (fun s : ℝ =>
          Complex.mk (-((1 : ℝ) / 2)) (Real.sqrt 3 / 2 + s))
        Complex.I t
      simpa only [Pi.add_apply, Complex.mk_eq_add_mul_I,
        zero_add, one_mul] using!
        hConst.add (hyComplex.mul_const Complex.I)
  | rightVerticalSegment =>
      have hyReal :
          HasDerivAt (fun s : ℝ => Real.sqrt 3 / 2 + s) 1 t :=
        (hasDerivAt_const t (Real.sqrt 3 / 2)).add (hasDerivAt_id t)
      have hyComplex :
          HasDerivAt
            (fun s : ℝ => ((Real.sqrt 3 / 2 + s : ℝ) : ℂ))
            (1 : ℂ) t :=
        hyReal.ofReal_comp
      have hConst :
          HasDerivAt
            (fun _ : ℝ => ((((1 : ℝ) / 2 : ℝ) : ℂ)))
            0 t :=
        hasDerivAt_const t _
      change HasDerivAt
        (fun s : ℝ =>
          Complex.mk ((1 : ℝ) / 2) (Real.sqrt 3 / 2 + s))
        Complex.I t
      simpa only [Pi.add_apply, Complex.mk_eq_add_mul_I,
        zero_add, one_mul] using!
        hConst.add (hyComplex.mul_const Complex.I)
'''

CONVERT_BRANCHES = r'''  | leftVerticalSegment =>
      have hyReal :
          HasDerivAt (fun s : ℝ => Real.sqrt 3 / 2 + s) 1 t :=
        (hasDerivAt_const t (Real.sqrt 3 / 2)).add (hasDerivAt_id t)
      have hyComplex :
          HasDerivAt
            (fun s : ℝ => ((Real.sqrt 3 / 2 + s : ℝ) : ℂ))
            (1 : ℂ) t :=
        hyReal.ofReal_comp
      have hConst :
          HasDerivAt
            (fun _ : ℝ => ((-((1 : ℝ) / 2) : ℝ) : ℂ))
            0 t :=
        hasDerivAt_const t _
      convert! hConst.add (hyComplex.mul_const Complex.I) using 1 <;>
        simp only [baseEdgeCoordinate, baseEdgeVelocity, Pi.add_apply,
          Complex.mk_eq_add_mul_I, zero_add, one_mul]
  | rightVerticalSegment =>
      have hyReal :
          HasDerivAt (fun s : ℝ => Real.sqrt 3 / 2 + s) 1 t :=
        (hasDerivAt_const t (Real.sqrt 3 / 2)).add (hasDerivAt_id t)
      have hyComplex :
          HasDerivAt
            (fun s : ℝ => ((Real.sqrt 3 / 2 + s : ℝ) : ℂ))
            (1 : ℂ) t :=
        hyReal.ofReal_comp
      have hConst :
          HasDerivAt
            (fun _ : ℝ => ((((1 : ℝ) / 2 : ℝ) : ℂ)))
            0 t :=
        hasDerivAt_const t _
      convert! hConst.add (hyComplex.mul_const Complex.I) using 1 <;>
        simp only [baseEdgeCoordinate, baseEdgeVelocity, Pi.add_apply,
          Complex.mk_eq_add_mul_I, zero_add, one_mul]
'''


def blob_sha(raw: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest()


def replacement(variant: str) -> str:
    if variant == "explicit_add_using_bang":
        circular_tail = r'''      have h := hx.add (hy.mul_const Complex.I)
      simpa only [baseEdgeCoordinate, baseEdgeVelocity, Pi.add_apply,
        Complex.mk_eq_add_mul_I] using! h
'''
        return HEADER + CIRCULAR + circular_tail + EXPLICIT_BRANCHES
    if variant == "change_using_bang":
        circular_tail = r'''      change HasDerivAt
        (fun s : ℝ =>
          Complex.mk (s / 2) (Real.sqrt (1 - (s / 2) ^ 2)))
        (Complex.mk ((1 : ℝ) / 2)
          (-t / (4 * Real.sqrt (1 - (t / 2) ^ 2)))) t
      simpa only [Pi.add_apply, Complex.mk_eq_add_mul_I] using!
        hx.add (hy.mul_const Complex.I)
'''
        return HEADER + CIRCULAR + circular_tail + CHANGE_BRANCHES
    if variant == "convert_bang":
        circular_tail = r'''      convert! hx.add (hy.mul_const Complex.I) using 1 <;>
        simp only [baseEdgeCoordinate, baseEdgeVelocity, Pi.add_apply,
          Complex.mk_eq_add_mul_I]
'''
        return HEADER + CIRCULAR + circular_tail + CONVERT_BRANCHES
    raise SystemExit(f"unknown variant: {variant}")


def main() -> None:
    if len(sys.argv) != 3:
        raise SystemExit("usage: qym_patch_gb83_v11_base_edge.py VARIANT QYM.lean")
    variant, filename = sys.argv[1], sys.argv[2]
    path = Path(filename)
    raw = path.read_bytes()
    input_sha = hashlib.sha256(raw).hexdigest()
    input_blob = blob_sha(raw)
    if input_sha != EXPECTED_SHA256 or input_blob != EXPECTED_BLOB:
        raise SystemExit(
            f"GB83 identity mismatch: sha={input_sha} blob={input_blob}"
        )
    text = raw.decode("utf-8")
    start = text.find(START)
    if start < 0:
        raise SystemExit("baseEdgeCoordinate theorem start anchor missing")
    end = text.find(END, start)
    if end < 0:
        raise SystemExit("baseEdgeCoordinate theorem end anchor missing")
    if text.find(START, start + 1) >= 0:
        raise SystemExit("baseEdgeCoordinate theorem anchor is not unique")

    block = replacement(variant)
    candidate = text[:start] + block + text[end:]
    encoded = candidate.encode("utf-8")
    forbidden = {name: len(pattern.findall(block)) for name, pattern in FORBIDDEN.items()}
    if sum(forbidden.values()) != 0:
        raise SystemExit(f"forbidden token in replacement: {forbidden}")
    path.write_bytes(encoded)

    marker = "theorem selectedRepresentativeChart_hasStrictDerivAt"
    marker_index = candidate.find(marker)
    if marker_index < 0:
        raise SystemExit("next-producer marker missing")
    gate_line = candidate.count("\n", 0, marker_index) + 1
    result = {
        "schema": "qym-gb83-v11-base-edge-patch",
        "variant": variant,
        "input_sha256": input_sha,
        "input_blob": input_blob,
        "candidate_sha256": hashlib.sha256(encoded).hexdigest(),
        "candidate_blob": blob_sha(encoded),
        "replacement_start_line": text.count("\n", 0, start) + 1,
        "next_producer_gate_line": gate_line,
        "forbidden": forbidden,
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
