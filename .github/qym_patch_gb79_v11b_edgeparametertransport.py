#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import hashlib
import json
import re
import sys

BASE_SHA256 = "790b40c05a8f3735dd171a135eda65de92ab68b247d13e7e2ffe2968e3798421"

HEAD = '''theorem edgeParameterTransport_hasDerivAt
    (e : QYM.FullCertification.PolygonTraceExtension.PolygonEdge) (t : ℝ) :
    HasDerivAt (QYM.FullCertification.P2NormalGreenExtension.edgeParameterTransport e)
      (e.2.parameterSign : ℝ) t := by
'''

PARAM_SIGN = (
    "Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry."
    "GammaTwoModularTileEdge.parameterSign"
)
EDGE_TRANSPORT = "QYM.FullCertification.P2NormalGreenExtension.edgeParameterTransport"

VARIANTS: dict[str, str] = {
    "change_const_mul": HEAD + '''  change HasDerivAt
    (fun x : ℝ => (e.2.parameterSign : ℝ) * x)
    (e.2.parameterSign : ℝ) t
  simpa using (hasDerivAt_id t).const_mul (e.2.parameterSign : ℝ)
''',
    "change_const_mul_exact": HEAD + '''  change HasDerivAt
    (fun x : ℝ => (e.2.parameterSign : ℝ) * x)
    (e.2.parameterSign : ℝ) t
  exact (hasDerivAt_id t).const_mul (e.2.parameterSign : ℝ)
''',
    "change_mul": HEAD + '''  change HasDerivAt
    (fun x : ℝ => (e.2.parameterSign : ℝ) * x)
    (e.2.parameterSign : ℝ) t
  simpa using
    (hasDerivAt_const t (e.2.parameterSign : ℝ)).mul (hasDerivAt_id t)
''',
    "change_mul_convert": HEAD + '''  change HasDerivAt
    (fun x : ℝ => (e.2.parameterSign : ℝ) * x)
    (e.2.parameterSign : ℝ) t
  convert (hasDerivAt_const t (e.2.parameterSign : ℝ)).mul (hasDerivAt_id t) using 1 <;> simp
''',
    "change_fun_prop": HEAD + '''  change HasDerivAt
    (fun x : ℝ => (e.2.parameterSign : ℝ) * x)
    (e.2.parameterSign : ℝ) t
  fun_prop
''',
    "unfold_fun_prop": HEAD + f'''  unfold {EDGE_TRANSPORT}
  fun_prop
''',
    "letI_mul": HEAD + '''  letI : AddCommGroup ℝ := Real.instAddCommGroup
  letI : Module ℝ ℝ := Semiring.toModule
  change HasDerivAt
    (fun x : ℝ => (e.2.parameterSign : ℝ) * x)
    (e.2.parameterSign : ℝ) t
  simpa using
    (hasDerivAt_const t (e.2.parameterSign : ℝ)).mul (hasDerivAt_id t)
''',
    "letI_change_const_mul": HEAD + '''  letI : AddCommGroup ℝ := Real.instAddCommGroup
  letI : Module ℝ ℝ := Semiring.toModule
  change HasDerivAt
    (fun x : ℝ => (e.2.parameterSign : ℝ) * x)
    (e.2.parameterSign : ℝ) t
  exact (hasDerivAt_id t).const_mul (e.2.parameterSign : ℝ)
''',
    "cases_fun_prop": HEAD + f'''  rcases e with ⟨q, k⟩
  cases k <;>
    simp [{EDGE_TRANSPORT}, {PARAM_SIGN}] <;>
    fun_prop
''',
    "cases_deriv": HEAD + f'''  rcases e with ⟨q, k⟩
  cases k <;>
    simp only [{EDGE_TRANSPORT}, {PARAM_SIGN}, Int.cast_one, Int.cast_neg,
      one_mul, neg_one_mul] <;>
    fun_prop
''',
    "transparent_change": '''set_option backward.isDefEq.respectTransparency false in
''' + HEAD + '''  change HasDerivAt
    (fun x : ℝ => (e.2.parameterSign : ℝ) * x)
    (e.2.parameterSign : ℝ) t
  simpa using (hasDerivAt_id t).const_mul (e.2.parameterSign : ℝ)
''',
    "transparent_mul": '''set_option backward.isDefEq.respectTransparency false in
''' + HEAD + '''  change HasDerivAt
    (fun x : ℝ => (e.2.parameterSign : ℝ) * x)
    (e.2.parameterSign : ℝ) t
  simpa using
    (hasDerivAt_const t (e.2.parameterSign : ℝ)).mul (hasDerivAt_id t)
''',
}

TARGET_RE = re.compile(
    r"(?ms)^theorem edgeParameterTransport_hasDerivAt\b.*?"
    r"(?=^/-- Exact derivative of the transported target curve\.)"
)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git_blob(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def audit(text: str) -> dict[str, int]:
    return {
        "sorry": len(re.findall(r"\bsorry\b", text)),
        "admit": len(re.findall(r"\badmit\b", text)),
        "native_decide": len(re.findall(r"\bnative_decide\b", text)),
        "Lean.ofReduceBool": text.count("Lean.ofReduceBool"),
        "global_axiom": len(re.findall(r"(?m)^\s*axiom\s+", text)),
        "unsafe": len(re.findall(r"(?m)^\s*unsafe\s+", text)),
        "maxHeartbeats_zero": len(re.findall(r"set_option\s+maxHeartbeats\s+0\b", text)),
    }


def main() -> None:
    if len(sys.argv) != 3:
        raise SystemExit("usage: qym_patch_gb79_v11b_edgeparametertransport.py VARIANT QYM.lean")
    variant = sys.argv[1]
    path = Path(sys.argv[2])
    if variant not in VARIANTS:
        raise SystemExit(f"unknown variant {variant!r}; expected {sorted(VARIANTS)}")

    before = path.read_bytes()
    if sha256(before) != BASE_SHA256:
        raise SystemExit(f"input is not authoritative GB79: {sha256(before)}")
    text = before.decode("utf-8")
    before_audit = audit(text)
    matches = list(TARGET_RE.finditer(text))
    if len(matches) != 1:
        raise SystemExit(f"expected one edgeParameterTransport theorem, found {len(matches)}")
    match = matches[0]
    replacement = VARIANTS[variant].rstrip() + "\n\n"
    updated = text[:match.start()] + replacement + text[match.end():]
    after_audit = audit(updated)
    if after_audit != before_audit:
        raise SystemExit(f"forbidden-token delta: {before_audit} -> {after_audit}")

    path.write_text(updated, encoding="utf-8")
    after = path.read_bytes()
    gate_marker = "theorem pairedTransportCoordinate_hasDerivAt"
    gate_index = updated.find(gate_marker)
    if gate_index < 0:
        raise SystemExit("post-blocker gate marker not found")

    print(json.dumps({
        "schema": "qym-gb79-v11b-edgeparametertransport-patch-v1",
        "variant": variant,
        "input_sha256": sha256(before),
        "input_blob": git_blob(before),
        "candidate_sha256": sha256(after),
        "candidate_blob": git_blob(after),
        "bytes": len(after),
        "lf": after.count(b"\n"),
        "gate_line": updated.count("\n", 0, gate_index) + 1,
        "audit_before": before_audit,
        "audit_after": after_audit,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
