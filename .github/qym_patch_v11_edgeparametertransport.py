#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import hashlib
import json
import re
import sys

THEOREM_HEAD = r'''theorem edgeParameterTransport_hasDerivAt
    (e : QYM.FullCertification.PolygonTraceExtension.PolygonEdge) (t : ℝ) :
    HasDerivAt (QYM.FullCertification.P2NormalGreenExtension.edgeParameterTransport e)
      (e.2.parameterSign : ℝ) t := by
'''

VARIANTS = {
    "letI_simpa": THEOREM_HEAD + r'''  letI : AddCommGroup ℝ := Real.instAddCommGroup
  letI : Module ℝ ℝ := Semiring.toModule
  simpa [QYM.FullCertification.P2NormalGreenExtension.edgeParameterTransport] using
    (hasDerivAt_id t).const_mul (e.2.parameterSign : ℝ)
''',
    "letI_change": THEOREM_HEAD + r'''  letI : AddCommGroup ℝ := Real.instAddCommGroup
  letI : Module ℝ ℝ := Semiring.toModule
  change HasDerivAt
    (fun x : ℝ => (e.2.parameterSign : ℝ) * x)
    (e.2.parameterSign : ℝ) t
  exact (hasDerivAt_id t).const_mul (e.2.parameterSign : ℝ)
''',
    "transparent_simpa": r'''set_option backward.isDefEq.respectTransparency false in
theorem edgeParameterTransport_hasDerivAt
    (e : QYM.FullCertification.PolygonTraceExtension.PolygonEdge) (t : ℝ) :
    HasDerivAt (QYM.FullCertification.P2NormalGreenExtension.edgeParameterTransport e)
      (e.2.parameterSign : ℝ) t := by
  simpa [QYM.FullCertification.P2NormalGreenExtension.edgeParameterTransport] using
    (hasDerivAt_id t).const_mul (e.2.parameterSign : ℝ)
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
    if len(sys.argv) not in (3, 4):
        raise SystemExit("usage: qym_patch_v11_edgeparametertransport.py VARIANT QYM.lean [EXPECTED_SHA256]")
    variant, filename = sys.argv[1], sys.argv[2]
    expected_sha = sys.argv[3] if len(sys.argv) == 4 else None
    if variant not in VARIANTS:
        raise SystemExit(f"unknown variant {variant!r}; expected {sorted(VARIANTS)}")
    path = Path(filename)
    before = path.read_bytes()
    if expected_sha is not None and sha256(before) != expected_sha:
        raise SystemExit(f"unexpected input SHA256: {sha256(before)} != {expected_sha}")
    text = before.decode("utf-8")
    before_audit = audit(text)
    matches = list(TARGET_RE.finditer(text))
    if len(matches) != 1:
        raise SystemExit(f"expected exactly one edgeParameterTransport theorem, found {len(matches)}")
    m = matches[0]
    text = text[:m.start()] + VARIANTS[variant].rstrip() + "\n\n" + text[m.end():]
    after_audit = audit(text)
    if after_audit != before_audit:
        raise SystemExit(f"forbidden-token delta: {before_audit} -> {after_audit}")
    path.write_text(text, encoding="utf-8")
    after = path.read_bytes()
    marker = "theorem pairedTransportCoordinate_hasDerivAt"
    marker_index = text.find(marker)
    if marker_index < 0:
        raise SystemExit("could not locate post-V11 gate marker")
    print(json.dumps({
        "schema": "qym-v11-edgeparametertransport-patch-v1",
        "variant": variant,
        "input_sha256": sha256(before),
        "input_blob": git_blob(before),
        "candidate_sha256": sha256(after),
        "candidate_blob": git_blob(after),
        "bytes": len(after),
        "lf": after.count(b"\n"),
        "gate_line": text.count("\n", 0, marker_index) + 1,
        "forbidden": after_audit,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
