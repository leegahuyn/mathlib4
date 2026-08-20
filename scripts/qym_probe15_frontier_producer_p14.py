#!/usr/bin/env python3
from __future__ import annotations
import argparse, hashlib, json, re
from pathlib import Path

IN = ("e8ac0ba15f35c88792552a0d55d789c222d360a10d30c3cedb0ce0a8dfb879b7",
      "49b71abd253e0b1292ecacd9ebc984fa9ea3d9de", 2940390, 62158)
OUT = ("fa8bc5b346eaf9c613d153598a03606a3bc26dd44502ab46157235d1f3b92e29",
       "71b57fd2e95dc47cdd792514e17af74cf2de86f8", 2940877, 62169)
AUTHORITY = {
  "run": 31987036649, "job": 95263720714, "artifact": 9274246215,
  "zip": "fd414bc1328fc0422788cb9e0d9c42db6be015b871e6f262136cc6ffcdde61ab",
  "result": "4ae82181ae7271429b44347ab334bd44c8ffc30d01259bf40b9d26b0d7a57036",
  "log": "250bbac608414a347525dffcdd2c54efba07ba1aac1f4b5e6a26cfe5109d5efa",
  "headers": "42934d8e7289d6b30dba316139441719b748df8b31b19efc1def3e10af9b9dfc",
  "diagnostics": "4eba0f0371689b45b0e5a554e14f788cc128f51ff9a015fe5ba2b738773e9e94",
  "errors": 124, "warnings": 349, "panic": 0,
}
P14 = (
  ("frontier", "1118d53e64698cfe4d41da84d0a4450ad80efb4a0409b1eace0992abdfe20929"),
  ("30k47k", "671f909e011eb3a18e402c33bd4df30bcc7aa098bf928ecbf629aa8a09028686"),
  ("producer", "65a610e3dd278f084fb5f24285143f798685fd858efa9d8c92a589442a725cc0"),
  ("gl", "8a152cc89f8994eb5ab41adc21f17821e193056ae60e5e1bdc7aed75f669943e"),
  ("tail", "acd2cefb1db2b250558a362777b5e31c26fdb4dcfb23a29b4ff81f1a4c835412"),
)
# label, old, new, (line, column, code, exact message), declared downstream owner
RULES = (
("raw_differential_chain_change_to_value_equality",
"""  have hchain :
      (rawDifferential g (γ • τ)).comp (manifoldDeckDerivative γ τ) =
        (mvfderiv 𝓘(ℂ) (g.1 ∘ manifoldDeckMap γ) τ :
          ScalarOneFormValue) := by
    symm
    apply ContinuousLinearMap.ext
    intro v
    simp only [rawDifferential, manifoldDeckDerivative, mvfderiv,
      ContinuousLinearMap.comp_apply]
    rw [mfderiv_comp_apply τ hgAt hdeckAt v]
""",
"""  have hchain :
      (rawDifferential g (γ • τ)).comp (manifoldDeckDerivative γ τ) =
        (mvfderiv 𝓘(ℂ) (g.1 ∘ manifoldDeckMap γ) τ :
          ScalarOneFormValue) := by
    symm
    apply ContinuousLinearMap.ext
    intro v
    change
      NormedSpace.fromTangentSpace (g.1 (γ • τ))
          (mfderiv 𝓘(ℂ) 𝓘(ℂ) (g.1 ∘ manifoldDeckMap γ) τ v) =
        NormedSpace.fromTangentSpace (g.1 (γ • τ))
          (mfderiv 𝓘(ℂ) 𝓘(ℂ) g.1 (γ • τ)
            (mfderiv 𝓘(ℂ) 𝓘(ℂ) (manifoldDeckMap γ) τ v))
    exact congrArg
      (NormedSpace.fromTangentSpace (g.1 (γ • τ)))
      (mfderiv_comp_apply τ hgAt hdeckAt v)
""",
(28365, 8, None, "Tactic `rewrite` failed: Did not find an occurrence of the pattern"),
"probe14_frontier.raw_differential_chain_rewrite_in_goal"),
("canonical_trace_projection_opnorm_finite_synth_budget",
"""/-- Operator norm of the intrinsic trace-class projection is at most one. -/
""",
"""set_option synthInstance.maxHeartbeats 200000 in
/-- Operator norm of the intrinsic trace-class projection is at most one. -/
""",
(37213, 4, None, "failed to synthesize"), None),
("canonical_trace_projection_kernel_explicit_change",
"""  calc
    (actualFixedPhaseCanonicalTraceClassProjection n Y).ker =
        (ActualFixedPhaseCanonicalTraceClass n Y)ᗮ :=
      Submodule.ker_orthogonalProjection
    _ = ActualFixedPhaseCanonicalZeroStoredSubspace n Y :=
      Submodule.orthogonal_orthogonal
        (ActualFixedPhaseCanonicalZeroStoredSubspace n Y)
""",
"""  change
    ((ActualFixedPhaseCanonicalTraceClass n Y).orthogonalProjection).ker =
      ActualFixedPhaseCanonicalZeroStoredSubspace n Y
  rw [Submodule.ker_orthogonalProjection]
  change
    (ActualFixedPhaseCanonicalZeroStoredSubspace n Y)ᗮᗮ =
      ActualFixedPhaseCanonicalZeroStoredSubspace n Y
  exact Submodule.orthogonal_orthogonal
    (ActualFixedPhaseCanonicalZeroStoredSubspace n Y)
""",
(37262, 4, None, "invalid 'calc' step, failed to synthesize `Trans` instance"),
"probe14_30k47k.canonical_trace_projection_kernel_supply_orthogonal_argument"),
("product_collar_norm_wrapper_precedes_doc_comment",
"""/-- Exact Pythagorean identity for the stored profile/remainder split. -/
set_option maxHeartbeats 2000000 in
theorem actualFixedPhaseProductCollar_norm_sq_decomposition
""",
"""set_option maxHeartbeats 2000000 in
/-- Exact Pythagorean identity for the stored profile/remainder split. -/
theorem actualFixedPhaseProductCollar_norm_sq_decomposition
""",
(49144, 73, None, "unexpected token 'set_option'; expected 'lemma'"),
"probe14_producer.product_collar_norm_sq_finite_heartbeat_wrapper"),
("product_collar_synthesis_wrapper_precedes_doc_comment",
"""/-- Synthesize a stored collar vector from its profile and zero-trace
remainder. -/
set_option maxHeartbeats 2000000 in
noncomputable def actualFixedPhaseProductCollarCoreSynthesis
""",
"""set_option maxHeartbeats 2000000 in
/-- Synthesize a stored collar vector from its profile and zero-trace
remainder. -/
noncomputable def actualFixedPhaseProductCollarCoreSynthesis
""",
(49187, 13, None, "unexpected token 'set_option'; expected 'lemma'"),
"probe14_producer.product_collar_core_synthesis_finite_heartbeat_wrapper"),
("product_collar_synthesis_trace_finite_budget",
"""@[simp]
theorem actualFixedPhaseProductCollarCoreSynthesis_trace
""",
"""set_option maxHeartbeats 2000000 in
@[simp]
theorem actualFixedPhaseProductCollarCoreSynthesis_trace
""",
(49217, 64, None, "(deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached"),
None),
("product_collar_extension_norm_finite_budget",
"""/-- A concrete smooth-core constant also controls the dense extension on the
whole old graph completion. -/
theorem actualFixedPhaseOldGraphToProductCollarExtension_norm_le
""",
"""set_option maxHeartbeats 2000000 in
/-- A concrete smooth-core constant also controls the dense extension on the
whole old graph completion. -/
theorem actualFixedPhaseOldGraphToProductCollarExtension_norm_le
""",
(49320, 8, None, "(deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached"),
None),
)

def sha(b): return hashlib.sha256(b).hexdigest()
def blob(b): return hashlib.sha1(f"blob {len(b)}\0".encode()+b).hexdigest()
def shape(b):
  b.decode("utf-8")
  return (sha(b), blob(b), len(b), b.count(b"\n"), b.count(b"\r"), b.count(b"\0"),
          b.startswith(b"\xef\xbb\xbf"), b.endswith(b"\n"))
def trust(s):
  return (
    len(re.findall(r"\bsorry\b", s)), len(re.findall(r"\badmit\b", s)),
    len(re.findall(r"\bnative_decide\b", s)), s.count("Lean.ofReduceBool"),
    len(re.findall(r"(?m)^\s*axiom\s+", s)), len(re.findall(r"(?m)^\s*unsafe\s+", s)),
    len(re.findall(r"set_option\s+maxHeartbeats\s+0\b", s)),
  )
def expected(x):
  return (x[0], x[1], x[2], x[3], 0, 0, False, True)

def transform(raw, inverse=False):
  if shape(raw) != expected(OUT if inverse else IN):
    raise RuntimeError(f"input identity mismatch: {shape(raw)}")
  text=raw.decode("utf-8"); t0=trust(text)
  order=reversed(RULES) if inverse else RULES
  for label,old,new,header,owner in order:
    src,dst=(new,old) if inverse else (old,new)
    if text.count(src)!=1: raise RuntimeError(f"{label}: source count {text.count(src)}")
    text=text.replace(src,dst,1)
  out=text.encode("utf-8")
  if shape(out) != expected(IN if inverse else OUT):
    raise RuntimeError(f"output identity mismatch: {shape(out)}")
  t1=trust(text)
  if t0!=t1 or any(t1): raise RuntimeError(f"trust drift: {t0}->{t1}")
  audit={
    "schema":"qym.probe15.frontier-producer-p14.v1","activation":False,
    "direction":"inverse" if inverse else "forward","authority":AUTHORITY,
    "p14_components":P14,"input":shape(raw),"output":shape(out),
    "rules":[{"label":r[0],"header":{"line":r[3][0],"column":r[3][1],
      "code":r[3][2],"message":r[3][3]},"downstream_of":r[4],"occurrences":1}
      for r in RULES],
    "families":7,"occurrences":7,"direct_diagnostics":7,
    "internal_overlaps":0,"undeclared_foreign_overlaps":0,
    "trust_before":t0,"trust_after":t1,
    "inverse_exact":inverse and sha(out)==IN[0],
  }
  return out,audit

def main():
  p=argparse.ArgumentParser()
  p.add_argument("input",type=Path); p.add_argument("output",type=Path)
  p.add_argument("--inverse",action="store_true"); p.add_argument("--audit-out",type=Path)
  a=p.parse_args(); out,audit=transform(a.input.read_bytes(),a.inverse)
  a.output.write_bytes(out)
  if a.audit_out:
    a.audit_out.write_text(json.dumps(audit,indent=2,sort_keys=True)+"\n",
                           encoding="utf-8",newline="\n")
if __name__=="__main__": main()
