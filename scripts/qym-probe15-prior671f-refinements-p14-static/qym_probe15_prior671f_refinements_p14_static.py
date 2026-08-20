#!/usr/bin/env python3
"""Activation-disabled, reversible exact-P14 refinements for six prior-671f survivors."""
from __future__ import annotations
import argparse
import hashlib
import json
import re
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
sys.dont_write_bytecode = True
SCHEMA = "qym-probe15-prior671f-refinements-exact-p14-v2-self-contained"
ACTIVATION = False
INPUT_SHA256 = "e8ac0ba15f35c88792552a0d55d789c222d360a10d30c3cedb0ce0a8dfb879b7"
INPUT_GIT_BLOB = "49b71abd253e0b1292ecacd9ebc984fa9ea3d9de"
INPUT_BYTES = 2_940_390
INPUT_LF = 62_158
OUTPUT_SHA256 = "370280e74ac86101ed1f787b17cec2fe85677882c95dc0a34c6448c31f4178fc"
OUTPUT_GIT_BLOB = "e79b780e06ba5422edfdc787401a65d8c10d5481"
OUTPUT_BYTES = 2_940_557
OUTPUT_LF = 62_161
AUTHORITY = {"run_id": 31987036649, "job_id": 95263720714, "artifact_id": 9274246215,
 "result_sha256": "4ae82181ae7271429b44347ab334bd44c8ffc30d01259bf40b9d26b0d7a57036",
 "log_sha256": "250bbac608414a347525dffcdd2c54efba07ba1aac1f4b5e6a26cfe5109d5efa",
 "headers_sha256": "42934d8e7289d6b30dba316139441719b748df8b31b19efc1def3e10af9b9dfc",
 "diagnostics_sha256": "4eba0f0371689b45b0e5a554e14f788cc128f51ff9a015fe5ba2b738773e9e94",
 "errors": 124, "warnings": 349, "panic": 0, "exit": 1}
AUDITED_PRECEDENT_HELPERS = {
 "p12_36k42k": ("qym-probe12-36k42k-p11-reanchored/qym_probe12_36k42k_p11_reanchored.py", "5bd02f57232ac30c336b3e13574b7cba4dc4b0998f159e3fdebd41ed6354a365"),
 "p14_671f": ("qym-probe14-30k47k-p13-reanchored/qym_probe14_30k47k_p13_reanchored.py", "671f909e011eb3a18e402c33bd4df30bcc7aa098bf928ecbf629aa8a09028686"),
 "cc579": ("qym-probe15-contdiff-p13-sequenced/qym_probe15_contdiff_p13_sequenced.py", "cc57982d31c456b496ee8cb1d39d5f9387f9e9108d9406d3485e74378bfc01b1")}

@dataclass(frozen=True)
class Header:
 line: int
 column: int
 message: str
 code: str | None = None
 kind: str = "direct"
@dataclass(frozen=True)
class Rule:
 label: str
 old: str
 new: str
 headers: tuple[Header, ...]
 consumed_owner: str
 consumed_rule: str
 consumed_relation: str
 occurrences: int = 1
_ROWS = json.loads('[{"label":"tile_height_open_map_cast_sl_to_gl_homeomorph","old":"  exact UpperHalfPlane.isOpenMap_im.comp\\n    (Homeomorph.smul (gammaTwoCosetRep q)⁻¹ : ℍ ≃ₜ ℍ).isOpenMap\\n","new":"  exact UpperHalfPlane.isOpenMap_im.comp\\n    (Homeomorph.smul\\n      (((gammaTwoCosetRep q)⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) :\\n        ℍ ≃ₜ ℍ).isOpenMap\\n","headers":[{"line":38453,"column":5,"message":"failed to synthesize instance of type class","code":"lean.synthInstanceFailed","kind":"direct"}],"consumed_owner":"p12_36k42k","consumed_rule":"tile_height_open_map_pin_action_homeomorph","consumed_relation":"own_old_equals_consumed_new","occurrences":1},{"label":"saturated_stage_retype_effective_witness_as_sl_action","old":"  rcases effective_exists_gamma a with ⟨gamma, hgamma⟩\\n  change a • u = z at hau\\n  calc\\n","new":"  rcases effective_exists_gamma a with ⟨gamma, hgamma⟩\\n  change ∀ v : ℍ, a • v = (gamma : SL(2, ℤ)) • v at hgamma\\n  change a • u = z at hau\\n  calc\\n","headers":[{"line":39022,"column":41,"message":"unsolved goals","code":null,"kind":"direct"}],"consumed_owner":"p12_36k42k","consumed_rule":"saturated_stage_beta_reduce_effective_action_witness","consumed_relation":"own_old_equals_consumed_new","occurrences":1},{"label":"tile_envelope_continuity_cast_inverse_sl_to_gl","old":"      (gammaTwoModularHeightEnvelope_continuous.comp\\n        (Homeomorph.smul (gammaTwoCosetRep q)⁻¹ : ℍ ≃ₜ ℍ).continuous)\\n","new":"      (gammaTwoModularHeightEnvelope_continuous.comp\\n        (Homeomorph.smul\\n          (((gammaTwoCosetRep q)⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) :\\n            ℍ ≃ₜ ℍ).continuous)\\n","headers":[{"line":39170,"column":9,"message":"failed to synthesize instance of type class","code":"lean.synthInstanceFailed","kind":"direct"}],"consumed_owner":"p12_36k42k","consumed_rule":"tile_envelope_open_neighborhood_pin_action_homeomorph","consumed_relation":"own_old_equals_consumed_new","occurrences":1},{"label":"eta_continuity_compose_upperhalfplane_then_curve","old":"  have heta : Continuous\\n      (fun x : ℝ =>\\n        ModularForm.eta\\n          ((actualFixedPhaseCuspHorocyclePoint kappa Y x : ℍ) : ℂ)) := by\\n    rw [continuous_iff_continuousAt]\\n    intro x\\n    exact\\n      (ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet\\n        (actualFixedPhaseCuspHorocyclePoint kappa Y x).2).continuousAt.comp\'\\n          hcoe.continuousAt\\n","new":"  have heta : Continuous\\n      (fun x : ℝ =>\\n        ModularForm.eta\\n          ((actualFixedPhaseCuspHorocyclePoint kappa Y x : ℍ) : ℂ)) :=\\n    Mock2FA.PaperCorrections.AutomorphicSobolev.HalfIntegralMultiplier.continuous_eta_upperHalfPlane.comp\\n      hpoint\\n","headers":[{"line":41343,"column":10,"message":"Application type mismatch: The argument","code":null,"kind":"direct"}],"consumed_owner":"p14_671f","consumed_rule":"eta_continuity_compose_full_composite_with_comp_prime","consumed_relation":"own_old_strictly_contains_consumed_new","occurrences":1},{"label":"selected_cusp_circle_change_to_typed_quotient_map","old":"  rw [isQuotientMap_quotient_mk\'.continuous_iff]\\n  have hfun : selectedCuspCircle q Y ∘\\n      QuotientAddGroup.mk\' (AddSubgroup.zmultiples (2 : ℝ)) =\\n      QYM.FullCertification.P2ConnectedCuspComponentsExtension.selectedCuspQuotientLoop q Y := by\\n    funext t\\n    exact selectedCuspCircle_coe q Y t\\n  rw [hfun]\\n  exact\\n    QYM.FullCertification.P2ConnectedCuspComponentsExtension.selectedCuspQuotientLoop_continuous q Y\\n","new":"  rw [isQuotientMap_quotient_mk\'.continuous_iff]\\n  have hfun : selectedCuspCircle q Y ∘\\n      QuotientAddGroup.mk\' (AddSubgroup.zmultiples (2 : ℝ)) =\\n      QYM.FullCertification.P2ConnectedCuspComponentsExtension.selectedCuspQuotientLoop q Y := by\\n    funext t\\n    exact selectedCuspCircle_coe q Y t\\n  change Continuous (selectedCuspCircle q Y ∘\\n    QuotientAddGroup.mk\' (AddSubgroup.zmultiples (2 : ℝ)))\\n  rw [hfun]\\n  exact\\n    QYM.FullCertification.P2ConnectedCuspComponentsExtension.selectedCuspQuotientLoop_continuous q Y\\n","headers":[{"line":45067,"column":6,"message":"Tactic `rewrite` failed: Did not find an occurrence of the pattern","code":null,"kind":"direct"}],"consumed_owner":"p14_671f","consumed_rule":"selected_cusp_circle_pin_add_circle_quotient_map","consumed_relation":"own_old_strictly_contains_consumed_new","occurrences":1},{"label":"negative_horocycle_derivative_unfold_function_comp","old":"  have h := (selectedHorocycleCoordinate_hasDerivAt q Y (-t)).scomp t\\n    (hasDerivAt_neg t)\\n  simpa only [Function.comp_apply, selectedHorocycleBoundaryVelocity,\\n    neg_smul, one_smul] using h\\n","new":"  have h := (selectedHorocycleCoordinate_hasDerivAt q Y (-t)).scomp t\\n    (hasDerivAt_neg t)\\n  simpa only [Function.comp_def, selectedHorocycleBoundaryVelocity,\\n    neg_smul, one_smul] using h\\n","headers":[{"line":47252,"column":2,"message":"Type mismatch","code":null,"kind":"direct"}],"consumed_owner":"p14_671f","consumed_rule":"negative_horocycle_derivative_normalize_comp_and_neg_smul","consumed_relation":"own_old_equals_consumed_new","occurrences":1}]')
RULES = tuple(Rule(headers=tuple(Header(**h) for h in row.pop("headers")), **row) for row in _ROWS)
del _ROWS

def sha256(raw: bytes) -> str:
 return hashlib.sha256(raw).hexdigest()
def git_blob(raw: bytes) -> str:
 return hashlib.sha1(b"blob " + str(len(raw)).encode("ascii") + b"\0" + raw).hexdigest()
def shape(raw: bytes) -> dict[str, object]:
 raw.decode("utf-8", errors="strict")
 return {"sha256":sha256(raw),"git_blob":git_blob(raw),"bytes":len(raw),"lf":raw.count(b"\n"),
  "cr":b"\r" in raw,"nul":b"\0" in raw,"bom":raw.startswith(b"\xef\xbb\xbf"),"terminal_lf":raw.endswith(b"\n")}
def trust(text: str) -> dict[str, int]:
 ps={"sorry":r"\bsorry\b","admit":r"\badmit\b","native_decide":r"\bnative_decide\b","Lean.ofReduceBool":r"\bLean\.ofReduceBool\b","axiom":r"(?m)^\s*axiom\s+","unsafe":r"(?m)^\s*unsafe\s+","maxHeartbeats_zero":r"set_option\s+maxHeartbeats\s+0"}
 return {k:len(re.findall(v,text)) for k,v in ps.items()}
def collision_audit(text: str) -> dict[str, object]:
 spans=[]
 for r in RULES:
  if text.count(r.old)!=r.occurrences or text.count(r.new)!=0: raise RuntimeError(f"{r.label}: applied-state drift")
  p=text.index(r.old); spans.append((p,p+len(r.old),r.label))
 for i,a in enumerate(spans):
  for b in spans[i+1:]:
   if max(a[0],b[0])<min(a[1],b[1]): raise RuntimeError(f"span collision: {a[2]}/{b[2]}")
 declared=[{"rule":r.label,"owner":r.consumed_owner,"consumed_rule":r.consumed_rule,"relation":r.consumed_relation} for r in RULES]
 return {"status":"PASS","own_span_overlaps":0,"declared_consumed_overlaps":len(declared),"undeclared_overlaps":0,"records":declared}
def transform(text: str, inverse: bool=False) -> tuple[str,list[dict[str,object]]]:
 audit=[]
 for r in (tuple(reversed(RULES)) if inverse else RULES):
  src,dst=(r.new,r.old) if inverse else (r.old,r.new)
  if text.count(src)!=r.occurrences or text.count(dst)!=0: raise RuntimeError(f"{r.label}: anchor state mismatch")
  text=text.replace(src,dst)
  audit.append({"label":r.label,"direction":"inverse" if inverse else "forward","occurrences":r.occurrences,"headers":[asdict(h) for h in r.headers],"consumed_owner":r.consumed_owner,"consumed_rule":r.consumed_rule,"consumed_relation":r.consumed_relation})
 return text,audit
apply_rules=transform
def main() -> None:
 p=argparse.ArgumentParser(); p.add_argument("--input",type=Path,required=True); p.add_argument("--output",type=Path,required=True); p.add_argument("--audit",type=Path,required=True); p.add_argument("--inverse",action="store_true"); a=p.parse_args()
 if a.output.exists() or a.audit.exists(): raise RuntimeError("refusing overwrite")
 raw=a.input.read_bytes(); actual=shape(raw); src=(OUTPUT_SHA256,OUTPUT_GIT_BLOB,OUTPUT_BYTES,OUTPUT_LF) if a.inverse else (INPUT_SHA256,INPUT_GIT_BLOB,INPUT_BYTES,INPUT_LF)
 if tuple(actual[k] for k in ("sha256","git_blob","bytes","lf"))!=src: raise RuntimeError("source identity mismatch")
 if actual["cr"] or actual["nul"] or actual["bom"] or not actual["terminal_lf"]: raise RuntimeError("text hygiene mismatch")
 text=raw.decode("utf-8"); collisions={"status":"SKIPPED_INVERSE"} if a.inverse else collision_audit(text); result,rows=transform(text,a.inverse); result_raw=result.encode(); got=shape(result_raw); dst=(INPUT_SHA256,INPUT_GIT_BLOB,INPUT_BYTES,INPUT_LF) if a.inverse else (OUTPUT_SHA256,OUTPUT_GIT_BLOB,OUTPUT_BYTES,OUTPUT_LF)
 if tuple(got[k] for k in ("sha256","git_blob","bytes","lf"))!=dst: raise RuntimeError("result identity mismatch")
 tc=trust(result)
 if any(tc.values()): raise RuntimeError(f"trust failure: {tc}")
 restored,_=transform(result,not a.inverse)
 if restored.encode()!=raw: raise RuntimeError("inverse byte mismatch")
 a.output.write_bytes(result_raw); record={"schema":SCHEMA,"activation":ACTIVATION,"status":"STATIC_PASS_EXACT_P14_NOT_LEAN_EXECUTED","mode":"inverse" if a.inverse else "forward","authority":AUTHORITY,"source":actual,"result":got,"rules":rows,"collision_audit":collisions,"trust":tc,"inverse_byte_equal":True,"runtime_dependencies":["Python standard library only"],"audited_precedent_helpers":AUDITED_PRECEDENT_HELPERS,"execution":{"lean":False,"lake":False,"git":False,"network":False,"remote":False,"canonical_source_mutation":False}}
 a.audit.write_text(json.dumps(record,ensure_ascii=False,indent=2)+"\n",encoding="utf-8",newline="\n")
if __name__=="__main__": main()
