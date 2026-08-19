#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,re,sys
BASE_SHA="790b40c05a8f3735dd171a135eda65de92ab68b247d13e7e2ffe2968e3798421"
BASE_BLOB="33e4fab1130e4c17ea5d212fe2691c3e0c0eb8d3"
HEAD='''theorem edgeParameterTransport_hasDerivAt\n    (e : QYM.FullCertification.PolygonTraceExtension.PolygonEdge) (t : ℝ) :\n    HasDerivAt (QYM.FullCertification.P2NormalGreenExtension.edgeParameterTransport e)\n      (e.2.parameterSign : ℝ) t := by\n'''
VARIANTS={
"letI_simpa":HEAD+'''  letI : AddCommGroup ℝ := Real.instAddCommGroup\n  letI : Module ℝ ℝ := Semiring.toModule\n  simpa [QYM.FullCertification.P2NormalGreenExtension.edgeParameterTransport] using\n    (hasDerivAt_id t).const_mul (e.2.parameterSign : ℝ)\n''',
"letI_change":HEAD+'''  letI : AddCommGroup ℝ := Real.instAddCommGroup\n  letI : Module ℝ ℝ := Semiring.toModule\n  change HasDerivAt (fun x : ℝ => (e.2.parameterSign : ℝ) * x)\n    (e.2.parameterSign : ℝ) t\n  exact (hasDerivAt_id t).const_mul (e.2.parameterSign : ℝ)\n''',
"transparent_simpa":'''set_option backward.isDefEq.respectTransparency false in\ntheorem edgeParameterTransport_hasDerivAt\n    (e : QYM.FullCertification.PolygonTraceExtension.PolygonEdge) (t : ℝ) :\n    HasDerivAt (QYM.FullCertification.P2NormalGreenExtension.edgeParameterTransport e)\n      (e.2.parameterSign : ℝ) t := by\n  simpa [QYM.FullCertification.P2NormalGreenExtension.edgeParameterTransport] using\n    (hasDerivAt_id t).const_mul (e.2.parameterSign : ℝ)\n''',
}
RE=re.compile(r'(?ms)^theorem edgeParameterTransport_hasDerivAt\b.*?(?=^/-- Exact derivative of the transported target curve\.)')
def blob(b):return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def audit(t):return {"sorry":len(re.findall(r'\bsorry\b',t)),"admit":len(re.findall(r'\badmit\b',t)),"native_decide":len(re.findall(r'\bnative_decide\b',t)),"Lean.ofReduceBool":t.count('Lean.ofReduceBool'),"global_axiom":len(re.findall(r'(?m)^\s*axiom\s+',t)),"unsafe":len(re.findall(r'(?m)^\s*unsafe\s+',t)),"maxHeartbeats_zero":len(re.findall(r'set_option\s+maxHeartbeats\s+0\b',t))}
def main():
 v,p=sys.argv[1],Path(sys.argv[2]); raw=p.read_bytes()
 if v not in VARIANTS:raise SystemExit('bad variant')
 if hashlib.sha256(raw).hexdigest()!=BASE_SHA or blob(raw)!=BASE_BLOB:raise SystemExit('not exact GB79')
 t=raw.decode(); a=audit(t); ms=list(RE.finditer(t))
 if len(ms)!=1:raise SystemExit(f'target count {len(ms)}')
 m=ms[0]; t=t[:m.start()]+VARIANTS[v].rstrip()+'\n\n'+t[m.end():]
 if audit(t)!=a:raise SystemExit('forbidden delta')
 marker='theorem pairedTransportCoordinate_hasDerivAt'; gate=t.count('\n',0,t.index(marker))+1
 p.write_text(t); out=p.read_bytes()
 print(json.dumps({'variant':v,'input_sha256':BASE_SHA,'candidate_sha256':hashlib.sha256(out).hexdigest(),'candidate_blob':blob(out),'gate_line':gate,'forbidden':a},indent=2,sort_keys=True))
if __name__=='__main__':main()
