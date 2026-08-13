#!/usr/bin/env python3
from pathlib import Path
import base64,gzip,hashlib,json,os,re,subprocess,sys
if len(sys.argv)!=3: raise SystemExit('usage: fa_v30_theorem_v51_batch.py <source> <outdir>')
source=Path(sys.argv[1]); out=Path(sys.argv[2]); out.mkdir(parents=True,exist_ok=True)
BASE='a26135f6674fb4111307c471b92b036b2d2f4a529dba3bb67bbfd7a7e35a90ce'
PATCH='83a1b643ead78de0548cdf131b4397cafdd33254e5161b13a9b1035e3d87455a'
CAND='cf8e7d50af43b10f920efae8963f2d841161424d466183a212d0d98f05a3f84a'
PAYLOAD='H4sIAFs8fWoC/+1Y3W7bNhS+91OcS7mylDlb4ixAgARdjQ1oUS8etovCUGmZsojRJEdSsZ2rYtiT7NH6JDsUJVtuWsfehTxsM2CD+iHPd36+8+MoioCcjTRbEM7sepxTkv1MNctYSiyT4uyNTH89T4aFSN0l4Xf4XRtmYk6J6IRhCNO/v/32FqJvri4vBr3zryGsVldwe9uB7Sco4BrGCylt/mMhLaPCvpQLRVJbH9uFRwi3W87hBXCiOEnpPVlCoIii+q2eMvtqpaTA/SC6x0u4voHpuhMCcGqB4KVbA5QaDu/ikZPyUmpNyx0mviusXEitcpaO5VRy+hB/T3j2C2Xz3H7HsoxqFMQIf4sbiZXaxD+IB6oNfWXJkK3obJQTQ/FIGnO5pHqo5WJcpCkILxmBtyJcE2YoCCi6tfbTdrUvATjtR5rO2ta+NP1G+5w8UMjHxRSCFawxbNrAgOEK17XWKDs2KN+Jv8HfEIKoj0A+/vF7Fz5++NOhqiMVgCjF126PXSsa05XdezsrBK5h6a8MWyh4h7IS+ltCZrNE0PnE8UYv8bbVUsyR+SJlinAHMylPnXQigDQnYk7dCt0UBBVmf13eq7UotvdadWiDSw0A7TOq220Y5SRkOo39vfJt88eHZSMiG4EIpOvyWntpzaOqTP9c9eki15MnzDqobkWNCAv+gxRrNcgamj7v0hN4Zg/72+f/P9czjmyhL3S+2O+miZ5vAfBisptWgqCI+8+T8knNDsgB25pNwLHnTw+BtTn+CBOVTYIU2E28ayV6rNwLbbLB9LnGxXdvr+9dh9RerCcl6ZIMYUrNHsvByMU/PG4x3b9uDZNH45F9ARNnghKdpHIxZcI/c1YLHc5qaBv0v+r1v3VD26B/0Tu/2AxtQeBbw3GaazljSAztSQgWilYZfzDf4aZ+9wn0plycHjU1xlvKKdOYCf+fC3bmgk+cX08GsOlfYHcygOAz84QfurbVKbBNdZS03k5vCm6Z4tU/DpuNpwi1owtL0yRRkz1PDHGaWnl4c7l1zoudkSIInnHUqZqAI3ruvfNuoiQTdok5teeP36NvzYOwMs0Xo/6gJmJbrT+t9kdS5aje4F/XGfTALAqeuJ9Jzc1DvH2Io11SxCzYgQ6cRRHcUyZmdIV3wOYUyhoc4UpEflzBgqukYWXBJamWxsD7QIT9btS/Ee+rRGGqCnx1cdm7dAX46nLQG1T116XphzoXp4hkRC2ay0gxlDpFwU1k+MqCqOSRatkDJgQ2BG6daGd9b4uM19g3B4EizCllgMwJE8aWuqClC8LRlM4FkDnXRMr5BhwKMFQRdCAm/uoNU4cAwE+4XWkpM7DUWANLhs/dmbMqAFIKzBrKMyBi5p5g0Bq0w1+lk/fQvRYAAA=='
before=source.read_bytes(); bt=before.decode(); base=hashlib.sha256(before).hexdigest(); assert base==BASE,(base,BASE)
if os.environ.get('BASE_SOURCE_SHA256'): assert base==os.environ['BASE_SOURCE_SHA256']
pb=gzip.decompress(base64.b64decode(PAYLOAD)); assert hashlib.sha256(pb).hexdigest()==PATCH
(out/'decoded.patch').write_bytes(pb)
p=subprocess.run(['patch','-p1','--batch','--forward'],input=pb,capture_output=True); (out/'patch.stdout').write_bytes(p.stdout); (out/'patch.stderr').write_bytes(p.stderr); assert p.returncode==0,(p.returncode,p.stdout,p.stderr)
after=source.read_bytes(); at=after.decode(); cand=hashlib.sha256(after).hexdigest(); assert cand==CAND,(cand,CAND); assert len(at.splitlines())==61440
decl=re.compile(r'(?m)^(?:protected\s+|private\s+|noncomputable\s+|local\s+)*(?:theorem|lemma|def|abbrev|instance|structure|class)\s+([^\s(:]+)'); assert decl.findall(bt)==decl.findall(at)
th=re.compile(r'(?m)^(?:protected\s+|private\s+|noncomputable\s+|local\s+)*(theorem|lemma)\s+([^\s(:]+)')
def headers(s):
    starts=[m.start() for m in decl.finditer(s)]; r=[]
    for m in th.finditer(s):
        nxt=next((x for x in starts if x>m.start()),len(s)); block=s[m.start():nxt]; cut=block.find(':= by')
        if cut<0: cut=block.find(':=')
        r.append((m.group(2),re.sub(r'\s+',' ',block if cut<0 else block[:cut]).strip()))
    return r
assert headers(bt)==headers(at)
forbidden=['sorry','admit','axiom','unsafe','native_decide','Lean.ofReduceBool','set_option']; counts={}
for w in forbidden:
    pat=r'(?<![A-Za-z0-9_])'+re.escape(w)+r'(?![A-Za-z0-9_])'; counts[w]=[len(re.findall(pat,bt)),len(re.findall(pat,at))]
assert all(a==b for a,b in counts.values()),counts
audit={'schema':'fa-v30-theorem-v51-strict-v1','base_source_sha256':BASE,'patch_sha256':PATCH,'candidate_sha256':CAND,'candidate_bytes':len(after),'candidate_lines':len(at.splitlines()),'repairs':['3646_nested_double_subtype_ext_bridge','3650_nested_double_subtype_ext_bridge','3659_zero_application'],'semantic_public_proposition_change':False,'theorem_lemma_headers_identical':True,'declaration_sequence_identical':True,'forbidden_lexical_counts_preserved':True,'forbidden_lexical_counts_before_after':counts,'patch_transport':'inline_gzip_base64_locked'}
(out/'PATCH_AUDIT.json').write_text(json.dumps(audit,indent=2,sort_keys=True)+'\n'); (out/'candidate.sha256').write_text(CAND+'\n'); print(json.dumps(audit,indent=2,sort_keys=True))
