#!/usr/bin/env python3
from pathlib import Path

path = Path('scripts/focused_qym_direct_v5_20260807.sh')
text = path.read_text(encoding='utf-8')
anchor = """PY

git status --porcelain=v1 > \"$LOGDIR/final-status.txt\"; test ! -s \"$LOGDIR/final-status.txt\"
"""
insert = """PY

# Stronger whole-environment audit when this Lean version exposes source-file
# declaration metadata.  The dispatcher falls back to the already required
# public theorem/lemma audit without weakening the allowed-axiom policy.
mkdir -p \"$LOGDIR/comprehensive-axiom\"
FOCUSED_LOGDIR=\"$LOGDIR/comprehensive-axiom\" \\
  bash scripts/focused_axiom_audit_dispatch_20260807.sh \"$LOGDIR/comprehensive-axiom\"
python3 - \"$LOGDIR/axiom-summary.json\" \"$LOGDIR/comprehensive-axiom/axiom-audit-summary.json\" <<'PY'
import json,sys
public=json.load(open(sys.argv[1])); comprehensive=json.load(open(sys.argv[2]))
assert public['sorryAx']==0 and public['nonstandard_axioms']==[]
assert comprehensive['sorryAx']==0 and comprehensive['nonstandard_axioms']==[]
observed=sorted(set(public.get('observed_axioms',[])) | set(comprehensive.get('observed_axioms',[])))
public['observed_axioms']=observed
public['comprehensive_mode']=comprehensive.get('mode')
public['comprehensive_checked_declarations']=comprehensive.get('checked_declarations')
open(sys.argv[1],'w').write(json.dumps(public,indent=2)+'\\n')
PY

git status --porcelain=v1 > \"$LOGDIR/final-status.txt\"; test ! -s \"$LOGDIR/final-status.txt\"
"""
if 'comprehensive_checked_declarations' not in text:
    if anchor not in text:
        raise SystemExit('QYM axiom block anchor missing')
    text = text.replace(anchor, insert)
path.write_text(text, encoding='utf-8')
