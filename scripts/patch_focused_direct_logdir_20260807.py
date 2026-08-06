#!/usr/bin/env python3
from pathlib import Path

path = Path('scripts/focused_direct_verify_20260807.sh')
text = path.read_text(encoding='utf-8')
old = '''from pathlib import Path
import json, re

allowed = {"propext", "Classical.choice", "Quot.sound"}
text = Path("/tmp/focused-proof/direct-v3/axiom-audit.log").read_text(errors="replace")
'''
new = '''from pathlib import Path
import json, os, re

allowed = {"propext", "Classical.choice", "Quot.sound"}
logdir = Path(os.environ.get("FOCUSED_LOGDIR", "/tmp/focused-proof/direct-v3"))
text = (logdir / "axiom-audit.log").read_text(errors="replace")
'''
if old in text:
    text = text.replace(old, new)
path.write_text(text, encoding='utf-8')
if 'Path("/tmp/focused-proof/direct-v3/axiom-audit.log")' in path.read_text(encoding='utf-8'):
    raise SystemExit('hard-coded axiom log path remains')
