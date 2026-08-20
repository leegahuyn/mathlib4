#!/usr/bin/env python3
from pathlib import Path

path = Path('scripts/focused_direct_verify_20260807.sh')
text = path.read_text(encoding='utf-8')
start = text.find('# Audit every public theorem/lemma declaration in the substantive focused modules.')
end = text.find('\nsha256sum \\\n', start)
if start < 0 or end < 0:
    raise SystemExit('old axiom-audit block anchors not found')
new = r'''# Audit every declaration whose Lean source file is one of the three
# substantive focused modules.  The environment audit follows generated and
# non-theorem declarations as well, and rejects every axiom outside the
# explicitly allowed kernel set.
bash scripts/focused_environment_axiom_audit_20260807.sh "${LOGDIR}"

python3 - <<'PY' | tee "${LOGDIR}/axiom-audit-summary.json"
from pathlib import Path
import json, os, re

allowed = {"propext", "Classical.choice", "Quot.sound"}
logdir = Path(os.environ.get("FOCUSED_LOGDIR", "/tmp/focused-proof/direct-v3"))
text = (logdir / "environment-axiom-audit.log").read_text(errors="replace")
text = re.sub(r"\x1b\[[0-9;]*m", "", text)
if "sorryAx" in text:
    raise SystemExit("sorryAx found in environment axiom audit")
checked_match = re.search(r"focused_checked_declarations=([0-9]+)", text)
if not checked_match or int(checked_match.group(1)) == 0:
    raise SystemExit("environment axiom audit matched no focused declarations")
observed_match = re.search(r"focused_observed_axioms=\[(.*?)\]", text, re.S)
if not observed_match:
    raise SystemExit("observed axiom set was not printed")
seen = {name.strip() for name in observed_match.group(1).split(",") if name.strip()}
nonstandard = sorted(seen - allowed)
report = {
    "checked_declarations": int(checked_match.group(1)),
    "allowed_axioms": sorted(allowed),
    "observed_axioms": sorted(seen),
    "nonstandard_axioms": nonstandard,
    "sorryAx": 0,
}
print(json.dumps(report, indent=2))
if nonstandard:
    raise SystemExit("nonstandard axioms detected: " + ", ".join(nonstandard))
PY
'''
text = text[:start] + new + text[end + 1:]
text = text.replace(
    'cp /tmp/focused_axiom_audit_20260807.lean "${LOGDIR}/focused_axiom_audit_20260807.lean"\n',
    '',
)
path.write_text(text, encoding='utf-8')
if 'generate_focused_axiom_audit_20260807.py' in path.read_text(encoding='utf-8'):
    # The variable declaration is no longer needed either.
    data = path.read_text(encoding='utf-8').replace(
        "AXIOM_GENERATOR='scripts/generate_focused_axiom_audit_20260807.py'\n", ""
    )
    path.write_text(data, encoding='utf-8')
