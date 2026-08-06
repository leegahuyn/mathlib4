#!/usr/bin/env bash
set -euo pipefail

LOGDIR="${1:-/tmp/focused-proof/direct-v3}"
mkdir -p "${LOGDIR}"

if bash scripts/focused_environment_axiom_audit_20260807.sh "${LOGDIR}"; then
  python3 - "${LOGDIR}" <<'PY' > "${LOGDIR}/axiom-audit-summary.json"
from pathlib import Path
import json, re, sys
logdir = Path(sys.argv[1])
text = (logdir / 'environment-axiom-audit.log').read_text(errors='replace')
text = re.sub(r'\x1b\[[0-9;]*m', '', text)
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
if 'sorryAx' in text:
    raise SystemExit('sorryAx found in environment axiom audit')
checked = re.search(r'focused_checked_declarations=([0-9]+)', text)
observed = re.search(r'focused_observed_axioms=\[(.*?)\]', text, re.S)
if not checked or int(checked.group(1)) == 0 or not observed:
    raise SystemExit('environment axiom audit did not emit a complete result')
seen = {x.strip() for x in observed.group(1).split(',') if x.strip()}
bad = sorted(seen - allowed)
report = {
    'mode': 'environment-source-file-declarations',
    'checked_declarations': int(checked.group(1)),
    'allowed_axioms': sorted(allowed),
    'observed_axioms': sorted(seen),
    'nonstandard_axioms': bad,
    'sorryAx': 0,
}
print(json.dumps(report, indent=2))
if bad:
    raise SystemExit('nonstandard axioms: ' + ', '.join(bad))
PY
  exit 0
fi

# Compatibility fallback for Lean versions that do not expose a usable
# declaration-to-source-file accessor.  Static scanning has already ruled out
# new global axiom declarations; this pass checks every public theorem/lemma.
python3 scripts/generate_focused_axiom_audit_20260807.py \
  --output /tmp/focused_axiom_audit_fallback_20260807.lean \
  PrimalitySheafVerification/Mock2_Advanced.lean \
  PrimalitySheafVerification/Mock2_FunctionalAnalysis_Integrated.lean \
  PrimalitySheafVerification/QYM.lean \
  > "${LOGDIR}/axiom-fallback-generation.txt"

generated_count="$(grep -oE 'generated_declaration_count=[0-9]+' "${LOGDIR}/axiom-fallback-generation.txt" | cut -d= -f2)"
[[ "${generated_count}" =~ ^[0-9]+$ ]]
[[ "${generated_count}" -gt 0 ]]

set +e
lake env lean /tmp/focused_axiom_audit_fallback_20260807.lean \
  > "${LOGDIR}/axiom-fallback.log" 2>&1
code=$?
set -e
echo "${code}" > "${LOGDIR}/axiom-fallback.exit"
if [[ "${code}" -ne 0 ]]; then
  tail -250 "${LOGDIR}/axiom-fallback.log" > "${LOGDIR}/axiom-audit.tail.txt" || true
  exit "${code}"
fi

python3 - "${LOGDIR}" "${generated_count}" <<'PY' > "${LOGDIR}/axiom-audit-summary.json"
from pathlib import Path
import json, re, sys
logdir = Path(sys.argv[1])
checked = int(sys.argv[2])
text = (logdir / 'axiom-fallback.log').read_text(errors='replace')
text = re.sub(r'\x1b\[[0-9;]*m', '', text)
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
if 'sorryAx' in text:
    raise SystemExit('sorryAx found in fallback axiom audit')
seen = set()
for match in re.finditer(r'depends on axioms:\s*\[(.*?)\]', text, re.S):
    for raw in match.group(1).split(','):
        name = raw.strip()
        if name:
            seen.add(name)
bad = sorted(seen - allowed)
report = {
    'mode': 'all-public-theorem-lemma-fallback',
    'checked_declarations': checked,
    'allowed_axioms': sorted(allowed),
    'observed_axioms': sorted(seen),
    'nonstandard_axioms': bad,
    'sorryAx': 0,
}
print(json.dumps(report, indent=2))
if bad:
    raise SystemExit('nonstandard axioms: ' + ', '.join(bad))
PY
