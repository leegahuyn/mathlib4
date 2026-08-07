#!/usr/bin/env bash
set -euo pipefail

BASE='scripts/ci_pass339_final_fa_mock3_qym_loop.sh'
test -f "${BASE}"

python3 - <<'PY'
from pathlib import Path

path = Path('scripts/ci_pass339_final_fa_mock3_qym_loop.sh')
source = path.read_text(encoding='utf-8')


def replace_once(old: str, new: str, label: str) -> None:
    global source
    count = source.count(old)
    print(f'{label}: expected=1 actual={count}')
    if count != 1:
        raise SystemExit(f'{label}: expected one occurrence, found {count}')
    source = source.replace(old, new)

replace_once(
    "mkdir -p \"${EVIDENCE}/logs\" \"${EVIDENCE}/source\" \"${EVIDENCE}/artifacts\" \"${OUTDIR}\"\n",
    """mkdir -p \"${EVIDENCE}/logs\" \"${EVIDENCE}/source\" \"${EVIDENCE}/artifacts\" \"${OUTDIR}\"

preserve_exit_evidence() {
  local code=$?
  mkdir -p \"${EVIDENCE}/source\" \"${EVIDENCE}/logs\"
  if [[ -f \"${FA}\" ]]; then
    cp \"${FA}\" \"${EVIDENCE}/source/Mock2_FunctionalAnalysis-on-exit.lean\" || true
    sha256sum \"${FA}\" > \"${EVIDENCE}/source/Mock2_FunctionalAnalysis-on-exit.sha256\" || true
  fi
  git diff -- \"${FA}\" \"${INTEGRATED}\" \"${QYM}\" > \"${EVIDENCE}/source/on-exit.patch\" || true
  printf 'exit_code=%s\\n' \"${code}\" > \"${EVIDENCE}/exit-status.txt\"
}
trap preserve_exit_evidence EXIT
""",
    'exit evidence trap',
)

replace_once(
    """cp \"${FA}\" \"${EVIDENCE}/source/Mock2_FunctionalAnalysis-pass339.lean\"

# Accept a direct PASS 339 success immediately; otherwise invoke the existing
# statement-preserving repair agents with the PASS 339 candidate as input.
fa_ok=0
""",
    """cp \"${FA}\" \"${EVIDENCE}/source/Mock2_FunctionalAnalysis-pass339.lean\"

# Run the PASS 339-specific statement-preserving frontier agent first. It only
# keeps a patch when the actual compiler frontier advances.
export PASS_BASELINE=339
export BASELINE_PASS=339
export BASELINE_SHA256=\"${PASS339_SHA}\"
export EXPECTED_INPUT_SHA256=\"${PASS339_SHA}\"
export TARGET_FILE=\"${FA}\"
export TARGET_SOURCE=\"${FA}\"
export LEAN_FILE=\"${FA}\"
export TARGET_MODULE='Mock2_FunctionalAnalysis'
export MODULE='Mock2_FunctionalAnalysis'
export PASS339_AGENT_ROUNDS=24
export PASS339_AGENT_MAX_ERRORS=40
export EVIDENCE_DIR=\"${EVIDENCE}/targeted-agent\"
export BRANCH=\"${TARGET_BRANCH}\"
export GH_TOKEN=\"${GH_TOKEN:-${GITHUB_TOKEN:-}}\"
export MODELS_TOKEN=\"${GH_TOKEN:-${GITHUB_TOKEN:-}}\"
mkdir -p \"${EVIDENCE_DIR}\"
set +e
python3 scripts/pass339_targeted_lean_repair_agent.py \\
  2>&1 | tee \"${EVIDENCE}/logs/pass339-targeted-agent.log\"
targeted_agent_code=${PIPESTATUS[0]}
set -e
printf 'targeted_agent_code=%s\\n' \"${targeted_agent_code}\" \\
  | tee -a \"${EVIDENCE}/snapshot.txt\"

# Accept the targeted agent only through two fresh direct Lean compilations;
# otherwise retain the older constrained agents as fallbacks.
fa_ok=0
""",
    'targeted agent insertion',
)

out = Path('/tmp/ci_pass339_final_fa_mock3_qym_loop_v2.generated.sh')
out.write_text(source, encoding='utf-8')
out.chmod(0o755)
PY

bash -n /tmp/ci_pass339_final_fa_mock3_qym_loop_v2.generated.sh
exec bash /tmp/ci_pass339_final_fa_mock3_qym_loop_v2.generated.sh
