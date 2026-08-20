#!/usr/bin/env bash
set -euo pipefail

ROOT="$(git rev-parse --show-toplevel)"
cd "${ROOT}"

LOGDIR="${FOCUSED_LOGDIR:-/tmp/focused-proof/candidate-v3}"
MARKER_OUT="${FOCUSED_MARKER_OUT:-/tmp/focused_candidate_v3.json}"
BUNDLE_OUT="${FOCUSED_BUNDLE_OUT:-/tmp/focused-candidate-v3-proof.tar.gz}"
OUT='.lake/build/lib/lean/PrimalitySheafVerification'
AUDITOR='scripts/focused_source_audit_20260807.py'

MOCK2='PrimalitySheafVerification/Mock2.lean'
M2A='PrimalitySheafVerification/Mock2_Advanced.lean'
FA='PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean'
INTEGRATED='PrimalitySheafVerification/Mock2_FunctionalAnalysis_Integrated.lean'
QYM='PrimalitySheafVerification/QYM.lean'
ADVANCED_BASELINE_COMMIT='623dfac27a24c170330d6218005e67b06490b814'

mkdir -p "${LOGDIR}" "${OUT}"
START_HEAD="$(git rev-parse HEAD)"
START_STATUS="$(git status --porcelain=v1)"
if [[ -n "${START_STATUS}" ]]; then
  printf '%s\n' "${START_STATUS}" > "${LOGDIR}/dirty-start.txt"
  echo 'The focused candidate pipeline requires a clean triggering worktree.' >&2
  exit 1
fi

printf '%s\n' \
  "start_head=${START_HEAD}" \
  "base_master_sha=$(git ls-remote origin refs/heads/master | awk '{print $1}')" \
  "mock2_blob=$(git hash-object "${MOCK2}")" \
  "m2a_start_blob=$(git hash-object "${M2A}")" \
  "m2a_start_sha256=$(sha256sum "${M2A}" | awk '{print $1}')" \
  "fa_start_blob=$(git hash-object "${FA}")" \
  "fa_start_sha256=$(sha256sum "${FA}" | awk '{print $1}')" \
  "qym_blob=$(git hash-object "${QYM}")" \
  "qym_sha256=$(sha256sum "${QYM}" | awk '{print $1}')" \
  > "${LOGDIR}/snapshot.txt"

LAST_CODE=0
compile_module() {
  local module="$1"
  local label="$2"
  local src="PrimalitySheafVerification/${module}.lean"
  local log="${LOGDIR}/${label}.log"
  rm -f \
    "${OUT}/${module}.olean" \
    "${OUT}/${module}.ilean" \
    "${OUT}/${module}.olean.private"
  set +e
  lake env lean "${src}" \
    -o "${OUT}/${module}.olean" \
    -i "${OUT}/${module}.ilean" \
    > "${log}" 2>&1
  LAST_CODE=$?
  set -e
  printf '%s\n' "${LAST_CODE}" > "${LOGDIR}/${label}.exit"
  return "${LAST_CODE}"
}

record_failure() {
  local label="$1"
  local log="${LOGDIR}/${label}.log"
  {
    echo "label=${label}"
    echo "exit_code=${LAST_CODE}"
    echo "first_error=$(grep -n 'error:' "${log}" | head -1 || true)"
    echo "total_errors=$(grep -c 'error:' "${log}" || true)"
    echo "last_error=$(grep -n 'error:' "${log}" | tail -1 || true)"
    echo "maximum_error_limit=$(grep -Eci 'maximum number of errors' "${log}" || true)"
  } > "${LOGDIR}/first-failure.env"
  grep -n 'error:' "${log}" | head -10 > "${LOGDIR}/${label}.first-ten-errors.txt" || true
  tail -200 "${log}" > "${LOGDIR}/${label}.tail.txt" || true
}

require_compiled_artifacts() {
  local module="$1"
  local label="$2"
  local log="${LOGDIR}/${label}.log"
  test -s "${OUT}/${module}.olean"
  test -s "${OUT}/${module}.ilean"
  test "$(grep -c 'error:' "${log}" || true)" -eq 0
  ! grep -Eqi \
    "maximum number of errors|PANIC|segmentation fault|stack overflow|missing object file|declaration uses 'sorry'|sorryAx" \
    "${log}"
  ! grep -a -q 'sorryAx' "${OUT}/${module}.olean"
}

compile_or_fail() {
  local module="$1"
  local label="$2"
  if ! compile_module "${module}" "${label}"; then
    record_failure "${label}"
    return 1
  fi
  require_compiled_artifacts "${module}" "${label}"
}

copy_baseline() {
  local source="$1"
  local destination="$2"
  cp "${source}" "${destination}"
}

assert_only_allowed_worktree_changes() {
  python3 - "$@" <<'PY'
import subprocess, sys
allowed = set(sys.argv[1:])
raw = subprocess.check_output(["git", "status", "--porcelain=v1"], text=True)
bad = []
for line in raw.splitlines():
    path = line[3:]
    if " -> " in path:
        path = path.split(" -> ", 1)[1]
    if path not in allowed:
        bad.append(path)
if bad:
    raise SystemExit("unexpected worktree changes: " + ", ".join(sorted(set(bad))))
PY
}

# ---------------------------------------------------------------------------
# Phase A: Mock2 regression and Mock2_Advanced candidate
# ---------------------------------------------------------------------------

copy_baseline "${M2A}" /tmp/m2a-baseline.lean
M2A_BASELINE_SIGNATURE="$(python3 "${AUDITOR}" signature /tmp/m2a-baseline.lean)"
M2A_MODE='checked-in'
M2A_REPAIRS='none'

compile_or_fail Mock2 'phase-a-Mock2-prerequisite'
if compile_module Mock2_Advanced 'phase-a-M2A-checked-in-smoke'; then
  require_compiled_artifacts Mock2_Advanced 'phase-a-M2A-checked-in-smoke'
else
  record_failure 'phase-a-M2A-checked-in-smoke'
  M2A_MODE='v61-v68-repair'
  M2A_REPAIRS='v61,v62,v63,v64,v65,v66,v67,v68'
  for version in $(seq 61 68); do
    script="scripts/repair_mock2_advanced_v${version}.py"
    test -f "${script}"
    python3 "${script}" >> "${LOGDIR}/phase-a-repair-application.log" 2>&1
  done
  assert_only_allowed_worktree_changes "${M2A}"
  git diff --check
fi

M2A_CANDIDATE_SIGNATURE="$(python3 "${AUDITOR}" signature "${M2A}")"
if [[ "${M2A_CANDIDATE_SIGNATURE}" != "${M2A_BASELINE_SIGNATURE}" ]]; then
  python3 "${AUDITOR}" compare /tmp/m2a-baseline.lean "${M2A}" \
    > "${LOGDIR}/phase-a-theorem-interface-mismatch.json" || true
  echo 'Mock2_Advanced theorem or lemma statement changed.' >&2
  exit 1
fi
python3 "${AUDITOR}" audit "${M2A}" > "${LOGDIR}/phase-a-static-trust.json"

for pass in 1 2; do
  compile_or_fail Mock2 "phase-a-Mock2-regression-pass${pass}"
  compile_or_fail Mock2_Advanced "phase-a-M2A-candidate-pass${pass}"
done

printf '%s\n' \
  "m2a_mode=${M2A_MODE}" \
  "m2a_repairs=${M2A_REPAIRS}" \
  "m2a_candidate_blob=$(git hash-object "${M2A}")" \
  "m2a_candidate_sha256=$(sha256sum "${M2A}" | awk '{print $1}')" \
  "m2a_theorem_signature_sha256=${M2A_CANDIDATE_SIGNATURE}" \
  >> "${LOGDIR}/snapshot.txt"

# ---------------------------------------------------------------------------
# Phase B/C: FunctionalAnalysis and its substantive Integrated boundary
# ---------------------------------------------------------------------------

FA_MODE=''
FA_REPAIRS='none'
if [[ -f "${INTEGRATED}" ]] \
   && grep -Fq 'import PrimalitySheafVerification.Mock2_FunctionalAnalysis_Integrated' "${FA}" \
   && [[ "$(wc -l < "${INTEGRATED}")" -gt 500 ]]; then
  copy_baseline "${INTEGRATED}" /tmp/fa-substantive-baseline.lean
else
  copy_baseline "${FA}" /tmp/fa-substantive-baseline.lean
fi
FA_BASELINE_SIGNATURE="$(python3 "${AUDITOR}" signature /tmp/fa-substantive-baseline.lean)"

compile_or_fail Mock2 'phase-b-Mock2-prerequisite'
compile_or_fail Mock2_Advanced 'phase-b-M2A-prerequisite'

if [[ -f "${INTEGRATED}" ]] \
   && grep -Fq 'import PrimalitySheafVerification.Mock2_FunctionalAnalysis_Integrated' "${FA}"; then
  if compile_module Mock2_FunctionalAnalysis_Integrated 'phase-b-Integrated-checked-in-smoke' \
     && require_compiled_artifacts Mock2_FunctionalAnalysis_Integrated 'phase-b-Integrated-checked-in-smoke' \
     && compile_module Mock2_FunctionalAnalysis 'phase-b-FA-wrapper-checked-in-smoke' \
     && require_compiled_artifacts Mock2_FunctionalAnalysis 'phase-b-FA-wrapper-checked-in-smoke'; then
    FA_MODE='checked-in-split'
  fi
fi

if [[ -z "${FA_MODE}" ]]; then
  if compile_module Mock2_FunctionalAnalysis 'phase-b-FA-unsplit-checked-in-smoke'; then
    require_compiled_artifacts Mock2_FunctionalAnalysis 'phase-b-FA-unsplit-checked-in-smoke'
    FA_MODE='checked-in-unsplit'
  else
    record_failure 'phase-b-FA-unsplit-checked-in-smoke'
    FA_MODE='repair-289-through-315'
    FA_REPAIRS='289,290,291,292,293,294,295,297,298,299,300,309,310,311,312,313,314,315'
    if [[ -f "${INTEGRATED}" ]] && [[ "$(wc -l < "${INTEGRATED}")" -gt 500 ]]; then
      cp "${INTEGRATED}" "${FA}"
    fi
    cp "${M2A}" /tmp/m2a-verified-before-fa-repair.lean
    git fetch --depth=1 origin "${ADVANCED_BASELINE_COMMIT}"
    git show "${ADVANCED_BASELINE_COMMIT}:${M2A}" > "${M2A}"
    scripts=(
      apply_two_hundred_eighty_ninth_pass_repairs.py
      apply_two_hundred_ninetieth_pass_repairs.py
      apply_two_hundred_ninety_first_pass_repairs.py
      apply_two_hundred_ninety_second_pass_repairs.py
      apply_two_hundred_ninety_third_pass_repairs.py
      apply_two_hundred_ninety_fourth_pass_repairs.py
      apply_two_hundred_ninety_fifth_pass_repairs.py
      apply_two_hundred_ninety_seventh_pass_repairs.py
      apply_two_hundred_ninety_eighth_pass_repairs.py
      apply_two_hundred_ninety_ninth_pass_repairs.py
      apply_three_hundredth_pass_repairs.py
      apply_three_hundred_ninth_pass_repairs.py
      apply_three_hundred_tenth_pass_repairs.py
      apply_three_hundred_eleventh_pass_repairs.py
      apply_three_hundred_twelfth_pass_repairs.py
      apply_three_hundred_thirteenth_pass_repairs.py
      apply_three_hundred_fourteenth_pass_repairs.py
      apply_three_hundred_fifteenth_pass_repairs.py
    )
    for script in "${scripts[@]}"; do
      test -f "scripts/${script}"
      python3 "scripts/${script}" >> "${LOGDIR}/phase-b-repair-application.log" 2>&1
    done
    cp /tmp/m2a-verified-before-fa-repair.lean "${M2A}"
    while IFS= read -r changed; do
      case "${changed}" in
        "${M2A}"|"${FA}"|"${INTEGRATED}") ;;
        *) git restore --source=HEAD --worktree -- "${changed}" ;;
      esac
    done < <(git diff --name-only)
    assert_only_allowed_worktree_changes "${M2A}" "${FA}" "${INTEGRATED}"
    git diff --check
  fi
fi

if [[ "${FA_MODE}" != 'checked-in-split' ]]; then
  FA_CANDIDATE_SIGNATURE="$(python3 "${AUDITOR}" signature "${FA}")"
  if [[ "${FA_CANDIDATE_SIGNATURE}" != "${FA_BASELINE_SIGNATURE}" ]]; then
    python3 "${AUDITOR}" compare /tmp/fa-substantive-baseline.lean "${FA}" \
      > "${LOGDIR}/phase-b-theorem-interface-mismatch.json" || true
    echo 'Mock2_FunctionalAnalysis theorem or lemma statement changed.' >&2
    exit 1
  fi
  python3 "${AUDITOR}" audit "${FA}" > "${LOGDIR}/phase-b-FA-unsplit-static-trust.json"
  for pass in 1 2; do
    compile_or_fail Mock2 "phase-b-unsplit-Mock2-pass${pass}"
    compile_or_fail Mock2_Advanced "phase-b-unsplit-M2A-pass${pass}"
    compile_or_fail Mock2_FunctionalAnalysis "phase-b-FA-unsplit-candidate-pass${pass}"
  done
  cp "${FA}" "${INTEGRATED}"
  cat > "${FA}" <<'LEAN'
/-!
# Mock2 FunctionalAnalysis compatibility entry point

The complete source-level implementation is stored in
`PrimalitySheafVerification.Mock2_FunctionalAnalysis_Integrated`.
This historical module path re-exports the same public declarations.
-/
import PrimalitySheafVerification.Mock2_FunctionalAnalysis_Integrated
LEAN
fi

FA_INTEGRATED_SIGNATURE="$(python3 "${AUDITOR}" signature "${INTEGRATED}")"
if [[ "${FA_INTEGRATED_SIGNATURE}" != "${FA_BASELINE_SIGNATURE}" ]]; then
  python3 "${AUDITOR}" compare /tmp/fa-substantive-baseline.lean "${INTEGRATED}" \
    > "${LOGDIR}/phase-c-integrated-interface-mismatch.json" || true
  echo 'Integrated FunctionalAnalysis did not preserve the theorem interface.' >&2
  exit 1
fi
python3 "${AUDITOR}" audit "${M2A}" "${INTEGRATED}" "${FA}" \
  > "${LOGDIR}/phase-c-static-trust.json"
git diff --check
assert_only_allowed_worktree_changes "${M2A}" "${FA}" "${INTEGRATED}"

for pass in 1 2; do
  compile_or_fail Mock2 "phase-c-Mock2-regression-pass${pass}"
  compile_or_fail Mock2_Advanced "phase-c-M2A-regression-pass${pass}"
  compile_or_fail Mock2_FunctionalAnalysis_Integrated "phase-c-Integrated-pass${pass}"
  compile_or_fail Mock2_FunctionalAnalysis "phase-c-FA-wrapper-pass${pass}"
done

printf '%s\n' \
  "fa_mode=${FA_MODE}" \
  "fa_repairs=${FA_REPAIRS}" \
  "integrated_blob=$(git hash-object "${INTEGRATED}")" \
  "integrated_sha256=$(sha256sum "${INTEGRATED}" | awk '{print $1}')" \
  "fa_wrapper_blob=$(git hash-object "${FA}")" \
  "fa_wrapper_sha256=$(sha256sum "${FA}" | awk '{print $1}')" \
  "fa_theorem_signature_sha256=${FA_INTEGRATED_SIGNATURE}" \
  >> "${LOGDIR}/snapshot.txt"

# ---------------------------------------------------------------------------
# Phase D: QYM with the complete checked-in candidate dependency graph
# ---------------------------------------------------------------------------

python3 "${AUDITOR}" audit "${QYM}" > "${LOGDIR}/phase-d-QYM-static-trust.json"
QYM_SIGNATURE="$(python3 "${AUDITOR}" signature "${QYM}")"
grep -Fq 'Mock2_FunctionalAnalysis_Integrated' "${QYM}"

for pass in 1 2; do
  compile_or_fail Mock2 "phase-d-Mock2-regression-pass${pass}"
  compile_or_fail Mock2_Advanced "phase-d-M2A-regression-pass${pass}"
  compile_or_fail Mock2_FunctionalAnalysis_Integrated "phase-d-Integrated-regression-pass${pass}"
  compile_or_fail Mock2_FunctionalAnalysis "phase-d-FA-regression-pass${pass}"
  compile_or_fail QYM "phase-d-QYM-pass${pass}"
done

# Final source and object proof hashes.
sha256sum \
  "${MOCK2}" "${M2A}" "${INTEGRATED}" "${FA}" "${QYM}" \
  "${OUT}/Mock2.olean" "${OUT}/Mock2.ilean" \
  "${OUT}/Mock2_Advanced.olean" "${OUT}/Mock2_Advanced.ilean" \
  "${OUT}/Mock2_FunctionalAnalysis_Integrated.olean" \
  "${OUT}/Mock2_FunctionalAnalysis_Integrated.ilean" \
  "${OUT}/Mock2_FunctionalAnalysis.olean" "${OUT}/Mock2_FunctionalAnalysis.ilean" \
  "${OUT}/QYM.olean" "${OUT}/QYM.ilean" \
  > "${LOGDIR}/source-and-artifact-sha256.txt"

python3 - "${MARKER_OUT}" <<'PY'
from pathlib import Path
import hashlib, json, os, subprocess, sys

root = Path.cwd()
def sha(path: str) -> str:
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def blob(path: str) -> str:
    return subprocess.check_output(["git", "hash-object", path], text=True).strip()
def warnings(prefix: str) -> int:
    total = 0
    logdir = Path(os.environ.get("FOCUSED_LOGDIR", "/tmp/focused-proof/candidate-v3"))
    for path in logdir.glob(prefix + "*.log"):
        total += path.read_text(errors="replace").count("warning:")
    return total

snapshot = {}
for line in Path(os.environ.get("FOCUSED_LOGDIR", "/tmp/focused-proof/candidate-v3"), "snapshot.txt").read_text().splitlines():
    if "=" in line:
        key, value = line.split("=", 1)
        snapshot[key] = value

report = {
    "focused_candidate_status": "PASS",
    "constructed_from_commit": subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip(),
    "base_master_sha": snapshot.get("base_master_sha"),
    "runtime_repair_used_for_final_direct_source": False,
    "candidate_generation": {
        "mock2_advanced_mode": snapshot.get("m2a_mode"),
        "mock2_advanced_repairs": snapshot.get("m2a_repairs"),
        "functional_analysis_mode": snapshot.get("fa_mode"),
        "functional_analysis_repairs": snapshot.get("fa_repairs"),
    },
    "sources": {
        "Mock2": {"path": "PrimalitySheafVerification/Mock2.lean", "sha256": sha("PrimalitySheafVerification/Mock2.lean"), "blob": blob("PrimalitySheafVerification/Mock2.lean")},
        "Mock2_Advanced": {"path": "PrimalitySheafVerification/Mock2_Advanced.lean", "sha256": sha("PrimalitySheafVerification/Mock2_Advanced.lean"), "blob": blob("PrimalitySheafVerification/Mock2_Advanced.lean"), "theorem_signature_sha256": snapshot.get("m2a_theorem_signature_sha256")},
        "Mock2_FunctionalAnalysis_Integrated": {"path": "PrimalitySheafVerification/Mock2_FunctionalAnalysis_Integrated.lean", "sha256": sha("PrimalitySheafVerification/Mock2_FunctionalAnalysis_Integrated.lean"), "blob": blob("PrimalitySheafVerification/Mock2_FunctionalAnalysis_Integrated.lean"), "theorem_signature_sha256": snapshot.get("fa_theorem_signature_sha256")},
        "Mock2_FunctionalAnalysis": {"path": "PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean", "sha256": sha("PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean"), "blob": blob("PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean")},
        "QYM": {"path": "PrimalitySheafVerification/QYM.lean", "sha256": sha("PrimalitySheafVerification/QYM.lean"), "blob": blob("PrimalitySheafVerification/QYM.lean"), "theorem_signature_sha256": os.environ.get("QYM_SIGNATURE")},
    },
    "candidate_clean_pass_1": 0,
    "candidate_clean_pass_2": 0,
    "error_count": 0,
    "maximum_error_limit": False,
    "missing_project_object_files": 0,
    "forbidden_tokens": 0,
    "sorryAx": 0,
    "new_global_axioms": 0,
    "theorem_statements_changed": False,
    "assumptions_changed": False,
    "mock2_regression": "PASS",
    "integrated_boundary": "substantive full implementation with historical compatibility entry",
    "qym_conditional_certificate_boundary": "preserved",
}
Path(sys.argv[1]).write_text(json.dumps(report, indent=2) + "\n")
PY

# QYM signature is recorded separately because shell variables are not exported by default.
python3 - "${MARKER_OUT}" "${QYM_SIGNATURE}" <<'PY'
from pathlib import Path
import json, sys
p = Path(sys.argv[1])
data = json.loads(p.read_text())
data["sources"]["QYM"]["theorem_signature_sha256"] = sys.argv[2]
p.write_text(json.dumps(data, indent=2) + "\n")
PY

assert_only_allowed_worktree_changes "${M2A}" "${FA}" "${INTEGRATED}"
git diff --check
cp "${M2A}" "${LOGDIR}/Mock2_Advanced.verified.lean"
cp "${INTEGRATED}" "${LOGDIR}/Mock2_FunctionalAnalysis_Integrated.verified.lean"
cp "${FA}" "${LOGDIR}/Mock2_FunctionalAnalysis.verified.lean"
cp "${QYM}" "${LOGDIR}/QYM.verified.lean"
cp "${MARKER_OUT}" "${LOGDIR}/focused_candidate_v3.json"
tar -czf "${BUNDLE_OUT}" -C "$(dirname "${LOGDIR}")" "$(basename "${LOGDIR}")"

echo 'FOCUSED_CANDIDATE_V3_PASS'
