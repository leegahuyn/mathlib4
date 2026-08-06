#!/usr/bin/env bash
set -euo pipefail

ROOT="$(git rev-parse --show-toplevel)"
cd "${ROOT}"

LOGDIR="${FOCUSED_LOGDIR:-/tmp/focused-proof/direct-v3}"
CANDIDATE_MARKER="${FOCUSED_CANDIDATE_MARKER:-.ci/focused/focused_candidate_v3.json}"
REPORT_OUT="${FOCUSED_REPORT_OUT:-/tmp/focused_direct_pass_v3.json}"
BUNDLE_OUT="${FOCUSED_BUNDLE_OUT:-/tmp/focused-direct-v3-proof.tar.gz}"
OUT='.lake/build/lib/lean/PrimalitySheafVerification'
AUDITOR='scripts/focused_source_audit_20260807.py'
AXIOM_GENERATOR='scripts/generate_focused_axiom_audit_20260807.py'

MOCK2='PrimalitySheafVerification/Mock2.lean'
M2A='PrimalitySheafVerification/Mock2_Advanced.lean'
FA='PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean'
INTEGRATED='PrimalitySheafVerification/Mock2_FunctionalAnalysis_Integrated.lean'
QYM='PrimalitySheafVerification/QYM.lean'

mkdir -p "${LOGDIR}" "${OUT}"
test -f "${CANDIDATE_MARKER}"
INITIAL_STATUS="$(git status --porcelain=v1)"
if [[ -n "${INITIAL_STATUS}" ]]; then
  printf '%s\n' "${INITIAL_STATUS}" > "${LOGDIR}/dirty-start.txt"
  echo 'Direct-source verification requires a clean checked-in worktree.' >&2
  exit 1
fi

python3 - "${CANDIDATE_MARKER}" <<'PY' | tee "${LOGDIR}/candidate-marker-verification.txt"
from pathlib import Path
import hashlib, json, subprocess, sys

marker = json.loads(Path(sys.argv[1]).read_text())
if marker.get("focused_candidate_status") != "PASS":
    raise SystemExit("candidate marker is not PASS")
expected = marker["sources"]
for module, data in expected.items():
    path = Path(data["path"])
    actual_sha = hashlib.sha256(path.read_bytes()).hexdigest()
    actual_blob = subprocess.check_output(["git", "hash-object", str(path)], text=True).strip()
    print(module, actual_sha, actual_blob)
    if actual_sha != data["sha256"]:
        raise SystemExit(f"source SHA mismatch for {module}")
    if actual_blob != data["blob"]:
        raise SystemExit(f"source blob mismatch for {module}")
PY

python3 "${AUDITOR}" audit "${MOCK2}" "${M2A}" "${INTEGRATED}" "${FA}" "${QYM}" \
  > "${LOGDIR}/static-trust-audit.json"

python3 - "${CANDIDATE_MARKER}" <<'PY' | tee "${LOGDIR}/theorem-interface-verification.txt"
from pathlib import Path
import json, subprocess, sys

marker = json.loads(Path(sys.argv[1]).read_text())
checks = {
    "Mock2_Advanced": "PrimalitySheafVerification/Mock2_Advanced.lean",
    "Mock2_FunctionalAnalysis_Integrated": "PrimalitySheafVerification/Mock2_FunctionalAnalysis_Integrated.lean",
    "QYM": "PrimalitySheafVerification/QYM.lean",
}
for module, path in checks.items():
    expected = marker["sources"][module].get("theorem_signature_sha256")
    actual = subprocess.check_output(
        ["python3", "scripts/focused_source_audit_20260807.py", "signature", path],
        text=True,
    ).strip()
    print(module, actual)
    if actual != expected:
        raise SystemExit(f"theorem/lemma interface mismatch for {module}")
PY

grep -Fq 'import PrimalitySheafVerification.Mock2_FunctionalAnalysis_Integrated' "${FA}"
grep -Fq 'Mock2_FunctionalAnalysis_Integrated' "${QYM}"
test "$(wc -l < "${INTEGRATED}")" -gt 500

git diff --exit-code

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
  echo "${LAST_CODE}" > "${LOGDIR}/${label}.exit"
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

compile_or_fail() {
  local module="$1"
  local label="$2"
  local log="${LOGDIR}/${label}.log"
  if ! compile_module "${module}" "${label}"; then
    record_failure "${label}"
    return 1
  fi
  test -s "${OUT}/${module}.olean"
  test -s "${OUT}/${module}.ilean"
  test "$(grep -c 'error:' "${log}" || true)" -eq 0
  ! grep -Eqi \
    "maximum number of errors|PANIC|segmentation fault|stack overflow|missing object file|declaration uses 'sorry'|sorryAx" \
    "${log}"
  ! grep -a -q 'sorryAx' "${OUT}/${module}.olean"
}

modules=(
  Mock2
  Mock2_Advanced
  Mock2_FunctionalAnalysis_Integrated
  Mock2_FunctionalAnalysis
  QYM
)

for pass in 1 2; do
  for module in "${modules[@]}"; do
    compile_or_fail "${module}" "direct-${module}-pass${pass}"
  done
done

# Audit every public theorem/lemma declaration in the substantive focused modules.
python3 "${AXIOM_GENERATOR}" \
  --output /tmp/focused_axiom_audit_20260807.lean \
  "${M2A}" "${INTEGRATED}" "${QYM}" \
  > "${LOGDIR}/axiom-audit-generation.txt"
set +e
lake env lean /tmp/focused_axiom_audit_20260807.lean \
  > "${LOGDIR}/axiom-audit.log" 2>&1
AXIOM_CODE=$?
set -e
echo "${AXIOM_CODE}" > "${LOGDIR}/axiom-audit.exit"
if [[ "${AXIOM_CODE}" -ne 0 ]]; then
  tail -250 "${LOGDIR}/axiom-audit.log" > "${LOGDIR}/axiom-audit.tail.txt" || true
  exit "${AXIOM_CODE}"
fi

python3 - <<'PY' | tee "${LOGDIR}/axiom-audit-summary.json"
from pathlib import Path
import json, re

allowed = {"propext", "Classical.choice", "Quot.sound"}
text = Path("/tmp/focused-proof/direct-v3/axiom-audit.log").read_text(errors="replace")
text = re.sub(r"\x1b\[[0-9;]*m", "", text)
if "sorryAx" in text:
    raise SystemExit("sorryAx found in #print axioms output")
seen = set()
for match in re.finditer(r"depends on axioms:\s*\[(.*?)\]", text, re.S):
    for raw in match.group(1).split(","):
        name = raw.strip()
        if name:
            seen.add(name)
nonstandard = sorted(seen - allowed)
report = {
    "allowed_axioms": sorted(allowed),
    "observed_axioms": sorted(seen),
    "nonstandard_axioms": nonstandard,
    "sorryAx": 0,
}
print(json.dumps(report, indent=2))
if nonstandard:
    raise SystemExit("nonstandard axioms detected: " + ", ".join(nonstandard))
PY

sha256sum \
  "${MOCK2}" "${M2A}" "${INTEGRATED}" "${FA}" "${QYM}" \
  "${OUT}/Mock2.olean" "${OUT}/Mock2.ilean" \
  "${OUT}/Mock2_Advanced.olean" "${OUT}/Mock2_Advanced.ilean" \
  "${OUT}/Mock2_FunctionalAnalysis_Integrated.olean" \
  "${OUT}/Mock2_FunctionalAnalysis_Integrated.ilean" \
  "${OUT}/Mock2_FunctionalAnalysis.olean" "${OUT}/Mock2_FunctionalAnalysis.ilean" \
  "${OUT}/QYM.olean" "${OUT}/QYM.ilean" \
  > "${LOGDIR}/source-and-artifact-sha256.txt"

POST_STATUS="$(git status --porcelain=v1)"
if [[ -n "${POST_STATUS}" ]]; then
  printf '%s\n' "${POST_STATUS}" > "${LOGDIR}/dirty-end.txt"
  echo 'Direct verification mutated the checked-in source worktree.' >&2
  exit 1
fi

git diff --exit-code

python3 - "${REPORT_OUT}" "${CANDIDATE_MARKER}" <<'PY'
from pathlib import Path
import hashlib, json, os, re, subprocess, sys

report_path = Path(sys.argv[1])
candidate = json.loads(Path(sys.argv[2]).read_text())
logdir = Path(os.environ.get("FOCUSED_LOGDIR", "/tmp/focused-proof/direct-v3"))
outdir = Path('.lake/build/lib/lean/PrimalitySheafVerification')

def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

def warning_count(module: str) -> int:
    return sum(
        p.read_text(errors="replace").count("warning:")
        for p in logdir.glob(f"direct-{module}-pass*.log")
    )

axiom_summary = json.loads((logdir / "axiom-audit-summary.json").read_text())
modules = [
    "Mock2",
    "Mock2_Advanced",
    "Mock2_FunctionalAnalysis_Integrated",
    "Mock2_FunctionalAnalysis",
    "QYM",
]
sources = {}
artifacts = {}
for module in modules:
    path = Path(f"PrimalitySheafVerification/{module}.lean")
    sources[module] = {
        "path": str(path),
        "blob": subprocess.check_output(["git", "hash-object", str(path)], text=True).strip(),
        "sha256": sha(path),
        "warnings_across_two_passes": warning_count(module),
    }
    artifacts[module] = {
        "olean_sha256": sha(outdir / f"{module}.olean"),
        "ilean_sha256": sha(outdir / f"{module}.ilean"),
    }

run_url = None
if os.environ.get("GITHUB_RUN_ID") and os.environ.get("GITHUB_REPOSITORY"):
    run_url = f"https://github.com/{os.environ['GITHUB_REPOSITORY']}/actions/runs/{os.environ['GITHUB_RUN_ID']}"

report = {
    "overall_focused_status": "PASS",
    "final_branch": os.environ.get("FOCUSED_BRANCH", "fix/primality-sheaf-clean-build"),
    "verified_commit": subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip(),
    "base_master_sha": subprocess.check_output(["git", "ls-remote", "origin", "refs/heads/master"], text=True).split()[0],
    "workflow_run": run_url,
    "runtime_source_repair": False,
    "source_mutation_during_verification": False,
    "clean_pass_1": 0,
    "clean_pass_2": 0,
    "error_count": 0,
    "maximum_error_limit": False,
    "missing_project_object_files": 0,
    "forbidden_tokens": 0,
    "sorry": 0,
    "admit": 0,
    "sorryAx": 0,
    "unsafe": 0,
    "native_decide": 0,
    "Lean.ofReduceBool": 0,
    "observed_axioms": axiom_summary["observed_axioms"],
    "nonstandard_axioms": axiom_summary["nonstandard_axioms"],
    "theorem_statements_changed": False,
    "assumptions_changed": False,
    "mock2_regression": "PASS",
    "integrated_boundary": "substantive full source implementation",
    "qym_conditional_certificate_boundary": "preserved",
    "sources": sources,
    "artifacts": artifacts,
    "candidate_provenance": candidate,
}
report_path.write_text(json.dumps(report, indent=2) + "\n")
PY

cp "${REPORT_OUT}" "${LOGDIR}/focused_direct_pass_v3.json"
cp /tmp/focused_axiom_audit_20260807.lean "${LOGDIR}/focused_axiom_audit_20260807.lean"
tar -czf "${BUNDLE_OUT}" -C "$(dirname "${LOGDIR}")" "$(basename "${LOGDIR}")"

echo 'FOCUSED_DIRECT_V3_PASS'
