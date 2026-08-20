#!/usr/bin/env bash
set -euo pipefail

LOGDIR="${1:-/tmp/focused-proof/direct-v3}"
mkdir -p "${LOGDIR}"

methods=(getFileNameFor? getFileName? getFileNameFor getFileName getPosition?)
shapes=(option direct)
success=0

for method in "${methods[@]}"; do
  for shape in "${shapes[@]}"; do
    safe_method="${method//\?/_q}"
    audit_file="/tmp/focused-env-axiom-${safe_method}-${shape}.lean"
    if [[ "${shape}" == option ]]; then
      access=$(cat <<LEAN
    match env.${method} declName with
    | some sourceFile =>
      let sourceText := toString sourceFile
      if sourceText.endsWith "Mock2_Advanced.lean" ||
         sourceText.endsWith "Mock2_FunctionalAnalysis_Integrated.lean" ||
         sourceText.endsWith "QYM.lean" then
        checked := checked + 1
        for axiomName in (Lean.collectAxioms env declName).toList do
          observed := observed.insert axiomName
          unless allowed.contains axiomName do
            bad := bad.push (declName, axiomName)
    | none => pure ()
LEAN
)
    else
      access=$(cat <<LEAN
    let sourceText := toString (env.${method} declName)
    if sourceText.endsWith "Mock2_Advanced.lean" ||
       sourceText.endsWith "Mock2_FunctionalAnalysis_Integrated.lean" ||
       sourceText.endsWith "QYM.lean" then
      checked := checked + 1
      for axiomName in (Lean.collectAxioms env declName).toList do
        observed := observed.insert axiomName
        unless allowed.contains axiomName do
          bad := bad.push (declName, axiomName)
LEAN
)
    fi
    cat > "${audit_file}" <<LEAN
import PrimalitySheafVerification.QYM
import Lean.Util.CollectAxioms

open Lean Elab Command

elab "#focused_environment_axiom_audit" : command => do
  let env ← getEnv
  let allowed : NameSet :=
    (({} : NameSet).insert ``propext).insert ``Classical.choice |>.insert ``Quot.sound
  let mut observed : NameSet := {}
  let mut checked : Nat := 0
  let mut bad : Array (Name × Name) := #[]
  for (declName, _) in env.constants.toList do
${access}
  logInfo m!"focused_checked_declarations={checked}"
  logInfo m!"focused_observed_axioms={observed.toList}"
  if checked == 0 then
    throwError "no declarations were matched to the focused source files"
  if !bad.isEmpty then
    throwError m!"nonstandard focused axioms={bad}"

#focused_environment_axiom_audit
LEAN
    log="${LOGDIR}/environment-axiom-${safe_method}-${shape}.log"
    set +e
    lake env lean "${audit_file}" > "${log}" 2>&1
    code=$?
    set -e
    echo "${code}" > "${LOGDIR}/environment-axiom-${safe_method}-${shape}.exit"
    if [[ "${code}" -eq 0 ]]; then
      ! grep -Fq 'sorryAx' "${log}"
      ! grep -Fq 'nonstandard focused axioms=' "${log}"
      cp "${audit_file}" "${LOGDIR}/focused_environment_axiom_audit.lean"
      cp "${log}" "${LOGDIR}/environment-axiom-audit.log"
      printf '%s\n' \
        "method=${method}" \
        "shape=${shape}" \
        "exit_code=0" \
        > "${LOGDIR}/environment-axiom-audit.env"
      success=1
      break 2
    fi
  done
done

if [[ "${success}" -ne 1 ]]; then
  {
    echo 'No supported Lean source-file metadata accessor completed the comprehensive axiom audit.'
    for f in "${LOGDIR}"/environment-axiom-*.log; do
      [[ -f "${f}" ]] || continue
      echo "===== ${f} ====="
      tail -80 "${f}"
    done
  } > "${LOGDIR}/environment-axiom-audit-failure.txt"
  exit 1
fi
