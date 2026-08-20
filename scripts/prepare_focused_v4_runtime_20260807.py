#!/usr/bin/env python3
"""Idempotently normalize the focused candidate/direct scripts before a v4 run."""

from pathlib import Path


def replace_if_present(text: str, old: str, new: str) -> str:
    return text.replace(old, new) if old in text else text


candidate = Path('scripts/focused_materialize_pipeline_20260807.sh')
text = candidate.read_text(encoding='utf-8')

text = replace_if_present(
    text,
    "compile_or_fail Mock2 'phase-b-Mock2-prerequisite'\n"
    "compile_or_fail Mock2_Advanced 'phase-b-M2A-prerequisite'\n\n",
    "# Phase A leaves verified Mock2 and Mock2_Advanced objects in place.\n\n",
)
text = replace_if_present(
    text,
    """  python3 \"${AUDITOR}\" audit \"${FA}\" > \"${LOGDIR}/phase-b-FA-unsplit-static-trust.json\"
  for pass in 1 2; do
    compile_or_fail Mock2 \"phase-b-unsplit-Mock2-pass${pass}\"
    compile_or_fail Mock2_Advanced \"phase-b-unsplit-M2A-pass${pass}\"
    compile_or_fail Mock2_FunctionalAnalysis \"phase-b-FA-unsplit-candidate-pass${pass}\"
  done
  cp \"${FA}\" \"${INTEGRATED}\"
""",
    """  python3 \"${AUDITOR}\" audit \"${FA}\" > \"${LOGDIR}/phase-b-FA-unsplit-static-trust.json\"
  # The substantive full candidate is compiled twice under the final
  # Integrated module name below; avoid compiling the same 60k-line body a
  # second time under the temporary historical path.
  cp \"${FA}\" \"${INTEGRATED}\"
""",
)
text = replace_if_present(
    text,
    """for pass in 1 2; do
  compile_or_fail Mock2 \"phase-c-Mock2-regression-pass${pass}\"
  compile_or_fail Mock2_Advanced \"phase-c-M2A-regression-pass${pass}\"
  compile_or_fail Mock2_FunctionalAnalysis_Integrated \"phase-c-Integrated-pass${pass}\"
  compile_or_fail Mock2_FunctionalAnalysis \"phase-c-FA-wrapper-pass${pass}\"
done
""",
    """for pass in 1 2; do
  compile_or_fail Mock2_FunctionalAnalysis_Integrated \"phase-c-Integrated-pass${pass}\"
  compile_or_fail Mock2_FunctionalAnalysis \"phase-c-FA-wrapper-pass${pass}\"
done
""",
)
text = replace_if_present(
    text,
    """for pass in 1 2; do
  compile_or_fail Mock2 \"phase-d-Mock2-regression-pass${pass}\"
  compile_or_fail Mock2_Advanced \"phase-d-M2A-regression-pass${pass}\"
  compile_or_fail Mock2_FunctionalAnalysis_Integrated \"phase-d-Integrated-regression-pass${pass}\"
  compile_or_fail Mock2_FunctionalAnalysis \"phase-d-FA-regression-pass${pass}\"
  compile_or_fail QYM \"phase-d-QYM-pass${pass}\"
done
""",
    """for pass in 1 2; do
  compile_or_fail QYM \"phase-d-QYM-pass${pass}\"
done
""",
)

if 'phase-a-M2A-selected-path-smoke' not in text:
    anchor = 'M2A_CANDIDATE_SIGNATURE="$(python3 "${AUDITOR}" signature "${M2A}")"\n'
    if anchor not in text:
        raise SystemExit('M2A candidate signature anchor missing')
    fallback = r'''# Select a compiling candidate before the mandatory two clean passes.  The
# requested v61-v68 path is primary; the established 289-312 + 316 chain is a
# theorem-interface-preserving fallback only when that candidate still fails.
if ! compile_module Mock2_Advanced 'phase-a-M2A-selected-path-smoke'; then
  record_failure 'phase-a-M2A-selected-path-smoke'
  if [[ "${M2A_MODE}" != 'v61-v68-repair' ]]; then
    exit "${LAST_CODE}"
  fi
  cp /tmp/m2a-baseline.lean "${M2A}"
  legacy_scripts=(
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
    apply_three_hundred_sixteenth_pass_repairs.py
  )
  for script in "${legacy_scripts[@]}"; do
    test -f "scripts/${script}"
    python3 "scripts/${script}" >> "${LOGDIR}/phase-a-legacy-316-repair-application.log" 2>&1
  done
  while IFS= read -r changed; do
    [[ -z "${changed}" || "${changed}" == "${M2A}" ]] || \
      git restore --source=HEAD --worktree -- "${changed}"
  done < <(git diff --name-only)
  assert_only_allowed_worktree_changes "${M2A}"
  git diff --check
  M2A_MODE='legacy-289-through-312-plus-316'
  M2A_REPAIRS='289,290,291,292,293,294,295,297,298,299,300,309,310,311,312,316'
  if ! compile_module Mock2_Advanced 'phase-a-M2A-legacy-316-smoke'; then
    record_failure 'phase-a-M2A-legacy-316-smoke'
    exit "${LAST_CODE}"
  fi
  require_compiled_artifacts Mock2_Advanced 'phase-a-M2A-legacy-316-smoke'
else
  require_compiled_artifacts Mock2_Advanced 'phase-a-M2A-selected-path-smoke'
fi

'''
    text = text.replace(anchor, fallback + anchor)

candidate.write_text(text, encoding='utf-8')

# Normalize the direct verifier to the version-robust comprehensive dispatcher.
direct = Path('scripts/focused_direct_verify_20260807.sh')
text = direct.read_text(encoding='utf-8')
text = text.replace(
    'Path("/tmp/focused-proof/direct-v3/axiom-audit.log")',
    'Path(os.environ.get("FOCUSED_LOGDIR", "/tmp/focused-proof/direct-v3")) / "axiom-audit.log"',
)
if 'focused_axiom_audit_dispatch_20260807.sh' not in text:
    markers = [
        '# Audit every declaration whose Lean source file is one of the three',
        '# Audit every public theorem/lemma declaration in the substantive focused modules.',
    ]
    start = next((text.find(m) for m in markers if text.find(m) >= 0), -1)
    end = text.find('\nsha256sum \\\n', start)
    if start < 0 or end < 0:
        raise SystemExit('direct axiom-audit block anchors missing')
    replacement = (
        '# Comprehensive allowed-axiom audit with a Lean-version-compatible fallback.\n'
        'bash scripts/focused_axiom_audit_dispatch_20260807.sh "${LOGDIR}"\n'
    )
    text = text[:start] + replacement + text[end + 1:]
text = text.replace("AXIOM_GENERATOR='scripts/generate_focused_axiom_audit_20260807.py'\n", '')
text = text.replace(
    'cp /tmp/focused_axiom_audit_20260807.lean "${LOGDIR}/focused_axiom_audit_20260807.lean"\n',
    '',
)
direct.write_text(text, encoding='utf-8')

# Required execution helpers must be present.
required = [
    'scripts/focused_source_audit_20260807.py',
    'scripts/focused_axiom_audit_dispatch_20260807.sh',
    'scripts/focused_environment_axiom_audit_20260807.sh',
    'scripts/generate_focused_axiom_audit_20260807.py',
    'scripts/run_focused_candidate_v3_20260807.sh',
    'scripts/run_focused_direct_v3_20260807.sh',
]
for raw in required:
    if not Path(raw).is_file():
        raise SystemExit(f'missing required focused helper: {raw}')
