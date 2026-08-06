#!/usr/bin/env python3
from pathlib import Path

path = Path('scripts/focused_m2a_candidate_v5_20260807.sh')
text = path.read_text(encoding='utf-8')
old = r'''  primary_ok=1
  for version in $(seq 61 68); do
    script="scripts/repair_mock2_advanced_v${version}.py"
    if [[ ! -f "$script" ]] || ! python3 "$script" >> "$LOGDIR/v61-v68-application.log" 2>&1; then
      primary_ok=0; break
    fi
  done
  if [[ "$primary_ok" -eq 1 ]]; then
    restore_unrelated
    if compile_module Mock2_Advanced 'm2a-v61-v68-smoke'; then
      require_success Mock2_Advanced 'm2a-v61-v68-smoke'
    else
      failure_report 'm2a-v61-v68-smoke'; primary_ok=0
    fi
  fi
  if [[ "$primary_ok" -eq 0 ]]; then
    cp /tmp/m2a-v5-baseline.lean "$TARGET"
    MODE='legacy-289-through-312-plus-316'
    REPAIRS='289,290,291,292,293,294,295,297,298,299,300,309,310,311,312,316'
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
      apply_three_hundred_sixteenth_pass_repairs.py
    )
    for script in "${scripts[@]}"; do
      test -f "scripts/$script"
      python3 "scripts/$script" >> "$LOGDIR/legacy-316-application.log" 2>&1
    done
    restore_unrelated
    if ! compile_module Mock2_Advanced 'm2a-legacy-316-smoke'; then
      failure_report 'm2a-legacy-316-smoke'; exit "$LAST_CODE"
    fi
    require_success Mock2_Advanced 'm2a-legacy-316-smoke'
  fi
'''
new = r'''  primary_ok=1
  primary_applied=1
  for version in $(seq 61 68); do
    script="scripts/repair_mock2_advanced_v${version}.py"
    if [[ ! -f "$script" ]] || ! python3 "$script" >> "$LOGDIR/v61-v68-application.log" 2>&1; then
      primary_ok=0; primary_applied=0; break
    fi
  done
  if [[ "$primary_ok" -eq 1 ]]; then
    restore_unrelated
    if compile_module Mock2_Advanced 'm2a-v61-v68-smoke'; then
      require_success Mock2_Advanced 'm2a-v61-v68-smoke'
    else
      failure_report 'm2a-v61-v68-smoke'; primary_ok=0
    fi
  fi

  # The pass-316 universe repair was independently established after the
  # v61-v68 line.  Test their composition before falling back to the older
  # full repair chain.
  if [[ "$primary_ok" -eq 0 && "$primary_applied" -eq 1 && -f scripts/apply_three_hundred_sixteenth_pass_repairs.py ]]; then
    if python3 scripts/apply_three_hundred_sixteenth_pass_repairs.py >> "$LOGDIR/v61-v68-plus-316-application.log" 2>&1; then
      restore_unrelated
      if compile_module Mock2_Advanced 'm2a-v61-v68-plus-316-smoke'; then
        require_success Mock2_Advanced 'm2a-v61-v68-plus-316-smoke'
        primary_ok=1
        MODE='v61-v68-plus-316'
        REPAIRS='v61,v62,v63,v64,v65,v66,v67,v68,316'
      else
        failure_report 'm2a-v61-v68-plus-316-smoke'
      fi
    fi
  fi

  if [[ "$primary_ok" -eq 0 ]]; then
    cp /tmp/m2a-v5-baseline.lean "$TARGET"
    MODE='legacy-289-through-312-plus-316'
    REPAIRS='289,290,291,292,293,294,295,297,298,299,300,309,310,311,312,316'
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
      apply_three_hundred_sixteenth_pass_repairs.py
    )
    apply_legacy() {
      for script in "${scripts[@]}"; do
        test -f "scripts/$script"
        python3 "scripts/$script" >> "$LOGDIR/legacy-316-application.log" 2>&1
      done
      restore_unrelated
    }
    apply_legacy
    legacy_ok=0
    if compile_module Mock2_Advanced 'm2a-legacy-316-smoke'; then
      require_success Mock2_Advanced 'm2a-legacy-316-smoke'
      legacy_ok=1
    else
      failure_report 'm2a-legacy-316-smoke'
    fi

    # Some repositories contain v68 as the final ledger-universe repair on top
    # of the legacy candidate.  It is applied only if the plain legacy source
    # still fails and only accepted after full compilation.
    if [[ "$legacy_ok" -eq 0 && -f scripts/repair_mock2_advanced_v68.py ]]; then
      if python3 scripts/repair_mock2_advanced_v68.py >> "$LOGDIR/legacy-316-plus-v68-application.log" 2>&1; then
        restore_unrelated
        if compile_module Mock2_Advanced 'm2a-legacy-316-plus-v68-smoke'; then
          require_success Mock2_Advanced 'm2a-legacy-316-plus-v68-smoke'
          legacy_ok=1
          MODE='legacy-289-through-312-plus-316-plus-v68'
          REPAIRS='289,290,291,292,293,294,295,297,298,299,300,309,310,311,312,316,v68'
        else
          failure_report 'm2a-legacy-316-plus-v68-smoke'
        fi
      fi
    fi

    # Last bounded variant: replay the complete v61-v68 line on the legacy
    # candidate.  Script-anchor failure rejects this variant; it never weakens
    # the source or bypasses Lean.
    if [[ "$legacy_ok" -eq 0 ]]; then
      cp /tmp/m2a-v5-baseline.lean "$TARGET"
      apply_legacy
      composite_applied=1
      for version in $(seq 61 68); do
        script="scripts/repair_mock2_advanced_v${version}.py"
        if [[ ! -f "$script" ]] || ! python3 "$script" >> "$LOGDIR/legacy-plus-v61-v68-application.log" 2>&1; then
          composite_applied=0; break
        fi
      done
      if [[ "$composite_applied" -eq 1 ]]; then
        restore_unrelated
        if compile_module Mock2_Advanced 'm2a-legacy-plus-v61-v68-smoke'; then
          require_success Mock2_Advanced 'm2a-legacy-plus-v61-v68-smoke'
          legacy_ok=1
          MODE='legacy-plus-v61-v68'
          REPAIRS='289,290,291,292,293,294,295,297,298,299,300,309,310,311,312,316,v61,v62,v63,v64,v65,v66,v67,v68'
        else
          failure_report 'm2a-legacy-plus-v61-v68-smoke'
        fi
      fi
    fi
    if [[ "$legacy_ok" -ne 1 ]]; then
      exit "$LAST_CODE"
    fi
  fi
'''
if old not in text:
    raise SystemExit('M2A v5 repair-selection block not found')
text = text.replace(old, new)
path.write_text(text, encoding='utf-8')
