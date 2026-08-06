#!/usr/bin/env python3
from pathlib import Path

path = Path('scripts/focused_fa_candidate_v5_20260807.sh')
text = path.read_text(encoding='utf-8')
old = r'''  scripts=(
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
  for script in "${scripts[@]}"; do test -f "scripts/$script"; python3 "scripts/$script" >> "$LOGDIR/repair-application.log" 2>&1; done
  cp /tmp/fa-v5-verified-m2a.lean "$M2A"
  while IFS= read -r changed; do
    case "$changed" in "$FA"|"$M2A"|"$INTEGRATED") ;; *) git restore --source=HEAD --worktree -- "$changed" ;; esac
  done < <(git diff --name-only)
  cmp -s "$M2A" /tmp/fa-v5-verified-m2a.lean
  CAND_SIG="$(python3 "$AUDITOR" signature "$FA")"
  if [[ "$CAND_SIG" != "$BASE_SIG" ]]; then python3 "$AUDITOR" compare /tmp/fa-v5-baseline.lean "$FA" > "$LOGDIR/theorem-interface-mismatch.json" || true; exit 1; fi
  python3 "$AUDITOR" audit "$FA" > "$LOGDIR/unsplit-static-trust.json"
  cp "$FA" "$INTEGRATED"
'''
new = r'''  scripts=(
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
  apply_fa_chain() {
    local log="$1"
    for script in "${scripts[@]}"; do
      test -f "scripts/$script" || return 1
      python3 "scripts/$script" >> "$log" 2>&1 || return 1
    done
  }
  restore_verified_m2a_and_unrelated() {
    cp /tmp/fa-v5-verified-m2a.lean "$M2A"
    while IFS= read -r changed; do
      case "$changed" in "$FA"|"$M2A"|"$INTEGRATED") ;; *) git restore --source=HEAD --worktree -- "$changed" ;; esac
    done < <(git diff --name-only)
    cmp -s "$M2A" /tmp/fa-v5-verified-m2a.lean
    git diff --check
  }
  select_historical_start() {
    local expected_blob='4eedc43d57f96b45897990bbeaada01ee0fd3b84'
    git fetch --no-tags --depth=1200 origin "$BRANCH" >/dev/null 2>&1 || true
    local commit blob
    while read -r commit; do
      blob="$(git rev-parse "$commit:$FA" 2>/dev/null || true)"
      if [[ "$blob" == "$expected_blob" ]]; then
        git show "$commit:$FA" > "$FA"
        printf '%s\n' "historical_start_commit=$commit" "historical_start_blob=$blob" >> "$LOGDIR/snapshot.txt"
        return 0
      fi
    done < <(git rev-list --all -- "$FA")
    return 1
  }

  repair_ok=1
  if ! apply_fa_chain "$LOGDIR/repair-application.log"; then repair_ok=0; fi
  restore_verified_m2a_and_unrelated
  if [[ "$repair_ok" -eq 1 ]]; then
    CAND_SIG="$(python3 "$AUDITOR" signature "$FA")"
    [[ "$CAND_SIG" == "$BASE_SIG" ]] || repair_ok=0
  fi
  if [[ "$repair_ok" -eq 1 ]]; then
    python3 "$AUDITOR" audit "$FA" > "$LOGDIR/unsplit-static-trust.json"
    if ! compile Mock2_FunctionalAnalysis 'FA-repaired-current-start-smoke'; then repair_ok=0; fi
  fi

  if [[ "$repair_ok" -eq 0 ]]; then
    cp /tmp/fa-v5-verified-m2a.lean "$M2A"
    if ! select_historical_start; then
      echo 'historical FunctionalAnalysis start blob was not found' > "$LOGDIR/historical-start-missing.txt"
      exit 1
    fi
    git show "$ADVANCED_BASELINE_COMMIT:$M2A" > "$M2A"
    if ! apply_fa_chain "$LOGDIR/historical-repair-application.log"; then
      echo 'historical FunctionalAnalysis repair chain failed' > "$LOGDIR/historical-repair-failed.txt"
      exit 1
    fi
    restore_verified_m2a_and_unrelated
    CAND_SIG="$(python3 "$AUDITOR" signature "$FA")"
    if [[ "$CAND_SIG" != "$BASE_SIG" ]]; then
      python3 "$AUDITOR" compare /tmp/fa-v5-baseline.lean "$FA" > "$LOGDIR/historical-theorem-interface-mismatch.json" || true
      exit 1
    fi
    python3 "$AUDITOR" audit "$FA" > "$LOGDIR/historical-unsplit-static-trust.json"
    if ! compile Mock2_FunctionalAnalysis 'FA-repaired-historical-start-smoke'; then
      exit "$LAST"
    fi
    MODE='historical-4eed-start-repair-289-through-315'
  fi
  cp "$FA" "$INTEGRATED"
'''
if old not in text:
    raise SystemExit('FA repair-selection block not found')
text = text.replace(old, new)
path.write_text(text, encoding='utf-8')
