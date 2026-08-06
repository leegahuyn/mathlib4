#!/usr/bin/env python3
from pathlib import Path

candidate = Path('.github/workflows/focused-candidate-pipeline-v3-20260807.yml')
text = candidate.read_text(encoding='utf-8')
retry_path = "      - '.ci/focused/focused_candidate_v3_retry.txt'\n"
anchor = "      - 'scripts/apply_*_pass_repairs.py'\n"
if retry_path not in text:
    if anchor not in text:
        raise SystemExit('candidate path anchor missing')
    text = text.replace(anchor, anchor + retry_path)
retry_step = r'''
      - name: Queue a bounded retry after a failed candidate run
        if: failure()
        shell: bash
        env:
          GH_TOKEN: ${{ github.token }}
        run: |
          set -euo pipefail
          retry_repo=/tmp/focused-candidate-retry
          rm -rf "${retry_repo}"
          git clone --branch "${BRANCH}" --single-branch \
            "https://x-access-token:${GH_TOKEN}@github.com/${GITHUB_REPOSITORY}.git" "${retry_repo}"
          cd "${retry_repo}"
          counter_file=.ci/focused/focused_candidate_v3_retry.txt
          mkdir -p "$(dirname "${counter_file}")"
          count=0
          [[ -f "${counter_file}" ]] && count="$(cat "${counter_file}")"
          if [[ ! "${count}" =~ ^[0-9]+$ ]]; then count=0; fi
          if [[ "${count}" -ge 3 ]]; then
            echo 'Candidate retry limit reached; preserving the failure for diagnosis.'
            exit 0
          fi
          count=$((count + 1))
          printf '%s\n' "${count}" > "${counter_file}"
          git config user.name 'github-actions[bot]'
          git config user.email '41898282+github-actions[bot]@users.noreply.github.com'
          git add "${counter_file}"
          git commit -m "ci: retry focused candidate v3 (${count}/3)"
          for attempt in 1 2 3 4; do
            if git push origin "HEAD:${BRANCH}"; then exit 0; fi
            git fetch origin "${BRANCH}"
            git rebase "origin/${BRANCH}" || exit 0
            sleep $((attempt * 2))
          done
          exit 0
'''
if 'Queue a bounded retry after a failed candidate run' not in text:
    text = text.rstrip() + '\n' + retry_step.lstrip('\n')
candidate.write_text(text, encoding='utf-8')

direct = Path('.github/workflows/focused-direct-source-v3-20260807.yml')
text = direct.read_text(encoding='utf-8')
retry_path = "      - '.ci/focused/focused_direct_v3_retry.txt'\n"
anchor = "      - '.ci/focused/focused_candidate_v3.json'\n"
if retry_path not in text:
    if anchor not in text:
        raise SystemExit('direct path anchor missing')
    text = text.replace(anchor, anchor + retry_path)
retry_step = r'''
      - name: Queue a bounded retry after a failed direct-source run
        if: failure()
        shell: bash
        env:
          GH_TOKEN: ${{ github.token }}
        run: |
          set -euo pipefail
          retry_repo=/tmp/focused-direct-retry
          rm -rf "${retry_repo}"
          git clone --branch "${BRANCH}" --single-branch \
            "https://x-access-token:${GH_TOKEN}@github.com/${GITHUB_REPOSITORY}.git" "${retry_repo}"
          cd "${retry_repo}"
          counter_file=.ci/focused/focused_direct_v3_retry.txt
          mkdir -p "$(dirname "${counter_file}")"
          count=0
          [[ -f "${counter_file}" ]] && count="$(cat "${counter_file}")"
          if [[ ! "${count}" =~ ^[0-9]+$ ]]; then count=0; fi
          if [[ "${count}" -ge 2 ]]; then
            echo 'Direct-source retry limit reached; preserving the failure for diagnosis.'
            exit 0
          fi
          count=$((count + 1))
          printf '%s\n' "${count}" > "${counter_file}"
          git config user.name 'github-actions[bot]'
          git config user.email '41898282+github-actions[bot]@users.noreply.github.com'
          git add "${counter_file}"
          git commit -m "ci: retry focused direct-source v3 (${count}/2)"
          for attempt in 1 2 3 4; do
            if git push origin "HEAD:${BRANCH}"; then exit 0; fi
            git fetch origin "${BRANCH}"
            git rebase "origin/${BRANCH}" || exit 0
            sleep $((attempt * 2))
          done
          exit 0
'''
if 'Queue a bounded retry after a failed direct-source run' not in text:
    text = text.rstrip() + '\n' + retry_step.lstrip('\n')
direct.write_text(text, encoding='utf-8')
