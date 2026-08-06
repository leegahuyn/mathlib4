#!/usr/bin/env python3
from pathlib import Path


def insert_before_retry(path: Path, retry_name: str, step: str) -> None:
    text = path.read_text(encoding='utf-8')
    if 'Publish compact focused failure summary' in text:
        return
    anchor = f'      - name: {retry_name}\n'
    if anchor not in text:
        raise SystemExit(f'retry anchor missing in {path}')
    text = text.replace(anchor, step.rstrip() + '\n\n' + anchor)
    path.write_text(text, encoding='utf-8')

candidate_step = r'''
      - name: Publish compact focused failure summary
        if: failure()
        shell: bash
        env:
          GH_TOKEN: ${{ github.token }}
        run: |
          set -euo pipefail
          python3 - <<'PY'
          from pathlib import Path
          import json, os
          logdir = Path('/tmp/focused-proof/candidate-v3')
          def read(name, limit=12000):
              p = logdir / name
              return p.read_text(errors='replace')[:limit] if p.exists() else None
          first_ten = {}
          for p in logdir.glob('*.first-ten-errors.txt'):
              first_ten[p.name] = p.read_text(errors='replace')[:12000]
          tails = {}
          for p in logdir.glob('*.tail.txt'):
              tails[p.name] = p.read_text(errors='replace')[-12000:]
          report = {
              'status': 'FAIL',
              'pipeline': 'focused-candidate-v3',
              'trigger_sha': os.environ.get('GITHUB_SHA'),
              'workflow_run': f"https://github.com/{os.environ.get('GITHUB_REPOSITORY')}/actions/runs/{os.environ.get('GITHUB_RUN_ID')}",
              'pipeline_exit_code': read('pipeline-exit-code.txt'),
              'snapshot': read('snapshot.txt'),
              'first_failure': read('first-failure.env'),
              'first_independent_errors': first_ten,
              'log_tails': tails,
          }
          Path('/tmp/focused_candidate_v3_failure.json').write_text(json.dumps(report, indent=2) + '\n')
          PY
          failure_repo=/tmp/focused-candidate-failure-repo
          rm -rf "${failure_repo}"
          git clone --branch "${BRANCH}" --single-branch \
            "https://x-access-token:${GH_TOKEN}@github.com/${GITHUB_REPOSITORY}.git" "${failure_repo}"
          cd "${failure_repo}"
          marker=.ci/focused/focused_candidate_v3_failure.json
          mkdir -p "$(dirname "${marker}")"
          cp /tmp/focused_candidate_v3_failure.json "${marker}"
          git config user.name 'github-actions[bot]'
          git config user.email '41898282+github-actions[bot]@users.noreply.github.com'
          git add "${marker}"
          if git diff --cached --quiet; then exit 0; fi
          git commit -m 'ci: record focused candidate v3 failure evidence'
          for attempt in 1 2 3; do
            if git push origin "HEAD:${BRANCH}"; then exit 0; fi
            git fetch origin "${BRANCH}"
            git rebase "origin/${BRANCH}" || exit 0
          done
          exit 0
'''

direct_step = r'''
      - name: Publish compact focused failure summary
        if: failure()
        shell: bash
        env:
          GH_TOKEN: ${{ github.token }}
        run: |
          set -euo pipefail
          python3 - <<'PY'
          from pathlib import Path
          import json, os
          logdir = Path('/tmp/focused-proof/direct-v3')
          def read(name, limit=12000):
              p = logdir / name
              return p.read_text(errors='replace')[:limit] if p.exists() else None
          first_ten = {}
          for p in logdir.glob('*.first-ten-errors.txt'):
              first_ten[p.name] = p.read_text(errors='replace')[:12000]
          tails = {}
          for p in logdir.glob('*.tail.txt'):
              tails[p.name] = p.read_text(errors='replace')[-12000:]
          report = {
              'status': 'FAIL',
              'pipeline': 'focused-direct-v3',
              'trigger_sha': os.environ.get('GITHUB_SHA'),
              'workflow_run': f"https://github.com/{os.environ.get('GITHUB_REPOSITORY')}/actions/runs/{os.environ.get('GITHUB_RUN_ID')}",
              'pipeline_exit_code': read('pipeline-exit-code.txt'),
              'first_failure': read('first-failure.env'),
              'axiom_audit_tail': read('axiom-audit.tail.txt'),
              'first_independent_errors': first_ten,
              'log_tails': tails,
          }
          Path('/tmp/focused_direct_v3_failure.json').write_text(json.dumps(report, indent=2) + '\n')
          PY
          failure_repo=/tmp/focused-direct-failure-repo
          rm -rf "${failure_repo}"
          git clone --branch "${BRANCH}" --single-branch \
            "https://x-access-token:${GH_TOKEN}@github.com/${GITHUB_REPOSITORY}.git" "${failure_repo}"
          cd "${failure_repo}"
          marker=.ci/focused/focused_direct_v3_failure.json
          mkdir -p "$(dirname "${marker}")"
          cp /tmp/focused_direct_v3_failure.json "${marker}"
          git config user.name 'github-actions[bot]'
          git config user.email '41898282+github-actions[bot]@users.noreply.github.com'
          git add "${marker}"
          if git diff --cached --quiet; then exit 0; fi
          git commit -m 'ci: record focused direct v3 failure evidence'
          for attempt in 1 2 3; do
            if git push origin "HEAD:${BRANCH}"; then exit 0; fi
            git fetch origin "${BRANCH}"
            git rebase "origin/${BRANCH}" || exit 0
          done
          exit 0
'''

insert_before_retry(
    Path('.github/workflows/focused-candidate-pipeline-v3-20260807.yml'),
    'Queue a bounded retry after a failed candidate run',
    candidate_step,
)
insert_before_retry(
    Path('.github/workflows/focused-direct-source-v3-20260807.yml'),
    'Queue a bounded retry after a failed direct-source run',
    direct_step,
)
