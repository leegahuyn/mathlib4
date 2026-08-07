from __future__ import annotations

from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
WORKFLOWS = ROOT / ".github" / "workflows"
OFFICIAL = WORKFLOWS / "primality-sheaf-ci.yml"
DRIVER = ROOT / "scripts" / "primality_official_ci_driver.sh"
MARKER = ROOT / "build-logs" / "final-local-gate-pass.json"

WORKFLOW = r'''name: PrimalitySheafVerification official clean CI

on:
  push:
    branches: [fix/primality-sheaf-clean-build]
    paths:
      - 'PrimalitySheafVerification/**'
      - 'scripts/primality_official_ci_driver.sh'
      - 'scripts/primality_final_local_gate.sh'
      - 'scripts/primality_final_local_gate_v2.sh'
      - 'scripts/generate_spt5_whole_file_audit.py'
      - '.github/workflows/primality-sheaf-ci.yml'
  pull_request:
    branches: [master]
    paths:
      - 'PrimalitySheafVerification/**'
      - 'scripts/primality_official_ci_driver.sh'
      - 'scripts/primality_final_local_gate.sh'
      - 'scripts/primality_final_local_gate_v2.sh'
      - 'scripts/generate_spt5_whole_file_audit.py'
      - '.github/workflows/primality-sheaf-ci.yml'
  workflow_dispatch:

permissions:
  contents: read

concurrency:
  group: primality-sheaf-official-${{ github.event.pull_request.head.sha || github.sha }}
  cancel-in-progress: true

jobs:
  clean-build-and-audit:
    runs-on: ubuntu-24.04
    timeout-minutes: 360
    env:
      SOURCE_SHA: ${{ github.event.pull_request.head.sha || github.sha }}
      FINAL_EVIDENCE_DIR: /tmp/primality-sheaf-official

    steps:
      - name: Checkout the exact tested commit
        uses: actions/checkout@11d5960a326750d5838078e36cf38b85af677262
        with:
          ref: ${{ env.SOURCE_SHA }}
          fetch-depth: 1
          persist-credentials: false

      - name: Install the pinned Lean toolchain and restore Mathlib cache
        shell: bash
        run: |
          set -euo pipefail
          curl --retry 5 --retry-all-errors --fail --silent --show-error \
            https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
            -o /tmp/elan-init.sh
          sh /tmp/elan-init.sh -y --default-toolchain none
          export PATH="${HOME}/.elan/bin:${PATH}"
          elan toolchain install "$(cat lean-toolchain)"
          lean --version
          lake --version
          lake exe cache get

      - name: Compile all modules twice and run the Spt5 whole-file axiom audit
        shell: bash
        run: |
          set -euo pipefail
          export PATH="${HOME}/.elan/bin:${PATH}"
          bash scripts/primality_official_ci_driver.sh

      - name: Upload official clean-build evidence
        if: always()
        uses: actions/upload-artifact@ea165f8d65b6e75b540449e92b4886f43607fa02
        with:
          name: primality-sheaf-official-${{ env.SOURCE_SHA }}
          path: /tmp/primality-sheaf-official
          if-no-files-found: error
          retention-days: 30
'''

DRIVER_TEXT = r'''#!/usr/bin/env bash
set -euo pipefail

# This final workflow never rewrites a Lean source file.  It compiles the
# checked-in sources from deleted project artifacts twice and audits Spt5.
git diff --exit-code -- PrimalitySheafVerification
bash -n scripts/primality_final_local_gate.sh
bash -n scripts/primality_final_local_gate_v2.sh
python3 -m py_compile scripts/generate_spt5_whole_file_audit.py
bash scripts/primality_final_local_gate_v2.sh
git diff --exit-code -- PrimalitySheafVerification
'''

# Only project-specific temporary workflows are removed.  Upstream Mathlib
# workflows with unrelated names remain untouched.
TEMP_PATTERN = re.compile(
    r"(?:"
    r"primality|mock2|functional|qym|fa31|fa32|fa33|"
    r"priority-|focused-finalize|adaptive-|materialize-|"
    r"fixed-candidate|direct-all-modules|install-scoped|"
    r"install-simplified|completion-supervisor|completion-orchestrator|"
    r"agent-2026"
    r")",
    re.IGNORECASE,
)


def main() -> int:
    if not MARKER.is_file():
        raise RuntimeError("final local PASS marker is required before official CI installation")
    WORKFLOWS.mkdir(parents=True, exist_ok=True)
    removed: list[str] = []
    for path in WORKFLOWS.iterdir():
        if not path.is_file() or path == OFFICIAL:
            continue
        if TEMP_PATTERN.search(path.name):
            removed.append(path.name)
            path.unlink()
    # Explicit duplicate from the original plan, even if its name changes case.
    duplicate = WORKFLOWS / "primality-sheaf-verification.yml"
    if duplicate.exists() and duplicate != OFFICIAL:
        removed.append(duplicate.name)
        duplicate.unlink()
    OFFICIAL.write_text(WORKFLOW, encoding="utf-8")
    DRIVER.write_text(DRIVER_TEXT, encoding="utf-8")
    DRIVER.chmod(0o755)
    manifest = ROOT / "build-logs" / "official-ci-installation.txt"
    manifest.parent.mkdir(parents=True, exist_ok=True)
    manifest.write_text(
        "official_workflow=.github/workflows/primality-sheaf-ci.yml\n"
        "runtime_lean_repair=0\n"
        "hardcoded_checkout_branch=0\n"
        "removed_temporary_workflows=" + ",".join(sorted(set(removed))) + "\n",
        encoding="utf-8",
    )
    print(f"removed temporary project workflows: {len(set(removed))}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
