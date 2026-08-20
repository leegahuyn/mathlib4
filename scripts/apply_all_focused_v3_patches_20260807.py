#!/usr/bin/env python3
import runpy

for script in [
    'scripts/patch_focused_v3_start_guard_20260807.py',
    'scripts/patch_focused_v3_failure_artifacts_20260807.py',
    'scripts/patch_focused_v3_runtime_20260807.py',
    'scripts/patch_focused_preflight_policy_20260807.py',
]:
    runpy.run_path(script, run_name='__main__')
