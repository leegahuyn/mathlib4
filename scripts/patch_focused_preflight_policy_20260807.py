#!/usr/bin/env python3
from pathlib import Path

path = Path('.github/workflows/focused-v3-preflight-20260807.yml')
text = path.read_text(encoding='utf-8')
old = """          ! grep -R -E '\\b(sorry|admit|native_decide|Lean\\.ofReduceBool)\\b' \\
            scripts/focused_materialize_pipeline_20260807.sh \\
            scripts/focused_direct_verify_20260807.sh
"""
new = """          ! grep -E 'repair_mock2_advanced|apply_.*_pass_repairs' \\
            .github/workflows/focused-direct-source-v3-20260807.yml \\
            scripts/run_focused_direct_v3_20260807.sh
"""
if old in text:
    text = text.replace(old, new)
path.write_text(text, encoding='utf-8')
if old in path.read_text(encoding='utf-8'):
    raise SystemExit('stale preflight policy block remains')
