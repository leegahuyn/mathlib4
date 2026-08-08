from __future__ import annotations

import os

import lean_repair_loop_v377 as core

_original_prompt_for = core.prompt_for


def styled_prompt_for(*args, **kwargs):
    base = _original_prompt_for(*args, **kwargs)
    style = os.environ.get('REPAIR_STYLE', '').strip()
    if not style:
        return base
    return base + f"\nAdditional repair strategy for this beam candidate:\n{style}\n"


core.prompt_for = styled_prompt_for

if __name__ == '__main__':
    raise SystemExit(core.main())
