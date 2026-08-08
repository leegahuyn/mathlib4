from __future__ import annotations

import os

import declaration_repair_agent_v384 as agent

cycle = os.environ.get('CHAIN_CYCLE', '0')
agent.STYLES = [
    (
        slug,
        models,
        style
        + f' This is persistent chain cycle {cycle}; do not repeat a previously rejected surface rewrite. '
          'Use the exact compiler mismatch and surrounding definitions to choose a different kernel-checkable route.'
    )
    for slug, models, style in agent.STYLES
]

if __name__ == '__main__':
    raise SystemExit(agent.main())
