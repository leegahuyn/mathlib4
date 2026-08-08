from __future__ import annotations

import os

import declaration_repair_agent_v384 as agent

cycle = os.environ.get('CHAIN_CYCLE', '0')
agent.STYLES = [
    (
        'diverse-typeclass',
        'openai/gpt-5,openai/gpt-4.1,anthropic/claude-sonnet-4.5,xai/grok-code-fast-1,mistral-ai/codestral-2501,deepseek/DeepSeek-V3-0324,openai/gpt-4o',
        f'Persistent diverse-model chain cycle {cycle}. Resolve the exact first typeclass, coercion, or dependent-transport root. Do not repeat a rejected surface rewrite.',
    ),
    (
        'diverse-api',
        'anthropic/claude-sonnet-4.5,openai/gpt-4.1,openai/gpt-5,mistral-ai/codestral-2501,xai/grok-code-fast-1,openai/gpt-4o',
        f'Persistent diverse-model chain cycle {cycle}. Treat the declaration as a current-mathlib API migration; preserve its full header exactly and use explicit typed intermediate facts.',
    ),
    (
        'diverse-proof',
        'xai/grok-code-fast-1,openai/gpt-5,openai/gpt-4.1,anthropic/claude-sonnet-4.5,openai/gpt-4o',
        f'Persistent diverse-model chain cycle {cycle}. Produce a small kernel-checkable proof-body replacement with calc/change/ext/rw/simpa only, without broad unrelated edits.',
    ),
]

if __name__ == '__main__':
    raise SystemExit(agent.main())
