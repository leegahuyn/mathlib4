#!/usr/bin/env python3
from __future__ import annotations

import importlib.util
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
HELPER = ROOT / "scripts" / "fa391_targeted_priority_agent_v2.py"

spec = importlib.util.spec_from_file_location("fa391", HELPER)
if spec is None or spec.loader is None:
    raise RuntimeError("cannot load PASS 391 helper")
fa391 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(fa391)


def error_window(log: str, limit: int = 65000) -> str:
    matches = list(fa391.ERROR_RE.finditer(log))
    if not matches:
        return log[-limit:]
    pieces: list[str] = []
    for index, match in enumerate(matches[:18]):
        start = max(0, match.start() - (9000 if index == 0 else 1800))
        end = min(len(log), match.start() + (22000 if index == 0 else 7000))
        pieces.append(log[start:end])
        if sum(len(piece) for piece in pieces) >= limit:
            break
    return "\n\n===== NEXT ERROR BLOCK =====\n\n".join(pieces)[:limit]


def improved_prompt(path: Path, metric: dict[str, object], log: str, text: str) -> str:
    first_line = int(metric["first_line"])
    ds, de, cs, ce = fa391.declaration_region(text, first_line)
    region = fa391.numbered_context(text, cs, ce)
    exact = fa391.api_search("\n".join(text.splitlines()[cs:ce]))
    return f"""
Repair the FIRST INDEPENDENT Lean error in `{path.relative_to(ROOT)}`.

Current metric:
{json.dumps(metric, indent=2)}

Compiler output centered on the actual first errors (warnings outside these windows were removed):
```text
{error_window(log)}
```

Exact source context with line numbers; the failing declaration is approximately lines {ds + 1}-{de}:
```lean
{region[:75000]}
```

Exact current-checkout API/name search:
```text
{exact[:35000]}
```

Return JSON only:
{{
  "edits": [{{"old": "exact unique source substring", "new": "replacement"}}],
  "reason": "brief technical reason"
}}

Requirements:
- Preserve every public theorem/lemma/corollary/def/abbrev name, binder, assumption, and conclusion exactly.
- Only repair proof bodies, local instances, letI/haveI declarations, explicit type/instance arguments, coercions, namespace qualification, or obsolete Mathlib APIs.
- The line-{first_line} cluster is an instance-coherence problem: terms are being elaborated with definitionally unequal SobolevCompletion NormedSpace/InnerProductSpace/CompleteSpace structures. Use one coherent local instance family and explicitly bind it where necessary.
- Copy each `old` substring byte-for-byte from the supplied source and keep it unique.
- No sorry, admit, axiom, unsafe, native_decide, Lean.ofReduceBool, theorem weakening, or speculative imports.
""".strip()


fa391.prompt_for = improved_prompt

if __name__ == "__main__":
    raise SystemExit(fa391.main())
