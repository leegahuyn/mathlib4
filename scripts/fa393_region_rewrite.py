#!/usr/bin/env python3
from __future__ import annotations

import concurrent.futures
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
OUT = ROOT / "build-logs" / "fa393-region-rewrite"
HELPER = ROOT / "scripts" / "fa391_targeted_priority_agent_v2.py"

spec = importlib.util.spec_from_file_location("fa391", HELPER)
if spec is None or spec.loader is None:
    raise RuntimeError("cannot load PASS 391 helper")
fa391 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(fa391)


def line_offsets(text: str) -> list[int]:
    offsets = [0]
    for match in re.finditer("\n", text):
        offsets.append(match.end())
    offsets.append(len(text))
    return offsets


def region(text: str, first_line: int) -> tuple[int, int, str]:
    ds, de, _, _ = fa391.declaration_region(text, first_line)
    lines = text.splitlines(keepends=True)
    # Include the local instance setup immediately before the failing declaration,
    # but stop before unrelated later public declarations.
    start_line = max(0, ds - 140)
    end_line = min(len(lines), de + 55)
    offsets = line_offsets(text)
    start = offsets[start_line]
    end = offsets[end_line] if end_line < len(offsets) else len(text)
    return start, end, "".join(lines[start_line:end_line])


def prompt(path: Path, metric: dict[str, object], compiler: str, excerpt: str) -> str:
    return f"""
Repair the first independent Lean error in `{path.relative_to(ROOT)}` by rewriting the supplied
contiguous local region. The current first error is line {metric['first_line']}.

Compiler output:
```text
{compiler[:55000]}
```

Exact source region to replace:
```lean
{excerpt[:85000]}
```

Return JSON only:
{{"replacement": "the complete replacement text for that exact region", "reason": "brief reason"}}

Hard constraints:
- Preserve every public theorem/lemma/corollary/def/abbrev header, binder, assumption, and conclusion byte-for-byte in meaning and spelling.
- Do not delete any mathematical declaration.
- You may repair proof bodies, local/noncomputable instances, letI/haveI declarations, explicit instance arguments, namespace qualification, coercions, and current Mathlib API calls.
- The line-{metric['first_line']} cluster is known to involve definitionally unequal SobolevCompletion NormedSpace/InnerProductSpace/CompleteSpace structures; establish one coherent local instance family rather than rewriting the theorem statement.
- No sorry, admit, axiom, unsafe, native_decide, or Lean.ofReduceBool.
- Do not add speculative imports.
- The replacement must be self-contained and must replace the entire supplied region, including unchanged lines.
""".strip()


def main() -> int:
    OUT.mkdir(parents=True, exist_ok=True)
    original_headers = fa391.public_headers(TARGET.read_text(encoding="utf-8"))
    history: list[dict[str, object]] = []
    metric = fa391.compile_file(TARGET, "fa393-baseline", max_errors=30)
    for round_index in range(1, 5):
        if int(metric["exit_code"]) == 0:
            break
        text = TARGET.read_text(encoding="utf-8")
        start, end, excerpt = region(text, int(metric["first_line"]))
        compiler = (ROOT / str(metric["log"])).read_text(encoding="utf-8", errors="replace")
        ask = prompt(TARGET, metric, compiler, excerpt)
        models = fa391.MODELS[:6]
        with concurrent.futures.ThreadPoolExecutor(max_workers=len(models)) as pool:
            responses = list(pool.map(lambda model: fa391.call_model(model, ask), models))
        best_text = None
        best_metric = metric
        response_dir = OUT / "responses" / f"round-{round_index:02d}"
        response_dir.mkdir(parents=True, exist_ok=True)
        for candidate_index, (model, raw) in enumerate(responses, 1):
            (response_dir / f"{candidate_index:02d}-{model.replace('/', '_')}.txt").write_text(
                raw, encoding="utf-8", errors="replace"
            )
            payload = fa391.extract_json(raw)
            if payload is None or not isinstance(payload.get("replacement"), str):
                continue
            replacement = str(payload["replacement"])
            candidate = text[:start] + replacement + text[end:]
            if candidate == text:
                continue
            if fa391.public_headers(candidate) != original_headers:
                continue
            if any(fa391.audit_text(candidate).values()):
                continue
            TARGET.write_text(candidate, encoding="utf-8")
            candidate_metric = fa391.compile_file(
                TARGET, f"fa393-r{round_index:02d}-c{candidate_index:02d}", max_errors=30
            )
            TARGET.write_text(text, encoding="utf-8")
            if fa391.better(candidate_metric, best_metric):
                best_text = candidate
                best_metric = candidate_metric
        accepted = best_text is not None
        if accepted:
            TARGET.write_text(best_text, encoding="utf-8")
            metric = fa391.compile_file(TARGET, f"fa393-accepted-{round_index:02d}", max_errors=60)
        history.append({
            "round": round_index,
            "accepted": accepted,
            "metric": metric,
            "source_sha256": fa391.sha(TARGET),
        })
        (OUT / "state.json").write_text(json.dumps(history, indent=2), encoding="utf-8")
        if not accepted:
            break
    print(json.dumps({"history": history, "final": metric}, indent=2))
    # Continue through FA 2x, Integrated/Mock3 2x, and QYM 2x in the required order.
    proc = subprocess.run(
        [sys.executable, str(HELPER), "--rounds", "10", "--models-per-round", "6"],
        cwd=ROOT,
        text=True,
    )
    return proc.returncode


if __name__ == "__main__":
    raise SystemExit(main())
