from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

MODULE_PATH = Path(__file__).with_name("pass376_multitarget_agent.py")
spec = importlib.util.spec_from_file_location("pass376_v2", MODULE_PATH)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load {MODULE_PATH}")
module = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = module
spec.loader.exec_module(module)


def reduction_aware_progress_key(self, width: int = 12):
    """Prefer later error positions; at an identical frontier prefer a smaller error log."""
    if self.passed:
        return (1,) + (10**9,) * (width * 2 + 1)
    flattened = [0]
    for line, col in self.positions[:width]:
        flattened.extend([line, col])
    while len(flattened) < 1 + width * 2:
        flattened.extend([10**9, 10**9])
    try:
        log_size = self.log_path.stat().st_size
    except OSError:
        log_size = 10**9
    flattened.append(-log_size)
    return tuple(flattened[: 2 + width * 2])


module.CompileResult.progress_key = reduction_aware_progress_key
module.PREFERRED_MODELS = [
    "openai/gpt-5",
    "openai/gpt-5-mini",
    "openai/gpt-4.1",
    "deepseek/DeepSeek-V3-0324",
    "meta/Llama-4-Scout-17B-16E-Instruct",
    "openai/gpt-4o",
    "microsoft/Phi-4",
]

if __name__ == "__main__":
    raise SystemExit(module.main())
