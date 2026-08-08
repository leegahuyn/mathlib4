from __future__ import annotations

import importlib.util
import subprocess
import sys
from pathlib import Path

MODULE_PATH = Path(__file__).with_name("pass376_aider_cycle.py")
spec = importlib.util.spec_from_file_location("pass376_aider_base", MODULE_PATH)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load {MODULE_PATH}")
module = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = module
spec.loader.exec_module(module)

_real_run = module.subprocess.run


def architect_run(command, *args, **kwargs):
    if isinstance(command, list) and command and command[0] == "aider":
        rewritten = list(command)
        if "--model" in rewritten:
            index = rewritten.index("--model")
            rewritten[index + 1] = "openai/openai/gpt-5"
        if "--edit-format" in rewritten:
            index = rewritten.index("--edit-format")
            del rewritten[index : index + 2]
        insertion = [
            "--architect",
            "--editor-model",
            "openai/openai/gpt-4.1",
            "--editor-edit-format",
            "diff",
        ]
        rewritten[1:1] = insertion
        command = rewritten
    return _real_run(command, *args, **kwargs)


module.subprocess.run = architect_run

if __name__ == "__main__":
    raise SystemExit(module.main())
