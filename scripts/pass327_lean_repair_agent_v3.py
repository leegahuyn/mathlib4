from __future__ import annotations

import os
from pathlib import Path
import subprocess
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import pass327_lean_repair_agent_v2 as patched

base = patched.base
_rest_call_model = base.call_model
_cli_ready = False


def _run(command: list[str], *, input_text: str | None = None, timeout: int = 360) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        command,
        cwd=base.ROOT,
        text=True,
        input=input_text,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=timeout,
        env=os.environ.copy(),
    )


def _ensure_cli() -> None:
    global _cli_ready
    if _cli_ready:
        return
    probe = _run(["gh", "models", "--help"], timeout=60)
    if probe.returncode != 0:
        install = _run(["gh", "extension", "install", "github/gh-models"], timeout=180)
        if install.returncode != 0 and "already installed" not in install.stdout.lower():
            raise RuntimeError("unable to install github/gh-models:\n" + install.stdout)
    probe = _run(["gh", "models", "--help"], timeout=60)
    if probe.returncode != 0:
        raise RuntimeError("gh models is unavailable after extension installation:\n" + probe.stdout)
    _cli_ready = True


def call_model_v3(prompt: str, call_index: int) -> tuple[str, str]:
    try:
        return _rest_call_model(prompt, call_index)
    except Exception as rest_error:
        _ensure_cli()
        errors = [f"REST backends failed: {type(rest_error).__name__}: {rest_error}"]
        models = ["openai/gpt-4.1", "openai/gpt-4o", "openai/gpt-4.1-mini"]
        for model in models:
            # The extension accepts the prompt on stdin in non-interactive mode.
            attempts = [
                ["gh", "models", "run", model],
                ["gh", "models", "run", model, "--prompt", prompt[:100000]],
            ]
            for command in attempts:
                try:
                    result = _run(
                        command,
                        input_text=prompt if "--prompt" not in command else None,
                        timeout=420,
                    )
                except Exception as exc:
                    errors.append(f"{model} {command[:4]}: {type(exc).__name__}: {exc}")
                    continue
                if result.returncode == 0 and result.stdout.strip():
                    output_dir = base.EVIDENCE / "model"
                    output_dir.mkdir(parents=True, exist_ok=True)
                    (output_dir / f"call-{call_index:03d}-{model.replace('/', '_')}-cli.txt").write_text(
                        result.stdout, encoding="utf-8"
                    )
                    return result.stdout, model + "-gh-cli"
                errors.append(f"{model} exit={result.returncode}: {result.stdout[:3000]}")
        raise RuntimeError("all GitHub Models REST and CLI paths failed:\n" + "\n".join(errors))


base.call_model = call_model_v3


if __name__ == "__main__":
    raise SystemExit(base.main())
