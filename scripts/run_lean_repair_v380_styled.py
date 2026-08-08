from __future__ import annotations

import os
from pathlib import Path
import subprocess
import tempfile

import lean_repair_loop_v377 as core

_original_prompt_for = core.prompt_for
_original_model_request = core.model_request
_extension_ready = False


def styled_prompt_for(*args, **kwargs):
    base = _original_prompt_for(*args, **kwargs)
    style = os.environ.get('REPAIR_STYLE', '').strip()
    if not style:
        return base
    return base + f"\nAdditional repair strategy for this candidate:\n{style}\n"


def ensure_extension(env: dict[str, str]) -> None:
    global _extension_ready
    if _extension_ready:
        return
    probe = subprocess.run(
        ['gh', 'models', '--help'], text=True, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, env=env, check=False, timeout=60
    )
    if probe.returncode != 0:
        subprocess.run(
            ['gh', 'extension', 'install', 'github/gh-models', '--force'],
            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            env=env, check=False, timeout=180
        )
    final_probe = subprocess.run(
        ['gh', 'models', '--help'], text=True, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, env=env, check=False, timeout=60
    )
    if final_probe.returncode != 0:
        raise RuntimeError('official gh models CLI is unavailable: ' + final_probe.stdout[-2000:])
    _extension_ready = True


def cli_model_request(prompt: str, attempt: int):
    try:
        return _original_model_request(prompt, attempt)
    except Exception as rest_error:
        token = os.environ.get('GITHUB_TOKEN', '').strip()
        if not token:
            raise RuntimeError(f'REST failed and GITHUB_TOKEN is unavailable: {rest_error}')
        env = os.environ.copy()
        env['GH_TOKEN'] = token
        env['GITHUB_TOKEN'] = token
        ensure_extension(env)
        models = [
            x.strip() for x in os.environ.get(
                'MODEL_CANDIDATES', 'openai/gpt-5,openai/gpt-4.1,openai/gpt-4o'
            ).split(',') if x.strip()
        ]
        failures: list[str] = [f'REST: {rest_error}']
        with tempfile.NamedTemporaryFile('w', encoding='utf-8', delete=False) as handle:
            handle.write(prompt)
            prompt_path = Path(handle.name)
        try:
            for model in models:
                commands = [
                    ['gh', 'models', 'run', model, prompt],
                    ['gh', 'models', 'run', model, '--prompt', prompt],
                    ['gh', 'models', 'run', model, '-p', prompt],
                ]
                for command in commands:
                    try:
                        proc = subprocess.run(
                            command, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, env=env, check=False, timeout=300
                        )
                    except Exception as exc:
                        failures.append(f'{model} {command[3:5]}: {exc}')
                        continue
                    output = proc.stdout.strip()
                    if proc.returncode == 0 and output and '--- ' in output and '+++ ' in output:
                        return model + ':gh-cli', output
                    failures.append(
                        f"{model} {' '.join(command[3:5])}: exit={proc.returncode} tail={output[-600:]}"
                    )
                try:
                    with prompt_path.open('r', encoding='utf-8') as stream:
                        proc = subprocess.run(
                            ['gh', 'models', 'run', model], stdin=stream, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                            env=env, check=False, timeout=300
                        )
                    output = proc.stdout.strip()
                    if proc.returncode == 0 and output and '--- ' in output and '+++ ' in output:
                        return model + ':gh-cli-stdin', output
                    failures.append(
                        f'{model} stdin: exit={proc.returncode} tail={output[-600:]}'
                    )
                except Exception as exc:
                    failures.append(f'{model} stdin: {exc}')
        finally:
            prompt_path.unlink(missing_ok=True)
        raise RuntimeError('REST and official gh models CLI failed: ' + ' | '.join(failures))


core.prompt_for = styled_prompt_for
core.model_request = cli_model_request

if __name__ == '__main__':
    raise SystemExit(core.main())
