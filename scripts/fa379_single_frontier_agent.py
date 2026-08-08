from __future__ import annotations

import importlib.util
import json
import os
import re
import shutil
import subprocess
import sys
import time
import urllib.error
import urllib.request
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
STATE_DIR = ROOT / "build-logs" / "fa379-agent"
MAX_ROUNDS = int(os.environ.get("FA379_MAX_ROUNDS", "18"))
TOKEN = os.environ.get("GITHUB_TOKEN", "")
MODELS = [
    x.strip()
    for x in os.environ.get(
        "FA379_MODELS", "openai/gpt-5,openai/gpt-4.1,openai/gpt-4o"
    ).split(",")
    if x.strip()
]


def import_script(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot import {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


C = import_script("fa378_base", ROOT / "scripts" / "fa378_competitive_agent.py")
C.STATE_DIR = STATE_DIR
C.TOKEN = TOKEN
C.MODELS = MODELS
ERROR_HEADER = C.ERROR_HEADER


def run(args: list[str], *, input_text: str | None = None, timeout: int | None = None):
    return subprocess.run(
        args,
        cwd=ROOT,
        input=input_text,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=timeout,
        check=False,
    )


def compile_one(label: str):
    proc = run(
        [
            "lake",
            "env",
            "lean",
            "-DmaxErrors=1",
            str(TARGET.relative_to(ROOT)),
        ],
        timeout=2100,
    )
    (STATE_DIR / f"{label}.log").write_text(proc.stdout, encoding="utf-8")
    return C.metric_from_log(proc.returncode, proc.stdout, TARGET.read_bytes()), proc.stdout


def declaration_context(lines: list[str], error_line: int) -> str:
    start_pattern = re.compile(
        r"^\s*(?:(?:private|public|protected|noncomputable)\s+)*"
        r"(?:theorem|lemma|corollary|def|abbrev|instance|example)\b"
    )
    start = max(1, error_line - 40)
    for index in range(error_line, max(1, error_line - 500), -1):
        if start_pattern.match(lines[index - 1]):
            start = max(1, index - 6)
            break
    end = min(len(lines), error_line + 120)
    for index in range(error_line + 1, min(len(lines), error_line + 500) + 1):
        if start_pattern.match(lines[index - 1]):
            end = min(len(lines), index + 5)
            break
    return "\n".join(f"{i}: {lines[i - 1]}" for i in range(start, end + 1))


def previous_diagnosis() -> str:
    paths = [
        ROOT / "build-logs" / "fa377-agent" / "persistent-summary.txt",
        ROOT / "build-logs" / "fa378-agent" / "persistent-summary.txt",
        ROOT / "build-logs" / "fa378-agent" / "state.json",
    ]
    return "\n".join(
        f"===== {path} =====\n{path.read_text(encoding='utf-8', errors='replace')[-10000:]}"
        for path in paths
        if path.exists()
    )


def build_prompt(metric, log: str, round_number: int) -> str:
    match = next(ERROR_HEADER.finditer(log), None)
    if match is None:
        raise RuntimeError("compile failed without a parsable Lean error header")
    line = int(match.group("line"))
    lines = TARGET.read_text(encoding="utf-8").splitlines()
    block = C.compiler_block(log, match)
    context = declaration_context(lines, line)
    api = C.relevant_api_search(block)
    previous = previous_diagnosis()
    return "\n".join(
        [
            "Return ONLY a unified diff for PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean.",
            "No prose and no Markdown fences.",
            "",
            "This task targets exactly the first independent Lean error. The candidate is compiled after every patch.",
            "Preserve every existing public theorem/lemma/corollary name, binder, assumption, and conclusion.",
            "You may rewrite its proof body or add a private helper lemma. Do not change imports.",
            "Never add sorry, admit, global axiom, unsafe, native_decide, or Lean.ofReduceBool.",
            "Use Lean 4.33.0-rc1 and current Mathlib APIs. Prefer a small explicit calc/change/ext/simpa-only proof over broad simp.",
            "",
            f"Round: {round_number}",
            f"Source SHA-256: {metric.source_sha256}",
            f"Current first error: line {line}, column {match.group('col')}",
            "",
            "Compiler block:",
            "```text",
            block,
            "```",
            "",
            "Containing declaration and local context:",
            "```lean",
            context,
            "```",
            "",
            "Relevant exact-checkout API search:",
            api or "(no additional exact-name hits)",
            "",
            "Previous rejected/partial strategies; do not repeat them:",
            "```text",
            previous[-14000:],
            "```",
        ]
    )


def rest_query(model: str, prompt: str, temperature: float, tag: str) -> str:
    payload = {
        "model": model,
        "temperature": temperature,
        "max_tokens": 14000,
        "messages": [
            {
                "role": "system",
                "content": "You are a senior Lean/mathlib maintainer. Return a minimal unified diff only.",
            },
            {"role": "user", "content": prompt},
        ],
    }
    request = urllib.request.Request(
        "https://models.github.ai/inference/chat/completions",
        data=json.dumps(payload).encode("utf-8"),
        headers={
            "Authorization": f"Bearer {TOKEN}",
            "Content-Type": "application/json",
            "Accept": "application/vnd.github+json",
            "X-GitHub-Api-Version": "2022-11-28",
            "User-Agent": "primality-sheaf-fa379-agent",
        },
        method="POST",
    )
    with urllib.request.urlopen(request, timeout=360) as response:
        body = json.load(response)
    content = body["choices"][0]["message"]["content"]
    (STATE_DIR / f"{tag}.txt").write_text(content, encoding="utf-8")
    return content


def cli_query(model: str, prompt: str, tag: str) -> str:
    attempts = [
        ["gh", "models", "run", model, "--prompt", prompt],
        ["gh", "models", "run", model, "-p", prompt],
        ["gh", "models", "run", model],
    ]
    errors: list[str] = []
    for index, args in enumerate(attempts, 1):
        proc = run(args, input_text=prompt if index == 3 else None, timeout=420)
        if proc.returncode == 0 and ("diff --git " in proc.stdout or "--- a/" in proc.stdout):
            (STATE_DIR / f"{tag}-cli-{index}.txt").write_text(proc.stdout, encoding="utf-8")
            return proc.stdout
        errors.append(f"attempt {index} exit={proc.returncode}: {proc.stdout[-1500:]}")
    raise RuntimeError("gh models failed: " + " | ".join(errors))


def model_responses(prompt: str, round_number: int):
    results: list[tuple[str, str]] = []
    failures: list[str] = []
    for model in MODELS:
        for temperature in (0.0, 0.15):
            tag = f"round-{round_number:02d}-{model.replace('/', '-')}-t{temperature}"
            try:
                results.append((f"REST:{model}:t{temperature}", rest_query(model, prompt, temperature, tag)))
            except Exception as exc:
                failures.append(f"{tag}: {exc!r}")
        try:
            results.append((f"CLI:{model}", cli_query(model, prompt, f"round-{round_number:02d}-{model.replace('/', '-') }")))
        except Exception as exc:
            failures.append(f"CLI:{model}: {exc!r}")
    (STATE_DIR / f"round-{round_number:02d}-model-failures.txt").write_text(
        "\n".join(failures), encoding="utf-8"
    )
    return results


def main() -> int:
    STATE_DIR.mkdir(parents=True, exist_ok=True)
    inherited = [
        ROOT / "build-logs" / "fa377-agent" / "ALL_REQUIRED_TARGETS_2X_PASS",
        ROOT / "build-logs" / "fa378-agent" / "ALL_REQUIRED_TARGETS_2X_PASS",
    ]
    for marker in inherited:
        if marker.exists():
            shutil.copy2(marker, STATE_DIR / "ALL_REQUIRED_TARGETS_2X_PASS")
            return 0
    materialized = ROOT / "build-logs" / "fa377-agent" / "materialized-pass376"
    if not materialized.exists():
        C.BASE.reconstruct_pass376_source()
        materialized.parent.mkdir(parents=True, exist_ok=True)
        materialized.write_text(C.sha256_bytes(TARGET.read_bytes()), encoding="utf-8")
    baseline_metric, baseline_log = compile_one("baseline-one")
    # A second wider compile supplies the true error count for ranking.
    current_metric, current_log = C.compile_current("baseline-wide", max_errors=120)
    if current_metric.exit_code == 0 and current_metric.errors == 0:
        C.BASE.verify_required_order()
        shutil.copy2(C.BASE.STATE_DIR / "ALL_REQUIRED_TARGETS_2X_PASS", STATE_DIR / "ALL_REQUIRED_TARGETS_2X_PASS")
        return 0
    history: list[dict[str, object]] = []
    accepted = 0
    for round_number in range(1, MAX_ROUNDS + 1):
        one_metric, one_log = compile_one(f"round-{round_number:02d}-frontier")
        prompt = build_prompt(one_metric, one_log, round_number)
        (STATE_DIR / f"round-{round_number:02d}-prompt.md").write_text(prompt, encoding="utf-8")
        original = TARGET.read_bytes()
        candidates: list[tuple[object, bytes, str, str]] = []
        outcomes: list[dict[str, object]] = []
        for label, response in model_responses(prompt, round_number):
            TARGET.write_bytes(original)
            try:
                patch = C.extract_patch(response)
                source, metric, log = C.candidate_from_patch(
                    original,
                    patch,
                    f"round-{round_number:02d}-{re.sub('[^A-Za-z0-9]+', '-', label)}",
                )
                candidates.append((metric, source, log, label))
                outcomes.append({"label": label, "metric": metric.__dict__})
            except Exception as exc:
                outcomes.append({"label": label, "exception": repr(exc)})
            finally:
                TARGET.write_bytes(original)
        improving = [item for item in candidates if item[0].better_than(current_metric)]
        record: dict[str, object] = {
            "round": round_number,
            "frontier": one_metric.__dict__,
            "baseline": current_metric.__dict__,
            "outcomes": outcomes,
        }
        if not improving:
            record["result"] = "no improving candidate"
            history.append(record)
            (STATE_DIR / "history.json").write_text(json.dumps(history, indent=2), encoding="utf-8")
            continue
        best_metric, best_source, best_log, best_label = max(improving, key=lambda item: item[0].score())
        TARGET.write_bytes(best_source)
        current_metric = best_metric
        current_log = best_log
        accepted += 1
        record.update({"result": "accepted", "label": best_label, "metric": best_metric.__dict__})
        history.append(record)
        (STATE_DIR / "history.json").write_text(json.dumps(history, indent=2), encoding="utf-8")
        shutil.copy2(TARGET, STATE_DIR / "best-source.lean")
        (STATE_DIR / "best-metric.json").write_text(json.dumps(best_metric.__dict__, indent=2), encoding="utf-8")
        print(f"[fa379] accepted {best_label}: {best_metric}")
        if current_metric.exit_code == 0 and current_metric.errors == 0:
            C.BASE.verify_required_order()
            shutil.copy2(C.BASE.STATE_DIR / "ALL_REQUIRED_TARGETS_2X_PASS", STATE_DIR / "ALL_REQUIRED_TARGETS_2X_PASS")
            (STATE_DIR / "state.json").write_text(json.dumps({"complete": True, "accepted": accepted, "metric": current_metric.__dict__}, indent=2), encoding="utf-8")
            return 0
    (STATE_DIR / "state.json").write_text(
        json.dumps({"complete": False, "accepted": accepted, "metric": current_metric.__dict__, "history": history[-4:]}, indent=2),
        encoding="utf-8",
    )
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
