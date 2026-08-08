from __future__ import annotations

import importlib.util
import json
import os
import re
import shutil
import subprocess
import sys
import urllib.error
import urllib.request
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
STATE_DIR = ROOT / "build-logs" / "fa381-agent"
TOKEN = os.environ.get("GITHUB_TOKEN", "")
MODELS = [
    x.strip()
    for x in os.environ.get(
        "FA381_MODELS", "openai/gpt-5,openai/gpt-4.1,openai/gpt-4o"
    ).split(",")
    if x.strip()
]
MAX_FRONTIERS = int(os.environ.get("FA381_MAX_FRONTIERS", "6"))
MAX_REVISIONS = int(os.environ.get("FA381_MAX_REVISIONS", "5"))


def import_script(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot import {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


C = import_script("fa378_base_dialogue", ROOT / "scripts" / "fa378_competitive_agent.py")
C.STATE_DIR = STATE_DIR
C.TOKEN = TOKEN
ERROR_HEADER = C.ERROR_HEADER


def run(args: list[str], *, timeout: int | None = None):
    return subprocess.run(
        args,
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=timeout,
        check=False,
    )


def compile_source(label: str, max_errors: int = 35):
    proc = run(
        ["lake", "env", "lean", f"-DmaxErrors={max_errors}", str(TARGET.relative_to(ROOT))],
        timeout=2100,
    )
    (STATE_DIR / f"{label}.log").write_text(proc.stdout, encoding="utf-8")
    metric = C.metric_from_log(proc.returncode, proc.stdout, TARGET.read_bytes())
    (STATE_DIR / f"{label}-metric.json").write_text(json.dumps(metric.__dict__, indent=2), encoding="utf-8")
    return metric, proc.stdout


def declaration_context(lines: list[str], error_line: int) -> str:
    decl = re.compile(
        r"^\s*(?:(?:private|public|protected|noncomputable)\s+)*"
        r"(?:theorem|lemma|corollary|def|abbrev|instance|example)\b"
    )
    start = max(1, error_line - 35)
    for i in range(error_line, max(1, error_line - 650), -1):
        if decl.match(lines[i - 1]):
            start = max(1, i - 8)
            break
    end = min(len(lines), error_line + 150)
    for i in range(error_line + 1, min(len(lines), error_line + 650) + 1):
        if decl.match(lines[i - 1]):
            end = min(len(lines), i + 6)
            break
    return "\n".join(f"{i}: {lines[i - 1]}" for i in range(start, end + 1))


def initial_prompt(metric, log: str, frontier_number: int) -> str:
    match = next(ERROR_HEADER.finditer(log), None)
    if match is None:
        raise RuntimeError("no parsable Lean error header")
    line = int(match.group("line"))
    lines = TARGET.read_text(encoding="utf-8").splitlines()
    api = C.relevant_api_search(C.compiler_block(log, match))
    previous = []
    for path in [
        ROOT / "build-logs" / "fa379-agent" / "persistent-summary.txt",
        ROOT / "build-logs" / "fa380-agent" / "persistent-summary.txt",
    ]:
        if path.exists():
            previous.append(path.read_text(encoding="utf-8", errors="replace")[-7000:])
    return "\n".join(
        [
            "Return ONLY a unified diff for PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean.",
            "No prose and no Markdown fences.",
            "",
            "Repair exactly the first independent Lean error shown below.",
            "All existing public theorem/lemma/corollary names, binders, assumptions and conclusions are fingerprint-guarded and must remain unchanged.",
            "You may rewrite proof bodies and add private helper lemmas. Do not change imports.",
            "Never add sorry, admit, global axiom, unsafe, native_decide, or Lean.ofReduceBool.",
            "The patch will be compiled immediately; if it fails you will receive the exact compiler feedback and must return a corrected full unified diff against the same baseline source.",
            "",
            f"Frontier number: {frontier_number}",
            f"Baseline source SHA-256: {metric.source_sha256}",
            f"Baseline metric: errors={metric.errors}, first_line={metric.first_line}",
            "",
            "Compiler block:",
            "```text",
            C.compiler_block(log, match),
            "```",
            "",
            "Containing declaration and local context:",
            "```lean",
            declaration_context(lines, line),
            "```",
            "",
            "Exact-checkout API search:",
            api or "(no extra hits)",
            "",
            "Prior stalled strategies to avoid:",
            "```text",
            "\n".join(previous)[-12000:],
            "```",
        ]
    )


def chat(model: str, messages: list[dict[str, str]], tag: str) -> str:
    payload = {
        "model": model,
        "temperature": 0.08,
        "max_tokens": 14000,
        "messages": messages,
    }
    request = urllib.request.Request(
        "https://models.github.ai/inference/chat/completions",
        data=json.dumps(payload).encode("utf-8"),
        headers={
            "Authorization": f"Bearer {TOKEN}",
            "Content-Type": "application/json",
            "Accept": "application/vnd.github+json",
            "X-GitHub-Api-Version": "2022-11-28",
            "User-Agent": "primality-sheaf-fa381-dialogue",
        },
        method="POST",
    )
    with urllib.request.urlopen(request, timeout=420) as response:
        data = json.load(response)
    content = data["choices"][0]["message"]["content"]
    (STATE_DIR / f"{tag}.txt").write_text(content, encoding="utf-8")
    return content


def candidate_feedback(original: bytes, response: str, label: str, baseline_metric):
    TARGET.write_bytes(original)
    try:
        patch = C.extract_patch(response)
        if C.FORBIDDEN_ADDITION.search(patch):
            return None, "Rejected before compilation: forbidden proof escape in added lines."
        if C.IMPORT_CHANGE.search(patch):
            return None, "Rejected before compilation: imports may not be changed."
        patch_path = STATE_DIR / f"{label}.patch"
        patch_path.write_text(patch, encoding="utf-8")
        check = run(["git", "apply", "--check", str(patch_path)], timeout=60)
        if check.returncode != 0:
            return None, "`git apply --check` failed:\n" + check.stdout[-5000:]
        apply = run(["git", "apply", "--whitespace=nowarn", str(patch_path)], timeout=60)
        if apply.returncode != 0:
            return None, "`git apply` failed:\n" + apply.stdout[-5000:]
        after = TARGET.read_text(encoding="utf-8")
        preserved, reason = C.headers_preserved(original.decode("utf-8"), after)
        if not preserved:
            return None, "Rejected by public-statement fingerprint guard: " + reason
        metric, log = compile_source(label)
        source = TARGET.read_bytes()
        if metric.better_than(baseline_metric):
            return (source, metric, log, patch), "IMPROVED"
        first = next(ERROR_HEADER.finditer(log), None)
        block = C.compiler_block(log, first) if first else log[-9000:]
        feedback = (
            "The patch compiled but did not improve the guarded metric. Return a corrected full unified diff against the original baseline source.\n"
            f"Baseline: {baseline_metric.__dict__}\nCandidate: {metric.__dict__}\n"
            "Candidate compiler feedback:\n```text\n" + block + "\n```"
        )
        return None, feedback
    except Exception as exc:
        return None, "Patch processing raised an exception: " + repr(exc)
    finally:
        TARGET.write_bytes(original)


def main() -> int:
    STATE_DIR.mkdir(parents=True, exist_ok=True)
    for marker in [
        ROOT / "build-logs" / "fa377-agent" / "ALL_REQUIRED_TARGETS_2X_PASS",
        ROOT / "build-logs" / "fa378-agent" / "ALL_REQUIRED_TARGETS_2X_PASS",
        ROOT / "build-logs" / "fa379-agent" / "ALL_REQUIRED_TARGETS_2X_PASS",
        ROOT / "build-logs" / "fa380-agent" / "ALL_REQUIRED_TARGETS_2X_PASS",
    ]:
        if marker.exists():
            shutil.copy2(marker, STATE_DIR / "ALL_REQUIRED_TARGETS_2X_PASS")
            return 0
    materialized = ROOT / "build-logs" / "fa377-agent" / "materialized-pass376"
    if not materialized.exists():
        C.BASE.reconstruct_pass376_source()
        materialized.parent.mkdir(parents=True, exist_ok=True)
        materialized.write_text(C.sha256_bytes(TARGET.read_bytes()), encoding="utf-8")
    current_metric, current_log = compile_source("baseline", max_errors=80)
    if current_metric.exit_code == 0 and current_metric.errors == 0:
        C.BASE.verify_required_order()
        shutil.copy2(C.BASE.STATE_DIR / "ALL_REQUIRED_TARGETS_2X_PASS", STATE_DIR / "ALL_REQUIRED_TARGETS_2X_PASS")
        return 0
    accepted = 0
    history: list[dict[str, object]] = []
    for frontier in range(1, MAX_FRONTIERS + 1):
        original = TARGET.read_bytes()
        prompt = initial_prompt(current_metric, current_log, frontier)
        improved = None
        outcomes: list[dict[str, object]] = []
        for model in MODELS:
            messages = [
                {"role": "system", "content": "You are a senior Lean/mathlib maintainer. Output a minimal unified diff only."},
                {"role": "user", "content": prompt},
            ]
            for revision in range(1, MAX_REVISIONS + 1):
                tag = f"frontier-{frontier:02d}-{model.replace('/', '-')}-revision-{revision:02d}"
                try:
                    response = chat(model, messages, tag)
                except Exception as exc:
                    outcomes.append({"model": model, "revision": revision, "exception": repr(exc)})
                    break
                candidate, feedback = candidate_feedback(original, response, tag, current_metric)
                outcomes.append({"model": model, "revision": revision, "feedback": feedback[-5000:]})
                if candidate is not None:
                    improved = (*candidate, model, revision)
                    break
                messages.append({"role": "assistant", "content": response})
                messages.append({"role": "user", "content": feedback})
            if improved is not None:
                break
        record: dict[str, object] = {
            "frontier": frontier,
            "baseline": current_metric.__dict__,
            "outcomes": outcomes,
        }
        if improved is None:
            record["result"] = "no improving dialogue candidate"
            history.append(record)
            (STATE_DIR / "history.json").write_text(json.dumps(history, indent=2), encoding="utf-8")
            continue
        source, metric, log, patch, model, revision = improved
        TARGET.write_bytes(source)
        current_metric = metric
        current_log = log
        accepted += 1
        record.update({
            "result": "accepted",
            "model": model,
            "revision": revision,
            "metric": metric.__dict__,
        })
        history.append(record)
        shutil.copy2(TARGET, STATE_DIR / "best-source.lean")
        (STATE_DIR / "best-metric.json").write_text(json.dumps(metric.__dict__, indent=2), encoding="utf-8")
        (STATE_DIR / "history.json").write_text(json.dumps(history, indent=2), encoding="utf-8")
        print(f"[fa381] accepted frontier {frontier} model={model} revision={revision}: {metric}")
        if current_metric.exit_code == 0 and current_metric.errors == 0:
            C.BASE.verify_required_order()
            shutil.copy2(C.BASE.STATE_DIR / "ALL_REQUIRED_TARGETS_2X_PASS", STATE_DIR / "ALL_REQUIRED_TARGETS_2X_PASS")
            (STATE_DIR / "state.json").write_text(json.dumps({"complete": True, "accepted": accepted, "metric": metric.__dict__}, indent=2), encoding="utf-8")
            return 0
    (STATE_DIR / "state.json").write_text(
        json.dumps({"complete": False, "accepted": accepted, "metric": current_metric.__dict__, "history": history[-3:]}, indent=2),
        encoding="utf-8",
    )
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
