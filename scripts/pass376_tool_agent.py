from __future__ import annotations

import argparse
import importlib.util
import json
import os
import re
import subprocess
import sys
import time
import urllib.error
import urllib.request
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
CORE_PATH = Path(__file__).with_name("pass376_multitarget_agent.py")
spec = importlib.util.spec_from_file_location("pass376_core_tools", CORE_PATH)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load {CORE_PATH}")
core = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = core
spec.loader.exec_module(core)

LOG_ROOT = ROOT / "build-logs" / "pass376-tool-agent"
STATE_PATH = ROOT / "build-logs" / "pass376-v2-state.json"
BASELINE_PATH = ROOT / "build-logs" / "pass376-v2-baseline.json"


def load_state() -> dict[str, Any]:
    if STATE_PATH.exists():
        return json.loads(STATE_PATH.read_text(encoding="utf-8"))
    return {"version": 2, "verified": {}, "history": [], "success": False}


def select_target(state: dict[str, Any], paths: list[Path]) -> Path:
    active = state.get("active_target")
    if isinstance(active, str):
        candidate = ROOT / active
        if candidate in paths and candidate.exists():
            return candidate
    verified = state.get("verified", {})
    for path in paths:
        key = str(path.relative_to(ROOT))
        item = verified.get(key)
        if not item or item.get("sha256") != core.sha256_file(path):
            return path
    return paths[-1]


def compact_compile(result: core.CompileResult) -> dict[str, Any]:
    text = result.log_path.read_text(encoding="utf-8", errors="replace")
    lines = text.splitlines()
    error_blocks: list[str] = []
    for index, line in enumerate(lines):
        if " error:" in line and ".lean:" in line:
            block = "\n".join(lines[index : min(len(lines), index + 28)])
            error_blocks.append(block)
            if len(error_blocks) >= 8:
                break
    return {
        **core.result_payload(result),
        "error_excerpt": "\n\n".join(error_blocks)[:24000],
    }


def reduction_key(result: core.CompileResult, width: int = 12) -> tuple[int, ...]:
    if result.passed:
        return (1,) + (10**9,) * (width * 2 + 1)
    values = [0]
    for line, col in result.positions[:width]:
        values.extend([line, col])
    while len(values) < 1 + width * 2:
        values.extend([10**9, 10**9])
    try:
        size = result.log_path.stat().st_size
    except OSError:
        size = 10**9
    values.append(-size)
    return tuple(values[: 2 + width * 2])


def chat_request(model: str, messages: list[dict[str, Any]], tools: list[dict[str, Any]]) -> dict[str, Any]:
    token = os.environ.get("GITHUB_TOKEN") or os.environ.get("GH_TOKEN")
    if not token:
        raise RuntimeError("GITHUB_TOKEN is unavailable")
    payload = {
        "model": model,
        "messages": messages,
        "tools": tools,
        "tool_choice": "auto",
        "temperature": 0.05,
        "max_tokens": 6500,
    }
    request = urllib.request.Request(
        "https://models.github.ai/inference/chat/completions",
        data=json.dumps(payload).encode("utf-8"),
        headers={
            "Authorization": f"Bearer {token}",
            "Content-Type": "application/json",
            "Accept": "application/json",
            "User-Agent": "pass376-tool-agent",
        },
        method="POST",
    )
    with urllib.request.urlopen(request, timeout=300) as response:
        return json.loads(response.read().decode("utf-8"))


def tool_definitions() -> list[dict[str, Any]]:
    def function(name: str, description: str, properties: dict[str, Any], required: list[str]):
        return {
            "type": "function",
            "function": {
                "name": name,
                "description": description,
                "parameters": {
                    "type": "object",
                    "properties": properties,
                    "required": required,
                    "additionalProperties": False,
                },
            },
        }
    return [
        function(
            "read_source",
            "Read a numbered contiguous range of the active Lean source file.",
            {
                "start_line": {"type": "integer", "minimum": 1},
                "end_line": {"type": "integer", "minimum": 1},
            },
            ["start_line", "end_line"],
        ),
        function(
            "search_repo",
            "Search current Lean project and Mathlib sources for an exact identifier or short pattern.",
            {"query": {"type": "string", "minLength": 1, "maxLength": 160}},
            ["query"],
        ),
        function(
            "compile",
            "Compile the active source and return the first current Lean errors.",
            {},
            [],
        ),
        function(
            "replace_exact",
            "Replace an exact source fragment. The replacement is rejected unless the expected occurrence count matches and the trust gate passes.",
            {
                "old": {"type": "string", "minLength": 1},
                "new": {"type": "string"},
                "expected_count": {"type": "integer", "minimum": 1, "maximum": 20},
            },
            ["old", "new", "expected_count"],
        ),
        function(
            "apply_patch",
            "Apply a unified diff for only the active source file. It is checked by git apply and the trust gate.",
            {"diff": {"type": "string", "minLength": 1}},
            ["diff"],
        ),
        function(
            "revert_last",
            "Revert the most recent accepted source edit in this tool session.",
            {},
            [],
        ),
        function(
            "finish",
            "Finish the tool session after compiling and confirming progress or success.",
            {"summary": {"type": "string", "maxLength": 2000}},
            ["summary"],
        ),
    ]


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--cycle", type=int, required=True)
    parser.add_argument("--budget-seconds", type=int, default=4800)
    parser.add_argument("--max-turns", type=int, default=48)
    args = parser.parse_args()

    LOG_ROOT.mkdir(parents=True, exist_ok=True)
    paths = core.target_paths()
    baseline_manifest = core.ensure_baseline(paths)
    state = load_state()
    target = select_target(state, paths)
    relative = str(target.relative_to(ROOT))
    snapshot = baseline_manifest[relative]
    valid, reason = core.validate_against_snapshot(target, snapshot)
    if not valid:
        raise RuntimeError(f"initial trust failure: {reason}")

    original = target.read_bytes()
    versions = [original]
    baseline = core.compile_target(
        target,
        f"tool-{target.stem}-cycle-{args.cycle:02d}-baseline",
        max_errors=16,
        timeout=1800,
    )
    if baseline.passed:
        print(f"[pass376-tool] {relative} already compiles")
        return 0

    models = [
        "openai/gpt-4.1",
        "openai/gpt-5-mini",
        "openai/gpt-4o",
    ]
    model_index = 0
    tools = tool_definitions()
    messages: list[dict[str, Any]] = [
        {
            "role": "system",
            "content": (
                "You are an expert Lean 4.33/mathlib proof repair agent operating through tools. "
                "Inspect the exact source and compiler output, search the current repository API, "
                "apply small proof-body fixes, and compile repeatedly. Never alter any public theorem, "
                "lemma, or corollary statement. Never use sorry, admit, axiom, unsafe, native_decide, "
                "or Lean.ofReduceBool. Work only on the active file. Do not finish until you have compiled "
                "the current source and either reached exit code 0 or made a clear compiler-frontier advance."
            ),
        },
        {
            "role": "user",
            "content": json.dumps(
                {
                    "active_file": relative,
                    "baseline": compact_compile(baseline),
                    "instruction": (
                        "Use read_source/search_repo/compile before editing. Fix earliest independent errors. "
                        "After each edit run compile and continue until success or a strong frontier advance."
                    ),
                },
                ensure_ascii=False,
            ),
        },
    ]
    deadline = time.monotonic() + args.budget_seconds
    latest = baseline
    finished_summary = ""

    for turn in range(1, args.max_turns + 1):
        if time.monotonic() > deadline - 120:
            break
        model = models[model_index % len(models)]
        try:
            body = chat_request(model, messages, tools)
        except (urllib.error.HTTPError, urllib.error.URLError, TimeoutError, KeyError, json.JSONDecodeError) as exc:
            with (LOG_ROOT / "model-errors.log").open("a", encoding="utf-8") as handle:
                handle.write(f"turn={turn} model={model} {type(exc).__name__}: {exc}\n")
            model_index += 1
            if model_index >= len(models) * 3:
                break
            continue
        choice = body.get("choices", [{}])[0]
        message = choice.get("message", {})
        content = message.get("content") or ""
        tool_calls = message.get("tool_calls") or []
        assistant_message: dict[str, Any] = {"role": "assistant", "content": content}
        if tool_calls:
            assistant_message["tool_calls"] = tool_calls
        messages.append(assistant_message)
        (LOG_ROOT / f"cycle-{args.cycle:02d}-turn-{turn:02d}.json").write_text(
            json.dumps(body, ensure_ascii=False, indent=2), encoding="utf-8"
        )
        if not tool_calls:
            messages.append(
                {
                    "role": "user",
                    "content": "Use the available tools now. Compile before claiming completion.",
                }
            )
            continue

        should_finish = False
        for call in tool_calls:
            function = call.get("function", {})
            name = function.get("name")
            try:
                arguments = json.loads(function.get("arguments") or "{}")
            except json.JSONDecodeError:
                arguments = {}
            result: dict[str, Any]

            if name == "read_source":
                lines = target.read_text(encoding="utf-8").splitlines()
                start = max(1, int(arguments.get("start_line", 1)))
                end = min(len(lines), max(start, int(arguments.get("end_line", start))))
                end = min(end, start + 260)
                result = {
                    "start_line": start,
                    "end_line": end,
                    "content": "\n".join(
                        f"{number:6d}: {lines[number - 1]}" for number in range(start, end + 1)
                    ),
                }

            elif name == "search_repo":
                query = str(arguments.get("query", ""))[:160]
                if not query:
                    result = {"error": "empty query"}
                else:
                    process = subprocess.run(
                        [
                            "rg",
                            "-n",
                            "-F",
                            "--glob",
                            "*.lean",
                            query,
                            "Mathlib",
                            "PrimalitySheafVerification",
                        ],
                        cwd=ROOT,
                        text=True,
                        stdout=subprocess.PIPE,
                        stderr=subprocess.STDOUT,
                        timeout=60,
                    )
                    result = {
                        "query": query,
                        "matches": "\n".join(process.stdout.splitlines()[:120])[:24000],
                    }

            elif name == "compile":
                latest = core.compile_target(
                    target,
                    f"tool-{target.stem}-cycle-{args.cycle:02d}-turn-{turn:02d}",
                    max_errors=16,
                    timeout=1800,
                )
                result = compact_compile(latest)

            elif name == "replace_exact":
                old = str(arguments.get("old", ""))
                new = str(arguments.get("new", ""))
                expected = int(arguments.get("expected_count", 1))
                text = target.read_text(encoding="utf-8")
                count = text.count(old)
                if count != expected:
                    result = {"accepted": False, "error": f"expected {expected} occurrence(s), found {count}"}
                else:
                    before = target.read_bytes()
                    target.write_text(text.replace(old, new), encoding="utf-8")
                    trusted, trust_reason = core.validate_against_snapshot(target, snapshot)
                    if not trusted:
                        target.write_bytes(before)
                        result = {"accepted": False, "error": trust_reason}
                    else:
                        versions.append(target.read_bytes())
                        result = {
                            "accepted": True,
                            "sha256": core.sha256_file(target),
                            "instruction": "Run compile next.",
                        }

            elif name == "apply_patch":
                diff = str(arguments.get("diff", ""))
                expected = relative
                paths_in_diff = re.findall(r"^(?:---|\+\+\+)\s+[ab]/([^\t\n]+)", diff, re.M)
                if not paths_in_diff or any(path != expected for path in paths_in_diff):
                    result = {"accepted": False, "error": "diff must change only the active file"}
                else:
                    patch_path = LOG_ROOT / f"cycle-{args.cycle:02d}-turn-{turn:02d}.patch"
                    patch_path.write_text(diff.strip() + "\n", encoding="utf-8")
                    check = subprocess.run(
                        ["git", "apply", "--check", str(patch_path)],
                        cwd=ROOT,
                        text=True,
                        stdout=subprocess.PIPE,
                        stderr=subprocess.STDOUT,
                    )
                    if check.returncode != 0:
                        result = {"accepted": False, "error": check.stdout[-3000:]}
                    else:
                        before = target.read_bytes()
                        applied = subprocess.run(
                            ["git", "apply", "--whitespace=nowarn", str(patch_path)],
                            cwd=ROOT,
                            text=True,
                            stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT,
                        )
                        trusted, trust_reason = core.validate_against_snapshot(target, snapshot)
                        if applied.returncode != 0 or not trusted:
                            target.write_bytes(before)
                            result = {
                                "accepted": False,
                                "error": applied.stdout[-2000:] if applied.returncode else trust_reason,
                            }
                        else:
                            versions.append(target.read_bytes())
                            result = {
                                "accepted": True,
                                "sha256": core.sha256_file(target),
                                "instruction": "Run compile next.",
                            }

            elif name == "revert_last":
                if len(versions) <= 1:
                    result = {"reverted": False, "error": "no edit to revert"}
                else:
                    versions.pop()
                    target.write_bytes(versions[-1])
                    result = {"reverted": True, "sha256": core.sha256_file(target)}

            elif name == "finish":
                finished_summary = str(arguments.get("summary", ""))
                latest = core.compile_target(
                    target,
                    f"tool-{target.stem}-cycle-{args.cycle:02d}-finish",
                    max_errors=16,
                    timeout=1800,
                )
                result = compact_compile(latest)
                should_finish = True

            else:
                result = {"error": f"unknown tool {name!r}"}

            messages.append(
                {
                    "role": "tool",
                    "tool_call_id": call.get("id", f"turn-{turn}"),
                    "content": json.dumps(result, ensure_ascii=False)[:30000],
                }
            )
        if should_finish:
            break
        if latest.passed:
            break

    final = core.compile_target(
        target,
        f"tool-{target.stem}-cycle-{args.cycle:02d}-final",
        max_errors=16,
        timeout=1800,
    )
    trusted, reason = core.validate_against_snapshot(target, snapshot)
    advanced = final.passed or reduction_key(final) > reduction_key(baseline)
    if not trusted or not advanced:
        target.write_bytes(original)
        print(
            f"[pass376-tool] rejected final candidate trusted={trusted} advanced={advanced} reason={reason}"
        )
        return 2

    state.setdefault("history", []).append(
        {
            "cycle": args.cycle,
            "target": relative,
            "event": "function-calling-tool-agent",
            "accepted": True,
            "summary": finished_summary,
            "before_sha256": core.sha256_bytes(original),
            "after_sha256": core.sha256_file(target),
            "baseline": core.result_payload(baseline),
            "final": core.result_payload(final),
        }
    )
    state["active_target"] = relative
    state["success"] = False
    core.invalidate_from(state, paths, paths.index(target))
    core.write_json(STATE_PATH, state)
    print(
        f"[pass376-tool] accepted {relative}: "
        f"first={final.first_line}:{final.first_col} errors={final.error_count}"
    )
    return 0 if final.passed else 2


if __name__ == "__main__":
    raise SystemExit(main())
