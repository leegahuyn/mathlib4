from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import time
import urllib.error
import urllib.request
from dataclasses import dataclass
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
PROJECT = ROOT / "PrimalitySheafVerification"
BUILD_LOGS = ROOT / "build-logs"
LOG_ROOT = BUILD_LOGS / "pass376-v2"
STATE_PATH = BUILD_LOGS / "pass376-v2-state.json"
BASELINE_PATH = BUILD_LOGS / "pass376-v2-baseline.json"
SUCCESS_MARKER = BUILD_LOGS / "pass376-fa-mock3-qym-2x-pass.txt"

ERROR_RE = re.compile(r"\.lean:(\d+):(\d+):\s+error:")
IMPORT_RE = re.compile(r"(?m)^\s*(?:public\s+)?import\s+([^\s]+)")
DECL_RE = re.compile(
    r"(?m)^(?P<indent>\s*)(?P<private>private\s+)?"
    r"(?P<kind>theorem|lemma|corollary)\s+(?P<name>[^\s(:{]+)"
)
FORBIDDEN_RE = re.compile(
    r"\b(?:sorry|admit|native_decide)\b|Lean\.ofReduceBool|"
    r"(?m)^\s*(?:unsafe\s+|axiom\s+)"
)
UNKNOWN_RE = re.compile(
    r"(?:Unknown identifier|unknown identifier|Invalid field|invalid field)[^`\n]*`([^`]+)`"
)

PREFERRED_MODELS = [
    "openai/gpt-5-mini",
    "openai/gpt-5",
    "openai/gpt-4.1",
    "openai/gpt-4o",
    "openai/gpt-4o-mini",
    "deepseek/DeepSeek-V3-0324",
    "meta/Llama-4-Scout-17B-16E-Instruct",
    "microsoft/Phi-4",
]


@dataclass(frozen=True)
class CompileResult:
    returncode: int
    positions: tuple[tuple[int, int], ...]
    log_path: Path
    elapsed_seconds: float

    @property
    def passed(self) -> bool:
        return self.returncode == 0 and not self.positions

    @property
    def first_line(self) -> int:
        return self.positions[0][0] if self.positions else (10**9 if self.passed else 0)

    @property
    def first_col(self) -> int:
        return self.positions[0][1] if self.positions else 0

    @property
    def error_count(self) -> int:
        return len(self.positions)

    def progress_key(self, width: int = 12) -> tuple[int, ...]:
        if self.passed:
            return (1,) + (10**9,) * (width * 2)
        flattened: list[int] = [0]
        for line, col in self.positions[:width]:
            flattened.extend([line, col])
        while len(flattened) < 1 + width * 2:
            flattened.extend([10**9, 10**9])
        return tuple(flattened[: 1 + width * 2])


def run(
    command: list[str],
    *,
    cwd: Path = ROOT,
    input_text: str | None = None,
    timeout: int | None = None,
    env: dict[str, str] | None = None,
) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        command,
        cwd=cwd,
        input=input_text,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=timeout,
        env=env,
    )


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def strip_comments_and_strings(text: str) -> str:
    out: list[str] = []
    index = 0
    block_depth = 0
    line_comment = False
    in_string = False
    in_char = False
    escaped = False
    while index < len(text):
        char = text[index]
        next_char = text[index + 1] if index + 1 < len(text) else ""
        if line_comment:
            if char == "\n":
                line_comment = False
                out.append("\n")
            else:
                out.append(" ")
            index += 1
            continue
        if block_depth:
            if char == "/" and next_char == "-":
                block_depth += 1
                out.extend("  ")
                index += 2
            elif char == "-" and next_char == "/":
                block_depth -= 1
                out.extend("  ")
                index += 2
            else:
                out.append("\n" if char == "\n" else " ")
                index += 1
            continue
        if in_string:
            out.append("\n" if char == "\n" else " ")
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
            index += 1
            continue
        if in_char:
            out.append("\n" if char == "\n" else " ")
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == "'":
                in_char = False
            index += 1
            continue
        if char == "-" and next_char == "-":
            line_comment = True
            out.extend("  ")
            index += 2
        elif char == "/" and next_char == "-":
            block_depth = 1
            out.extend("  ")
            index += 2
        elif char == '"':
            in_string = True
            out.append(" ")
            index += 1
        elif char == "'" and (
            index == 0 or not (text[index - 1].isalnum() or text[index - 1] == "_")
        ):
            in_char = True
            out.append(" ")
            index += 1
        else:
            out.append(char)
            index += 1
    return "".join(out)


def declaration_headers(text: str) -> dict[str, str]:
    clean = strip_comments_and_strings(text)
    headers: dict[str, str] = {}
    for match in DECL_RE.finditer(clean):
        if match.group("private"):
            continue
        name = match.group("name")
        start = match.start()
        round_depth = square_depth = curly_depth = 0
        cursor = match.end()
        end: int | None = None
        while cursor < len(clean):
            char = clean[cursor]
            if char == "(":
                round_depth += 1
            elif char == ")":
                round_depth = max(0, round_depth - 1)
            elif char == "[":
                square_depth += 1
            elif char == "]":
                square_depth = max(0, square_depth - 1)
            elif char == "{":
                curly_depth += 1
            elif char == "}":
                curly_depth = max(0, curly_depth - 1)
            if round_depth == square_depth == curly_depth == 0:
                if clean.startswith(":=", cursor):
                    end = cursor
                    break
                if clean.startswith(" where", cursor) or clean.startswith("\nwhere", cursor):
                    end = cursor
                    break
            cursor += 1
        if end is None:
            continue
        headers[name] = re.sub(r"\s+", " ", clean[start:end]).strip()
    return headers


def trust_snapshot(path: Path) -> dict[str, Any]:
    text = path.read_text(encoding="utf-8")
    clean = strip_comments_and_strings(text)
    return {
        "headers": declaration_headers(text),
        "imports": sorted(set(IMPORT_RE.findall(clean))),
    }


def validate_against_snapshot(path: Path, snapshot: dict[str, Any]) -> tuple[bool, str]:
    text = path.read_text(encoding="utf-8")
    clean = strip_comments_and_strings(text)
    forbidden = FORBIDDEN_RE.search(clean)
    if forbidden:
        return False, f"forbidden executable token: {forbidden.group(0)!r}"
    expected_headers = snapshot["headers"]
    actual_headers = declaration_headers(text)
    if set(actual_headers) != set(expected_headers):
        missing = sorted(set(expected_headers) - set(actual_headers))
        added = sorted(set(actual_headers) - set(expected_headers))
        return False, f"public declaration set changed; missing={missing[:6]} added={added[:6]}"
    changed = [name for name in expected_headers if actual_headers[name] != expected_headers[name]]
    if changed:
        return False, f"public declaration headers changed: {changed[:8]}"
    expected_imports = set(snapshot["imports"])
    actual_imports = set(IMPORT_RE.findall(clean))
    removed = sorted(expected_imports - actual_imports)
    if removed:
        return False, f"existing imports removed: {removed}"
    return True, "ok"


def target_paths() -> list[Path]:
    result = [PROJECT / "Mock2_FunctionalAnalysis.lean"]
    integrated = PROJECT / "Mock2_FunctionalAnalysis_Integrated.lean"
    if integrated.exists():
        result.append(integrated)
    for path in sorted(PROJECT.glob("Mock3*.lean")):
        if path not in result:
            result.append(path)
    qym = PROJECT / "QYM.lean"
    if qym.exists():
        result.append(qym)
    return result


def module_output_dir() -> Path:
    return ROOT / ".lake" / "build" / "lib" / "lean" / "PrimalitySheafVerification"


def clean_target_artifacts(path: Path) -> None:
    output = module_output_dir()
    for suffix in (".olean", ".ilean", ".olean.hash", ".ilean.hash"):
        (output / f"{path.stem}{suffix}").unlink(missing_ok=True)


def compile_target(
    path: Path,
    label: str,
    *,
    max_errors: int = 12,
    timeout: int = 1800,
) -> CompileResult:
    LOG_ROOT.mkdir(parents=True, exist_ok=True)
    safe_label = re.sub(r"[^A-Za-z0-9_.-]+", "-", label)
    log_path = LOG_ROOT / f"{safe_label}.log"
    started = time.monotonic()
    try:
        process = run(
            [
                "lake",
                "env",
                "lean",
                f"-DmaxErrors={max_errors}",
                str(path.relative_to(ROOT)),
            ],
            timeout=timeout,
        )
        output = process.stdout
        returncode = process.returncode
    except subprocess.TimeoutExpired as exc:
        output = (exc.stdout or "") + "\n[pass376-v2] compiler timeout\n"
        returncode = 124
    elapsed = time.monotonic() - started
    log_path.write_text(output, encoding="utf-8")
    positions = tuple((int(line), int(col)) for line, col in ERROR_RE.findall(output))
    if returncode != 0 and not positions:
        positions = ((0, 0),)
    return CompileResult(returncode, positions, log_path, elapsed)


def result_payload(result: CompileResult) -> dict[str, Any]:
    return {
        "returncode": result.returncode,
        "error_count": result.error_count,
        "first_line": result.first_line,
        "first_col": result.first_col,
        "positions": [list(item) for item in result.positions],
        "elapsed_seconds": round(result.elapsed_seconds, 3),
        "log": str(result.log_path.relative_to(ROOT)),
    }


def load_json(path: Path, fallback: Any) -> Any:
    if not path.exists():
        return fallback
    return json.loads(path.read_text(encoding="utf-8"))


def write_json(path: Path, payload: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2), encoding="utf-8")


def ensure_baseline(paths: list[Path]) -> dict[str, Any]:
    baseline = load_json(BASELINE_PATH, {})
    changed = False
    for path in paths:
        key = str(path.relative_to(ROOT))
        if key not in baseline:
            baseline[key] = trust_snapshot(path)
            changed = True
    if changed or not BASELINE_PATH.exists():
        write_json(BASELINE_PATH, baseline)
    return baseline


def discover_models() -> list[str]:
    token = os.environ.get("GITHUB_TOKEN") or os.environ.get("GH_TOKEN")
    available: list[str] = []
    if token:
        request = urllib.request.Request(
            "https://models.github.ai/catalog/models",
            headers={
                "Authorization": f"Bearer {token}",
                "Accept": "application/json",
                "User-Agent": "pass376-multitarget-agent",
            },
        )
        try:
            with urllib.request.urlopen(request, timeout=90) as response:
                body = json.loads(response.read().decode("utf-8"))
            entries = body if isinstance(body, list) else body.get("models", [])
            for entry in entries:
                if not isinstance(entry, dict):
                    continue
                name = entry.get("id") or entry.get("name") or entry.get("model")
                if isinstance(name, str):
                    available.append(name)
        except Exception as exc:  # diagnostics only; fallbacks remain
            LOG_ROOT.mkdir(parents=True, exist_ok=True)
            with (LOG_ROOT / "model-errors.log").open("a", encoding="utf-8") as handle:
                handle.write(f"catalog: {type(exc).__name__}: {exc}\n")
    ordered = [model for model in PREFERRED_MODELS if model in available]
    ordered.extend(model for model in available if model not in ordered)
    ordered.extend(model for model in PREFERRED_MODELS if model not in ordered)
    deduplicated: list[str] = []
    for model in ordered:
        if model not in deduplicated:
            deduplicated.append(model)
    return deduplicated[:16]


def rest_model_call(prompt: str, model: str) -> str | None:
    token = os.environ.get("GITHUB_TOKEN") or os.environ.get("GH_TOKEN")
    if not token:
        return None
    payload = {
        "model": model,
        "messages": [
            {
                "role": "system",
                "content": (
                    "You repair Lean 4.33/mathlib proofs. Return only a minimal unified diff. "
                    "Never use sorry, admit, axiom, unsafe, native_decide, Lean.ofReduceBool, "
                    "or alter a public declaration statement."
                ),
            },
            {"role": "user", "content": prompt},
        ],
        "temperature": 0.05,
        "max_tokens": 9000,
    }
    request = urllib.request.Request(
        "https://models.github.ai/inference/chat/completions",
        data=json.dumps(payload).encode("utf-8"),
        headers={
            "Authorization": f"Bearer {token}",
            "Content-Type": "application/json",
            "Accept": "application/json",
            "User-Agent": "pass376-multitarget-agent",
        },
        method="POST",
    )
    try:
        with urllib.request.urlopen(request, timeout=240) as response:
            body = json.loads(response.read().decode("utf-8"))
        return body["choices"][0]["message"]["content"]
    except Exception as exc:
        LOG_ROOT.mkdir(parents=True, exist_ok=True)
        with (LOG_ROOT / "model-errors.log").open("a", encoding="utf-8") as handle:
            handle.write(f"REST {model}: {type(exc).__name__}: {exc}\n")
        return None


def cli_model_call(prompt: str, model: str) -> str | None:
    if shutil.which("gh") is None:
        return None
    environment = os.environ.copy()
    environment.setdefault("GH_TOKEN", environment.get("GITHUB_TOKEN", ""))
    commands = [
        ["gh", "models", "run", model, "--prompt", prompt],
        ["gh", "models", "run", model, prompt],
        ["gh", "models", "run", model],
    ]
    for index, command in enumerate(commands):
        try:
            process = run(
                command,
                input_text=prompt if index == 2 else None,
                timeout=300,
                env=environment,
            )
        except (OSError, subprocess.TimeoutExpired):
            continue
        if process.returncode == 0 and process.stdout.strip():
            return process.stdout
    return None


def model_call(prompt: str, model: str, output_path: Path) -> str | None:
    response = rest_model_call(prompt, model)
    if response is None:
        response = cli_model_call(prompt, model)
    if response:
        output_path.parent.mkdir(parents=True, exist_ok=True)
        output_path.write_text(response, encoding="utf-8")
    return response


def error_context(path: Path, result: CompileResult) -> str:
    log = result.log_path.read_text(encoding="utf-8", errors="replace")
    source_lines = path.read_text(encoding="utf-8").splitlines()
    chunks = ["LEAN ERROR OUTPUT\n" + log[:26000]]
    seen: set[int] = set()
    for line, col in result.positions[:8]:
        if line <= 0 or line in seen:
            continue
        seen.add(line)
        low = max(1, line - 65)
        high = min(len(source_lines), line + 80)
        numbered = "\n".join(
            f"{number:6d}: {source_lines[number - 1]}" for number in range(low, high + 1)
        )
        chunks.append(f"SOURCE CONTEXT AROUND {line}:{col}\n{numbered}")
    api_hints: list[str] = []
    identifiers = []
    for identifier in UNKNOWN_RE.findall(log):
        if identifier not in identifiers:
            identifiers.append(identifier)
    for identifier in identifiers[:8]:
        try:
            search = run(
                [
                    "rg",
                    "-n",
                    "-F",
                    "--glob",
                    "*.lean",
                    identifier,
                    "Mathlib",
                    "PrimalitySheafVerification",
                ],
                timeout=45,
            )
            if search.stdout.strip():
                api_hints.append(f"SEARCH RESULTS FOR {identifier}\n" + "\n".join(search.stdout.splitlines()[:30]))
        except (OSError, subprocess.TimeoutExpired):
            pass
    chunks.extend(api_hints)
    return "\n\n".join(chunks)[:70000]


def build_prompt(
    path: Path,
    result: CompileResult,
    strategy: int,
    rejection: str,
) -> str:
    strategies = [
        "Make the smallest proof-body/API correction for the first independent errors.",
        "Search the supplied current-API hints and replace obsolete theorem or field usage explicitly.",
        "Rewrite the failing proof from first principles using ext/change/calc and fully qualified lemmas.",
        "Add a small private helper theorem if that removes a repeated proof obstruction.",
        "Separate dependent transports with have/change/simpa rather than relying on definitional equality.",
    ]
    relative = path.relative_to(ROOT)
    return f"""
Repair the first independent Lean errors in `{relative}`.

Hard constraints:
- Return ONLY a unified diff for exactly `{relative}`.
- Keep every existing non-private theorem/lemma/corollary name, binder, assumption, and conclusion unchanged.
- You may change proof bodies and add only `private lemma` or `private theorem` helpers.
- Never add/use `sorry`, `admit`, global `axiom`, `unsafe`, `native_decide`, or `Lean.ofReduceBool`.
- Never delete an existing import.
- Use Lean 4.33.0-rc1 and the checked-out mathlib API.
- Fix no more than the first five independent errors in one patch.
- Do not mask errors with huge heartbeat settings or broad source rewrites.
- {strategies[strategy % len(strategies)]}

Compiler: exit={result.returncode}; first={result.first_line}:{result.first_col}; visible_errors={result.error_count}.
Previous rejection: {rejection or '(none)'}

{error_context(path, result)}
""".strip()


def extract_diff(response: str, path: Path) -> str | None:
    fenced = re.search(r"```(?:diff|patch)?\s*\n(.*?)```", response, re.S)
    if fenced:
        response = fenced.group(1)
    starts = [
        position
        for token in ("diff --git ", "--- a/")
        if (position := response.find(token)) >= 0
    ]
    if not starts:
        return None
    diff = response[min(starts) :].strip() + "\n"
    paths = re.findall(r"^(?:---|\+\+\+)\s+[ab]/([^\t\n]+)", diff, re.M)
    expected = str(path.relative_to(ROOT))
    if not paths or any(item != expected for item in paths):
        return None
    return diff


def append_history(state: dict[str, Any], entry: dict[str, Any]) -> None:
    history = state.setdefault("history", [])
    history.append(entry)
    if len(history) > 500:
        del history[:-500]
    write_json(STATE_PATH, state)


def invalidate_from(state: dict[str, Any], paths: list[Path], index: int) -> None:
    verified = state.setdefault("verified", {})
    for target in paths[index:]:
        verified.pop(str(target.relative_to(ROOT)), None)


def try_model_patch(
    path: Path,
    baseline_result: CompileResult,
    snapshot: dict[str, Any],
    models: list[str],
    cycle: int,
    attempt_seed: int,
) -> tuple[bool, CompileResult, str]:
    original_bytes = path.read_bytes()
    rejection = ""
    relative = str(path.relative_to(ROOT))
    for attempt in range(6):
        model = models[(attempt_seed + attempt) % len(models)]
        strategy = cycle + attempt
        prompt = build_prompt(path, baseline_result, strategy, rejection)
        response_path = LOG_ROOT / path.stem / f"cycle-{cycle:02d}-attempt-{attempt}-{model.replace('/', '_')}.txt"
        response = model_call(prompt, model, response_path)
        if not response:
            rejection = f"model {model} returned no response"
            continue
        diff = extract_diff(response, path)
        if diff is None:
            rejection = f"model {model} did not return a one-file unified diff"
            continue
        patch_path = LOG_ROOT / path.stem / f"cycle-{cycle:02d}-attempt-{attempt}.patch"
        patch_path.parent.mkdir(parents=True, exist_ok=True)
        patch_path.write_text(diff, encoding="utf-8")
        path.write_bytes(original_bytes)
        check = run(["git", "apply", "--check", str(patch_path)])
        if check.returncode != 0:
            rejection = "git apply --check failed: " + check.stdout[-1400:]
            continue
        applied = run(["git", "apply", "--whitespace=nowarn", str(patch_path)])
        if applied.returncode != 0:
            rejection = "git apply failed: " + applied.stdout[-1400:]
            continue
        valid, reason = validate_against_snapshot(path, snapshot)
        if not valid:
            path.write_bytes(original_bytes)
            rejection = reason
            continue
        candidate = compile_target(
            path,
            f"{path.stem}-cycle-{cycle:02d}-attempt-{attempt}",
            max_errors=12,
        )
        if candidate.passed or candidate.progress_key() > baseline_result.progress_key():
            return True, candidate, f"accepted {model}: {reason}"
        path.write_bytes(original_bytes)
        rejection = (
            f"compiler did not advance: baseline={baseline_result.progress_key()} "
            f"candidate={candidate.progress_key()}"
        )
    path.write_bytes(original_bytes)
    return False, baseline_result, rejection


def verify_twice(path: Path, snapshot: dict[str, Any], cycle: int) -> tuple[bool, list[CompileResult], str]:
    valid, reason = validate_against_snapshot(path, snapshot)
    if not valid:
        return False, [], reason
    results: list[CompileResult] = []
    for run_number in (1, 2):
        clean_target_artifacts(path)
        result = compile_target(
            path,
            f"{path.stem}-cycle-{cycle:02d}-verify-{run_number}",
            max_errors=2000,
            timeout=3600,
        )
        results.append(result)
        if not result.passed:
            return False, results, f"verification run {run_number} failed"
        output = module_output_dir()
        if not (output / f"{path.stem}.olean").exists() or not (output / f"{path.stem}.ilean").exists():
            return False, results, "expected .olean/.ilean were not generated"
    return True, results, "ok"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--budget-seconds", type=int, default=2400)
    parser.add_argument("--cycle", type=int, default=1)
    args = parser.parse_args()

    LOG_ROOT.mkdir(parents=True, exist_ok=True)
    SUCCESS_MARKER.unlink(missing_ok=True)
    paths = target_paths()
    if not paths or paths[0].name != "Mock2_FunctionalAnalysis.lean":
        raise RuntimeError("FunctionalAnalysis target is missing")
    baseline = ensure_baseline(paths)
    state = load_json(
        STATE_PATH,
        {
            "version": 2,
            "verified": {},
            "history": [],
            "success": False,
        },
    )
    models = discover_models()
    if not models:
        raise RuntimeError("no GitHub Models candidates are available")
    state["models"] = models
    state["last_cycle"] = args.cycle
    deadline = time.monotonic() + args.budget_seconds

    for index, path in enumerate(paths):
        relative = str(path.relative_to(ROOT))
        snapshot = baseline[relative]
        valid, reason = validate_against_snapshot(path, snapshot)
        if not valid:
            append_history(
                state,
                {"cycle": args.cycle, "target": relative, "event": "trust-failure", "reason": reason},
            )
            state["success"] = False
            write_json(STATE_PATH, state)
            return 3

        current_sha = sha256_file(path)
        verified_entry = state.setdefault("verified", {}).get(relative)
        initial = compile_target(path, f"{path.stem}-cycle-{args.cycle:02d}-baseline", max_errors=12)
        append_history(
            state,
            {"cycle": args.cycle, "target": relative, "event": "baseline", **result_payload(initial)},
        )

        if initial.passed and verified_entry and verified_entry.get("sha256") == current_sha:
            print(f"[pass376-v2] {relative}: prior two-pass proof retained; dependency rebuilt")
            continue

        result = initial
        stalls = 0
        local_iteration = 0
        while not result.passed and time.monotonic() < deadline - 480:
            local_iteration += 1
            accepted, candidate, note = try_model_patch(
                path,
                result,
                snapshot,
                models,
                args.cycle * 100 + local_iteration,
                args.cycle + local_iteration,
            )
            append_history(
                state,
                {
                    "cycle": args.cycle,
                    "iteration": local_iteration,
                    "target": relative,
                    "event": "repair",
                    "accepted": accepted,
                    "note": note,
                    **result_payload(candidate),
                },
            )
            if accepted:
                result = candidate
                stalls = 0
                invalidate_from(state, paths, index)
                print(
                    f"[pass376-v2] {relative}: advanced to "
                    f"{result.first_line}:{result.first_col} visible_errors={result.error_count}"
                )
            else:
                stalls += 1
                print(f"[pass376-v2] {relative}: stalled {stalls}: {note}")
                if stalls >= 8:
                    break

        if not result.passed:
            state["active_target"] = relative
            state["frontier"] = result_payload(result)
            state["success"] = False
            write_json(STATE_PATH, state)
            return 2

        verified, verification, note = verify_twice(path, snapshot, args.cycle)
        append_history(
            state,
            {
                "cycle": args.cycle,
                "target": relative,
                "event": "verify-twice",
                "ok": verified,
                "note": note,
                "runs": [result_payload(item) for item in verification],
            },
        )
        if not verified:
            state["active_target"] = relative
            state["success"] = False
            write_json(STATE_PATH, state)
            return 2
        state.setdefault("verified", {})[relative] = {
            "sha256": sha256_file(path),
            "cycle": args.cycle,
            "runs": [result_payload(item) for item in verification],
        }
        state["active_target"] = None
        write_json(STATE_PATH, state)
        print(f"[pass376-v2] {relative}: VERIFIED TWICE")

    final_validations: dict[str, Any] = {}
    for path in paths:
        relative = str(path.relative_to(ROOT))
        valid, reason = validate_against_snapshot(path, baseline[relative])
        entry = state.setdefault("verified", {}).get(relative)
        sha = sha256_file(path)
        final_validations[relative] = {
            "trust": valid,
            "reason": reason,
            "sha256": sha,
            "verified_sha_matches": bool(entry and entry.get("sha256") == sha),
        }
    success = all(
        item["trust"] and item["verified_sha_matches"] for item in final_validations.values()
    )
    state["targets"] = [str(path.relative_to(ROOT)) for path in paths]
    state["final_validations"] = final_validations
    state["success"] = success
    state["completed_cycle"] = args.cycle if success else None
    write_json(STATE_PATH, state)
    if not success:
        return 2
    SUCCESS_MARKER.write_text(
        "Mock2_FunctionalAnalysis, Mock2_FunctionalAnalysis_Integrated, every checked-in "
        "Mock3 bridge, and QYM passed twice in the required order.\n"
        + "\n".join(
            f"{path.relative_to(ROOT)} sha256={sha256_file(path)}" for path in paths
        )
        + "\n",
        encoding="utf-8",
    )
    print("[pass376-v2] SUCCESS: all required FA / Integrated / Mock3 / QYM targets passed twice")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
