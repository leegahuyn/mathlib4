#!/usr/bin/env python3
from __future__ import annotations

import concurrent.futures
import dataclasses
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time
import urllib.error
import urllib.request

ROOT = Path(__file__).resolve().parents[1]
PVS = ROOT / "PrimalitySheafVerification"
BRANCH = "fix/fa406-self-contained-20260809"
EVIDENCE = ROOT / "build-logs" / "fa406-self-contained"
STATE = EVIDENCE / "STATE.json"
FINAL = EVIDENCE / "FINAL_STATUS.json"
MARKER = EVIDENCE / "ALL_REQUIRED_TARGETS_2X_PASS"
CYCLE_FILE = ROOT / ".fa406-cycle"

ERROR_RE = re.compile(r"(?P<file>[^:\n]+\.lean):(?P<line>\d+):(?P<col>\d+):\s+error:")
DECL_RE = re.compile(
    r"^\s*(?:(?:noncomputable|private|protected|public|opaque)\s+)*"
    r"(?:theorem|lemma|corollary|def|abbrev|instance|structure|class|inductive)\b"
)
NAME_RE = re.compile(
    r"^\s*(?:(?:noncomputable|private|protected|public|opaque)\s+)*"
    r"(?:theorem|lemma|corollary|def|abbrev|instance|structure|class|inductive)"
    r"(?:\s+([A-Za-z0-9_'.]+))?"
)

PREFERRED_MODELS = [
    "openai/gpt-5",
    "openai/gpt-5-mini",
    "openai/o3",
    "openai/o4-mini",
    "openai/gpt-4.1",
    "xai/grok-3-mini",
    "deepseek/DeepSeek-V3-0324",
    "mistral-ai/Mistral-Large-2411",
    "qwen/Qwen3-235B-A22B",
]


@dataclasses.dataclass(frozen=True)
class Metric:
    exit_code: int
    errors: int
    first_line: int
    first_col: int
    declaration_ordinal: int
    declaration_name: str
    errors_in_declaration: int
    source_sha256: str
    olean: bool
    ilean: bool
    log: str

    @property
    def passed(self) -> bool:
        return self.exit_code == 0 and self.errors == 0 and self.olean and self.ilean

    def score(self) -> tuple[int, int, int, int, int]:
        if self.passed:
            return (2, 10**9, 0, 10**9, 0)
        return (
            1,
            self.declaration_ordinal,
            -self.errors_in_declaration,
            self.first_line,
            -self.errors,
        )

    def better_than(self, other: "Metric") -> bool:
        return self.score() > other.score()

    def to_json(self) -> dict[str, object]:
        return dataclasses.asdict(self) | {"passed": self.passed, "score": self.score()}


def run(cmd: list[str], *, timeout: int = 1800, cwd: Path = ROOT) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        cmd,
        cwd=cwd,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=timeout,
    )


def sha_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def artifact_paths(path: Path) -> tuple[Path, Path]:
    rel = path.relative_to(ROOT).with_suffix("")
    base = ROOT / ".lake" / "build" / "lib" / "lean" / rel
    return base.with_suffix(".olean"), base.with_suffix(".ilean")


def declaration_starts(source: str) -> list[int]:
    return [i for i, line in enumerate(source.splitlines()) if DECL_RE.match(line)]


def declaration_identity(source: str, line_number: int) -> tuple[int, str, int, int]:
    lines = source.splitlines(keepends=True)
    starts = declaration_starts(source)
    if not starts or line_number <= 0:
        return (-1, "(preamble)", 0, len(lines))
    idx = max(0, min(len(lines) - 1, line_number - 1))
    prior = [s for s in starts if s <= idx]
    if not prior:
        return (-1, "(preamble)", 0, starts[0])
    start = prior[-1]
    ordinal = starts.index(start)
    end = starts[ordinal + 1] if ordinal + 1 < len(starts) else len(lines)
    match = NAME_RE.match(lines[start])
    name = match.group(1) if match and match.group(1) else lines[start].strip()[:120]
    return ordinal, name, start, end


def declaration_headers(source: str) -> list[str]:
    lines = source.splitlines(keepends=True)
    starts = declaration_starts(source)
    headers: list[str] = []
    for ordinal, start in enumerate(starts):
        end = starts[ordinal + 1] if ordinal + 1 < len(starts) else len(lines)
        segment = "".join(lines[start:end])
        pos = find_assignment(segment)
        headers.append(segment[: pos + 2] if pos is not None else lines[start])
    return headers


def find_assignment(segment: str) -> int | None:
    i = 0
    comment_depth = 0
    in_string = False
    escaped = False
    while i + 1 < len(segment):
        if comment_depth:
            if segment.startswith("/-", i):
                comment_depth += 1
                i += 2
                continue
            if segment.startswith("-/", i):
                comment_depth -= 1
                i += 2
                continue
            i += 1
            continue
        if in_string:
            c = segment[i]
            if escaped:
                escaped = False
            elif c == "\\":
                escaped = True
            elif c == '"':
                in_string = False
            i += 1
            continue
        if segment.startswith("/-", i):
            comment_depth = 1
            i += 2
            continue
        if segment.startswith("--", i):
            while i < len(segment) and segment[i] != "\n":
                i += 1
            continue
        if segment[i] == '"':
            in_string = True
            i += 1
            continue
        if segment.startswith(":=", i):
            return i
        i += 1
    return None


def strip_comments_and_strings(text: str) -> str:
    out: list[str] = []
    i = 0
    comment_depth = 0
    in_string = False
    escaped = False
    while i < len(text):
        if comment_depth:
            if text.startswith("/-", i):
                comment_depth += 1
                out.extend("  ")
                i += 2
                continue
            if text.startswith("-/", i):
                comment_depth -= 1
                out.extend("  ")
                i += 2
                continue
            out.append("\n" if text[i] == "\n" else " ")
            i += 1
            continue
        if in_string:
            c = text[i]
            out.append("\n" if c == "\n" else " ")
            if escaped:
                escaped = False
            elif c == "\\":
                escaped = True
            elif c == '"':
                in_string = False
            i += 1
            continue
        if text.startswith("/-", i):
            comment_depth = 1
            out.extend("  ")
            i += 2
            continue
        if text.startswith("--", i):
            while i < len(text) and text[i] != "\n":
                out.append(" ")
                i += 1
            continue
        if text[i] == '"':
            in_string = True
            out.append(" ")
            i += 1
            continue
        out.append(text[i])
        i += 1
    return "".join(out)


def forbidden_counts(source: str) -> dict[str, int]:
    code = strip_comments_and_strings(source)
    patterns = {
        "sorry": r"\bsorry\b",
        "admit": r"\badmit\b",
        "global_axiom": r"(?m)^\s*(?:public\s+)?axiom\b",
        "unsafe": r"(?m)^\s*unsafe\b",
        "native_decide": r"\bnative_decide\b",
        "Lean.ofReduceBool": r"\bLean\.ofReduceBool\b",
    }
    return {name: len(re.findall(pattern, code)) for name, pattern in patterns.items()}


def compile_file(path: Path, log_path: Path, *, max_errors: int = 220) -> Metric:
    EVIDENCE.mkdir(parents=True, exist_ok=True)
    log_path.parent.mkdir(parents=True, exist_ok=True)
    source = path.read_text(encoding="utf-8")
    olean, ilean = artifact_paths(path)
    olean.parent.mkdir(parents=True, exist_ok=True)
    for artifact in (olean, ilean):
        try:
            artifact.unlink()
        except FileNotFoundError:
            pass
    cmd = [
        "lake", "env", "lean",
        f"-DmaxErrors={max_errors}",
        "-DwarningAsError=false",
        f"-o={olean}",
        f"-i={ilean}",
        str(path.relative_to(ROOT)),
    ]
    started = time.time()
    try:
        proc = run(cmd, timeout=2100)
        output = proc.stdout
        exit_code = proc.returncode
    except subprocess.TimeoutExpired as exc:
        output = (exc.stdout or "") + "\nTIMEOUT\n"
        exit_code = 124
    log_path.write_text(output, encoding="utf-8", errors="replace")
    matches = list(ERROR_RE.finditer(output))
    errors = len(matches)
    first_line = int(matches[0].group("line")) if matches else 0
    first_col = int(matches[0].group("col")) if matches else 0
    ordinal, name, start, end = declaration_identity(source, first_line)
    error_lines = [int(m.group("line")) for m in matches]
    errors_in_declaration = sum(start + 1 <= line <= end for line in error_lines)
    if exit_code != 0 and errors == 0:
        errors = max_errors + 1
    metric = Metric(
        exit_code=exit_code,
        errors=errors,
        first_line=first_line,
        first_col=first_col,
        declaration_ordinal=ordinal,
        declaration_name=name,
        errors_in_declaration=errors_in_declaration,
        source_sha256=sha_text(source),
        olean=olean.exists(),
        ilean=ilean.exists(),
        log=str(log_path.relative_to(ROOT)),
    )
    elapsed = time.time() - started
    with log_path.open("a", encoding="utf-8") as handle:
        handle.write(f"\nFA406_METRIC={json.dumps(metric.to_json(), sort_keys=True)}\n")
        handle.write(f"FA406_ELAPSED_SECONDS={elapsed:.3f}\n")
    return metric


def error_context(log_text: str, first_line: int, limit: int = 18000) -> str:
    lines = log_text.splitlines()
    selected: list[str] = []
    for i, line in enumerate(lines):
        match = ERROR_RE.search(line)
        if match and abs(int(match.group("line")) - first_line) <= 40:
            selected.extend(lines[max(0, i - 2): min(len(lines), i + 10)])
        if sum(len(x) + 1 for x in selected) >= limit:
            break
    if not selected:
        selected = lines[-220:]
    return "\n".join(selected)[-limit:]


def exact_api_search(segment: str, errors: str, limit: int = 22000) -> str:
    identifiers = re.findall(r"\b[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)+\b", errors + "\n" + segment)
    identifiers += re.findall(r"unknown (?:constant|identifier|field) ['`]?([A-Za-z0-9_.']+)", errors)
    seen: set[str] = set()
    output: list[str] = []
    for identifier in identifiers:
        if identifier in seen or len(identifier) < 4:
            continue
        seen.add(identifier)
        tail = identifier.split(".")[-1]
        pattern = rf"\b{re.escape(tail)}\b"
        try:
            proc = run(
                ["rg", "-n", "--glob", "*.lean", "-m", "8", pattern, "Mathlib", "PrimalitySheafVerification"],
                timeout=25,
            )
        except Exception:
            continue
        if proc.stdout.strip():
            output.append(f"### {identifier}\n{proc.stdout[:3500]}")
        if sum(len(x) for x in output) >= limit:
            break
    return "\n\n".join(output)[:limit] or "(no exact API hits)"


def catalog_models(token: str) -> list[str]:
    request = urllib.request.Request(
        "https://models.github.ai/catalog/models",
        headers={
            "Authorization": f"Bearer {token}",
            "Accept": "application/vnd.github+json",
            "X-GitHub-Api-Version": "2022-11-28",
        },
    )
    available: list[str] = []
    try:
        with urllib.request.urlopen(request, timeout=90) as response:
            payload = json.loads(response.read().decode("utf-8"))
        entries = payload if isinstance(payload, list) else payload.get("models", [])
        for entry in entries:
            if isinstance(entry, dict):
                model = entry.get("id") or entry.get("name")
                if model:
                    available.append(str(model))
    except Exception:
        pass
    ordered = [model for model in PREFERRED_MODELS if model in available]
    ordered.extend(model for model in available if model not in ordered)
    return ordered or list(PREFERRED_MODELS)


def model_request(model: str, prompt: str, token: str, seed: int) -> str:
    payload = {
        "model": model,
        "messages": [
            {"role": "system", "content": "You are an expert Lean 4 and current Mathlib proof repairer. Return only the requested tagged replacement body."},
            {"role": "user", "content": prompt},
        ],
        "temperature": 0.15,
        "max_tokens": 7000,
        "seed": seed,
    }
    request = urllib.request.Request(
        "https://models.github.ai/inference/chat/completions",
        data=json.dumps(payload).encode("utf-8"),
        method="POST",
        headers={
            "Authorization": f"Bearer {token}",
            "Accept": "application/vnd.github+json",
            "Content-Type": "application/json",
            "X-GitHub-Api-Version": "2022-11-28",
        },
    )
    with urllib.request.urlopen(request, timeout=240) as response:
        data = json.loads(response.read().decode("utf-8"))
    content = data["choices"][0]["message"]["content"]
    if isinstance(content, list):
        return "\n".join(str(item.get("text", item)) if isinstance(item, dict) else str(item) for item in content)
    return str(content)


def extract_body(content: str) -> str | None:
    match = re.search(r"<BODY>\s*(.*?)\s*</BODY>", content, re.DOTALL)
    if not match:
        return None
    body = match.group(1).strip("\n")
    body = re.sub(r"^```(?:lean)?\s*\n", "", body)
    body = re.sub(r"\n```\s*$", "", body)
    if body.startswith(":="):
        body = body[2:].lstrip()
    return body + ("\n" if body and not body.endswith("\n") else "")


def declaration_bounds(source: str, first_line: int) -> tuple[int, int, str, str, int]:
    lines = source.splitlines(keepends=True)
    ordinal, name, start_line, end_line = declaration_identity(source, first_line)
    if ordinal < 0:
        raise RuntimeError("first error is outside a repairable top-level declaration")
    start_char = sum(len(line) for line in lines[:start_line])
    end_char = sum(len(line) for line in lines[:end_line])
    segment = source[start_char:end_char]
    assignment = find_assignment(segment)
    if assignment is None:
        raise RuntimeError(f"declaration {name} has no := body")
    return start_char, end_char, name, segment, assignment


def make_prompt(path: Path, metric: Metric, source: str, log_text: str, round_index: int) -> tuple[str, tuple[int, int, str, str, int]]:
    bounds = declaration_bounds(source, metric.first_line)
    start, end, name, segment, assignment = bounds
    lines = source.splitlines()
    lo = max(0, metric.first_line - 130)
    hi = min(len(lines), metric.first_line + 130)
    nearby = "\n".join(f"{i + 1}: {lines[i]}" for i in range(lo, hi))
    errors = error_context(log_text, metric.first_line)
    api = exact_api_search(segment, errors)
    immutable = segment[: assignment + 2]
    old_body = segment[assignment + 2:]
    prompt = f"""Repair only the body of the earliest failing Lean declaration.

Lean toolchain: Lean 4.33.0-rc1 with the repository's pinned Mathlib.
File: {path.relative_to(ROOT)}
Round: {round_index}
Declaration: {name}
Current compiler metric:
{json.dumps(metric.to_json(), indent=2)}

The declaration header and assignment prefix are immutable. Your response replaces only
the text after `:=` and before the next top-level declaration.

<IMMUTABLE_PREFIX>
{immutable}
</IMMUTABLE_PREFIX>

<CURRENT_BODY>
{old_body}
</CURRENT_BODY>

<COMPILER_ERRORS>
{errors}
</COMPILER_ERRORS>

<NEARBY_SOURCE>
{nearby}
</NEARBY_SOURCE>

<EXACT_API_SEARCH>
{api}
</EXACT_API_SEARCH>

Return exactly:
<BODY>
replacement text immediately after the immutable `:=`
</BODY>

Hard constraints:
- Do not repeat or alter the declaration header, name, binders, assumptions, or conclusion.
- Fix the first root API/typeclass/dependent-transport error, not later cascades.
- Use only existing current Mathlib/project declarations and local proof terms.
- Local `have`, `let`, `letI`, `change`, `show`, `calc`, `ext`, and `simpa only` are allowed.
- No sorry, admit, new axiom, unsafe, native_decide, Lean.ofReduceBool, theorem weakening, or hidden assumptions.
- Return tags only; no markdown or explanation outside the tags.
"""
    return prompt, bounds


def commit_progress(path: Path, metric: Metric, round_index: int) -> None:
    STATE.parent.mkdir(parents=True, exist_ok=True)
    STATE.write_text(
        json.dumps({
            "stage": path.name,
            "round": round_index,
            "metric": metric.to_json(),
            "updated_at": time.time(),
        }, indent=2),
        encoding="utf-8",
    )
    run(["git", "add", str(path.relative_to(ROOT)), str(STATE.relative_to(ROOT))], timeout=120)
    diff = run(["git", "diff", "--cached", "--quiet"], timeout=120)
    if diff.returncode == 0:
        return
    message = f"fix: advance PASS 406 {path.stem} round {round_index} [skip ci]"
    commit = run(["git", "commit", "-m", message], timeout=180)
    if commit.returncode != 0:
        raise RuntimeError(commit.stdout)
    push = run(["git", "push", "origin", f"HEAD:{BRANCH}"], timeout=300)
    if push.returncode != 0:
        raise RuntimeError(push.stdout)


def repair_target(path: Path, token: str, models: list[str], *, rounds: int, cycle: int) -> Metric:
    target_dir = EVIDENCE / path.stem
    target_dir.mkdir(parents=True, exist_ok=True)
    source = path.read_text(encoding="utf-8")
    baseline_headers = declaration_headers(source)
    bad = forbidden_counts(source)
    if any(bad.values()):
        raise RuntimeError(f"forbidden proof escape in checked-in source: {bad}")
    metric = compile_file(path, target_dir / "round-000-baseline.log")
    if metric.passed:
        return metric
    no_progress = 0
    for round_index in range(1, rounds + 1):
        source = path.read_text(encoding="utf-8")
        log_path = ROOT / metric.log
        log_text = log_path.read_text(encoding="utf-8", errors="replace") if log_path.exists() else ""
        try:
            prompt, (start, end, name, segment, assignment) = make_prompt(path, metric, source, log_text, round_index)
        except Exception as exc:
            (target_dir / f"round-{round_index:03d}-unrepairable.txt").write_text(repr(exc), encoding="utf-8")
            break
        (target_dir / f"round-{round_index:03d}-prompt.txt").write_text(prompt, encoding="utf-8")
        rotated = models[(cycle + round_index) % len(models):] + models[:(cycle + round_index) % len(models)]
        selected_models = rotated[: min(6, len(rotated))]
        jobs = [(model, seed) for model in selected_models for seed in (0, 1)]
        responses: list[tuple[str, int, str]] = []
        with concurrent.futures.ThreadPoolExecutor(max_workers=min(8, len(jobs))) as pool:
            futures = {pool.submit(model_request, model, prompt, token, seed): (model, seed) for model, seed in jobs}
            for future in concurrent.futures.as_completed(futures):
                model, seed = futures[future]
                try:
                    content = future.result()
                except Exception as exc:
                    content = f"<ERROR>{type(exc).__name__}: {exc}</ERROR>"
                responses.append((model, seed, content))
        immutable = segment[: assignment + 2]
        candidates: list[tuple[str, str]] = []
        seen: set[str] = set()
        for model, seed, content in responses:
            safe_model = re.sub(r"[^A-Za-z0-9_.-]+", "_", model)
            (target_dir / f"round-{round_index:03d}-response-{safe_model}-{seed}.txt").write_text(content, encoding="utf-8")
            body = extract_body(content)
            if body is None:
                continue
            replacement = immutable + (" " if body and not body.startswith((" ", "\n")) else "") + body
            candidate = source[:start] + replacement + source[end:]
            digest = sha_text(candidate)
            if digest in seen or candidate == source:
                continue
            seen.add(digest)
            candidates.append((f"{safe_model}-{seed}-{digest[:10]}", candidate))
        candidates.sort(key=lambda item: abs(len(item[1]) - len(source)))
        candidates = candidates[:8]
        diagnostics: list[dict[str, object]] = []
        best_metric: Metric | None = None
        best_source: str | None = None
        original = source
        for index, (label, candidate) in enumerate(candidates):
            if declaration_headers(candidate) != baseline_headers:
                diagnostics.append({"label": label, "rejected": "declaration headers changed"})
                continue
            candidate_bad = forbidden_counts(candidate)
            if any(candidate_bad.values()):
                diagnostics.append({"label": label, "rejected": f"forbidden {candidate_bad}"})
                continue
            path.write_text(candidate, encoding="utf-8")
            try:
                candidate_metric = compile_file(path, target_dir / f"round-{round_index:03d}-candidate-{index:02d}.log")
            finally:
                path.write_text(original, encoding="utf-8")
            diagnostics.append({"label": label, "metric": candidate_metric.to_json()})
            if candidate_metric.better_than(metric) and (best_metric is None or candidate_metric.better_than(best_metric)):
                best_metric = candidate_metric
                best_source = candidate
        (target_dir / f"round-{round_index:03d}-candidates.json").write_text(json.dumps(diagnostics, indent=2), encoding="utf-8")
        if best_metric is None or best_source is None:
            no_progress += 1
            if no_progress >= 4:
                break
            continue
        no_progress = 0
        path.write_text(best_source, encoding="utf-8")
        confirmed = compile_file(path, target_dir / f"round-{round_index:03d}-accepted.log")
        if not confirmed.better_than(metric) and not confirmed.passed:
            path.write_text(original, encoding="utf-8")
            continue
        metric = confirmed
        commit_progress(path, metric, round_index)
        if metric.passed:
            return metric
    return metric


def verify_twice(path: Path, label: str) -> list[Metric]:
    results: list[Metric] = []
    for run_index in (1, 2):
        metric = compile_file(path, EVIDENCE / "final-verification" / f"{label}-run-{run_index}.log", max_errors=500)
        results.append(metric)
        if not metric.passed:
            break
    return results


def ensure_prerequisites() -> list[dict[str, object]]:
    results: list[dict[str, object]] = []
    for name in ("Mock2.lean", "Mock2_Advanced.lean"):
        path = PVS / name
        metric = compile_file(path, EVIDENCE / "prerequisites" / f"{path.stem}.log", max_errors=300)
        results.append({"module": name, "metric": metric.to_json()})
        if not metric.passed:
            raise RuntimeError(f"verified prerequisite {name} no longer compiles: {metric.to_json()}")
    return results


def main() -> int:
    token = os.environ.get("GITHUB_TOKEN", "")
    if not token:
        raise SystemExit("GITHUB_TOKEN is required")
    EVIDENCE.mkdir(parents=True, exist_ok=True)
    cycle = int(CYCLE_FILE.read_text().strip()) if CYCLE_FILE.exists() else 0
    models = catalog_models(token)
    state: dict[str, object] = {
        "cycle": cycle,
        "branch": BRANCH,
        "models": models,
        "started_at": time.time(),
        "prerequisites": [],
        "modules": [],
    }
    STATE.write_text(json.dumps(state, indent=2), encoding="utf-8")
    try:
        state["prerequisites"] = ensure_prerequisites()
        targets: list[Path] = [PVS / "Mock2_FunctionalAnalysis.lean"]
        targets.append(PVS / "Mock2_FunctionalAnalysis_Integrated.lean")
        targets.extend(sorted(PVS.glob("Mock3*.lean")))
        targets.append(PVS / "QYM.lean")
        for path in targets:
            if not path.exists():
                if path.name.startswith("Mock3"):
                    continue
                raise RuntimeError(f"required target missing: {path}")
            metric = repair_target(path, token, models, rounds=30, cycle=cycle)
            module_record: dict[str, object] = {"module": path.name, "repair_metric": metric.to_json()}
            if not metric.passed:
                state["stage"] = path.name
                state["complete"] = False
                state["modules"].append(module_record)
                STATE.write_text(json.dumps(state, indent=2), encoding="utf-8")
                FINAL.write_text(json.dumps(state, indent=2), encoding="utf-8")
                return 1
            twice = verify_twice(path, path.stem)
            module_record["verification"] = [item.to_json() for item in twice]
            module_record["status"] = "PASS_2X" if len(twice) == 2 and all(item.passed for item in twice) else "FAIL"
            state["modules"].append(module_record)
            STATE.write_text(json.dumps(state, indent=2), encoding="utf-8")
            if module_record["status"] != "PASS_2X":
                state["stage"] = path.name
                state["complete"] = False
                FINAL.write_text(json.dumps(state, indent=2), encoding="utf-8")
                return 1
        state["complete"] = True
        state["status"] = "SUCCESS_ALL_REQUIRED_TARGETS_2X_PASS"
        state["finished_at"] = time.time()
        FINAL.write_text(json.dumps(state, indent=2), encoding="utf-8")
        MARKER.write_text("SUCCESS_ALL_REQUIRED_TARGETS_2X_PASS\n", encoding="utf-8")
        run(["git", "add", str(FINAL.relative_to(ROOT)), str(MARKER.relative_to(ROOT))], timeout=120)
        if run(["git", "diff", "--cached", "--quiet"], timeout=120).returncode != 0:
            run(["git", "commit", "-m", "fix: obtain PASS 406 FA Integrated Mock3 QYM 2x PASS [skip ci]"], timeout=180)
            push = run(["git", "push", "origin", f"HEAD:{BRANCH}"], timeout=300)
            if push.returncode != 0:
                raise RuntimeError(push.stdout)
        return 0
    except Exception as exc:
        state["complete"] = False
        state["exception"] = f"{type(exc).__name__}: {exc}"
        state["finished_at"] = time.time()
        STATE.write_text(json.dumps(state, indent=2), encoding="utf-8")
        FINAL.write_text(json.dumps(state, indent=2), encoding="utf-8")
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
