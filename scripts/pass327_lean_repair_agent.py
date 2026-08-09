from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import textwrap
import time
from typing import Any
from urllib import error, request

ROOT = Path(__file__).resolve().parents[1]
TARGET_DIR = ROOT / "PrimalitySheafVerification"
OUTDIR = ROOT / ".lake" / "build" / "lib" / "lean" / "PrimalitySheafVerification"
EVIDENCE = Path("/tmp/pass327-repair-agent")
STATE_PATH = ROOT / "build-logs" / "pass327-agent-state.json"
SUCCESS_PATH = ROOT / "build-logs" / "pass327-targets-pass.json"

FORBIDDEN_CODE_PATTERNS = {
    "sorry": re.compile(r"\bsorry\b"),
    "admit": re.compile(r"\badmit\b"),
    "global_axiom": re.compile(r"(?m)^\s*axiom\b"),
    "unsafe": re.compile(r"\bunsafe\b"),
    "native_decide": re.compile(r"\bnative_decide\b"),
    "Lean.ofReduceBool": re.compile(r"\bLean\.ofReduceBool\b"),
}

DIAG_RE = re.compile(
    r"(?m)^(PrimalitySheafVerification/[^:\n]+\.lean):(\d+):(\d+): "
    r"(error(?:\([^\n)]*\))?):\s*(.*)$"
)

MODELS = [
    ("https://models.github.ai/inference/chat/completions", "openai/gpt-4.1"),
    ("https://models.github.ai/inference/chat/completions", "openai/gpt-4o"),
    ("https://models.github.ai/inference/chat/completions", "openai/gpt-4.1-mini"),
    ("https://models.inference.ai.azure.com/chat/completions", "gpt-4o"),
]


def run(
    args: list[str],
    *,
    cwd: Path = ROOT,
    timeout: int | None = None,
    check: bool = False,
    input_text: str | None = None,
) -> subprocess.CompletedProcess[str]:
    proc = subprocess.run(
        args,
        cwd=cwd,
        text=True,
        input=input_text,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=timeout,
    )
    if check and proc.returncode != 0:
        raise RuntimeError(f"command failed ({proc.returncode}): {' '.join(args)}\n{proc.stdout}")
    return proc


def sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def strip_comments_and_strings(source: str) -> str:
    output: list[str] = []
    index = 0
    depth = 0
    in_string = False
    escaped = False
    while index < len(source):
        if depth:
            if source.startswith("/-", index):
                depth += 1
                output.extend("  ")
                index += 2
            elif source.startswith("-/", index):
                depth -= 1
                output.extend("  ")
                index += 2
            else:
                output.append("\n" if source[index] == "\n" else " ")
                index += 1
        elif in_string:
            character = source[index]
            output.append("\n" if character == "\n" else " ")
            if escaped:
                escaped = False
            elif character == "\\":
                escaped = True
            elif character == '"':
                in_string = False
            index += 1
        elif source.startswith("/-", index):
            depth = 1
            output.extend("  ")
            index += 2
        elif source.startswith("--", index):
            while index < len(source) and source[index] != "\n":
                output.append(" ")
                index += 1
        elif source[index] == '"':
            in_string = True
            output.append(" ")
            index += 1
        else:
            output.append(source[index])
            index += 1
    if depth or in_string:
        raise RuntimeError("unterminated comment or string")
    return "".join(output)


def audit_source(path: Path) -> dict[str, int]:
    source = path.read_text(encoding="utf-8")
    code = strip_comments_and_strings(source)
    counts = {name: len(pattern.findall(code)) for name, pattern in FORBIDDEN_CODE_PATTERNS.items()}
    if any(counts.values()):
        raise RuntimeError(f"forbidden executable token in {path}: {counts}")
    return counts


def declaration_headers(source: str) -> list[str]:
    """Conservative textual fingerprint for proof declaration statements.

    It intentionally tracks theorem/lemma/corollary headers only.  Proof-body
    changes are allowed, but an existing public mathematical statement may not
    be silently edited by the repair agent.
    """
    lines = source.splitlines()
    result: list[str] = []
    start_re = re.compile(
        r"^\s*(?:(?:private|protected|nonrec)\s+)*(theorem|lemma|corollary)\b"
    )
    index = 0
    while index < len(lines):
        if not start_re.match(lines[index]):
            index += 1
            continue
        collected: list[str] = []
        paren = bracket = brace = 0
        while index < len(lines):
            line = lines[index]
            collected.append(line)
            code = strip_comments_and_strings(line)
            paren += code.count("(") - code.count(")")
            bracket += code.count("[") - code.count("]")
            brace += code.count("{") - code.count("}")
            # A declaration header ends at its top-level proof introducer.
            marker = None
            if paren <= 0 and bracket <= 0 and brace <= 0:
                for candidate in (":=", " where"):
                    position = code.find(candidate)
                    if position >= 0:
                        marker = candidate
                        break
            if marker is not None:
                joined = "\n".join(collected)
                position = joined.find(marker)
                header = joined[:position]
                result.append(re.sub(r"\s+", " ", header).strip())
                index += 1
                break
            index += 1
        else:
            break
    return result


def compile_module(path: Path, label: str) -> dict[str, Any]:
    OUTDIR.mkdir(parents=True, exist_ok=True)
    (EVIDENCE / "logs").mkdir(parents=True, exist_ok=True)
    module = path.stem
    for suffix in (".olean", ".ilean", ".olean.private"):
        candidate = OUTDIR / f"{module}{suffix}"
        if candidate.exists():
            candidate.unlink()
    log_path = EVIDENCE / "logs" / f"{label}.log"
    command = [
        "lake",
        "env",
        "lean",
        "-DmaxErrors=2000",
        str(path.relative_to(ROOT)),
        "-o",
        str(OUTDIR / f"{module}.olean"),
        "-i",
        str(OUTDIR / f"{module}.ilean"),
    ]
    started = time.time()
    proc = run(command, timeout=1800)
    elapsed = round(time.time() - started, 3)
    log_path.write_text(proc.stdout, encoding="utf-8")
    diagnostics = parse_diagnostics(proc.stdout)
    warnings = len(re.findall(r"(?m)^.*:\d+:\d+: warning:", proc.stdout))
    maximum_errors = "maximum number of errors" in proc.stdout
    missing_object = "object file" in proc.stdout and "does not exist" in proc.stdout
    olean = OUTDIR / f"{module}.olean"
    ilean = OUTDIR / f"{module}.ilean"
    passed = (
        proc.returncode == 0
        and not diagnostics
        and not maximum_errors
        and not missing_object
        and olean.is_file()
        and olean.stat().st_size > 0
        and ilean.is_file()
        and ilean.stat().st_size > 0
        and "declaration uses 'sorry'" not in proc.stdout
        and "sorryAx" not in proc.stdout
    )
    result = {
        "path": str(path.relative_to(ROOT)),
        "label": label,
        "exit_code": proc.returncode,
        "error_count": len(diagnostics),
        "warning_count": warnings,
        "first_error_line": diagnostics[0][1] if diagnostics else None,
        "last_error_line": diagnostics[-1][1] if diagnostics else None,
        "maximum_errors": maximum_errors,
        "missing_object": missing_object,
        "passed": passed,
        "elapsed_seconds": elapsed,
        "source_sha256": sha256_text(path.read_text(encoding="utf-8")),
        "log": str(log_path),
    }
    with (EVIDENCE / "compile-results.jsonl").open("a", encoding="utf-8") as handle:
        handle.write(json.dumps(result, ensure_ascii=False) + "\n")
    return result


def parse_diagnostics(log: str) -> list[tuple[str, int, int, str, str]]:
    return [
        (match.group(1), int(match.group(2)), int(match.group(3)), match.group(4), match.group(5))
        for match in DIAG_RE.finditer(log)
    ]


def diagnostic_blocks(log: str, limit: int = 14) -> list[str]:
    matches = list(DIAG_RE.finditer(log))
    blocks: list[str] = []
    for index, match in enumerate(matches[:limit]):
        end = matches[index + 1].start() if index + 1 < len(matches) else len(log)
        block = log[match.start():end].strip()
        blocks.append(block[:7000])
    return blocks


def source_context(path: Path, diagnostics: list[tuple[str, int, int, str, str]]) -> str:
    lines = path.read_text(encoding="utf-8").splitlines()
    pieces: list[str] = []
    seen: set[int] = set()
    for _, line, _, _, _ in diagnostics[:14]:
        if line in seen:
            continue
        seen.add(line)
        start = max(1, line - 28)
        end = min(len(lines), line + 42)
        context = "\n".join(f"{number}: {lines[number - 1]}" for number in range(start, end + 1))
        pieces.append(f"SOURCE LINES {start}-{end} AROUND ERROR {line}\n{context}")
    return "\n\n---\n\n".join(pieces)


def namespace_context(path: Path, diagnostics: list[tuple[str, int, int, str, str]]) -> str:
    lines = path.read_text(encoding="utf-8").splitlines()
    interesting = re.compile(
        r"^\s*(?:namespace|end|open|variable|section|noncomputable section|universe)\b"
    )
    output: list[str] = []
    for _, line, _, _, _ in diagnostics[:8]:
        preceding = [
            f"{idx}: {lines[idx - 1]}"
            for idx in range(max(1, line - 500), line)
            if interesting.match(lines[idx - 1])
        ][-35:]
        output.append(f"NAMESPACE/INSTANCE CONTEXT BEFORE {line}\n" + "\n".join(preceding))
    return "\n\n".join(output)


def api_search_context(log: str, target: Path) -> str:
    identifiers: list[str] = []
    patterns = [
        r"Unknown identifier `([^`]+)`",
        r"Unknown constant `([^`]+)`",
        r"unknown namespace `([^`]+)`",
        r"Invalid field `([^`]+)`",
        r"Did not find an occurrence of the pattern\s+([^\n]+)",
    ]
    for pattern in patterns:
        for value in re.findall(pattern, log):
            value = value.strip()
            if 2 <= len(value) <= 140 and value not in identifiers:
                identifiers.append(value)
    output: list[str] = []
    for identifier in identifiers[:18]:
        atomic = identifier.split(".")[-1].split()[0].strip("`'(){}[]")
        if len(atomic) < 3:
            continue
        proc = run(
            [
                "bash",
                "-lc",
                "rg -n --fixed-strings --glob '*.lean' -- "
                + subprocess.list2cmdline([atomic])
                + " Mathlib PrimalitySheafVerification | head -40",
            ],
            timeout=25,
        )
        if proc.stdout.strip():
            output.append(f"SEARCH RESULTS FOR {atomic}\n{proc.stdout[:12000]}")
    return "\n\n".join(output)


def build_prompt(path: Path, compile_result: dict[str, Any]) -> str:
    log = Path(compile_result["log"]).read_text(encoding="utf-8", errors="replace")
    diagnostics = parse_diagnostics(log)
    blocks = diagnostic_blocks(log)
    context = source_context(path, diagnostics)
    namespace = namespace_context(path, diagnostics)
    search = api_search_context("\n".join(blocks), path)
    imports = "\n".join(path.read_text(encoding="utf-8").splitlines()[:260])
    return textwrap.dedent(
        f"""
        You are repairing a Lean 4.33.0-rc1 file against the checked-out Mathlib API.
        The baseline is the user's PASS 327 candidate.  Make a real kernel-checked
        repair; do not merely silence diagnostics.

        TARGET FILE: {path.relative_to(ROOT)}
        CURRENT RESULT: exit={compile_result['exit_code']}, errors={compile_result['error_count']},
        first_error_line={compile_result['first_error_line']}, last_error_line={compile_result['last_error_line']}.

        NON-NEGOTIABLE RULES:
        - Return only one unified git diff in a ```diff fenced block.
        - Modify only {path.relative_to(ROOT)}.
        - Do not change any existing theorem, lemma, or corollary statement,
          conclusion, binder, hypothesis, or assumption.
        - Do not add `sorry`, `admit`, any global `axiom`, `unsafe`,
          `native_decide`, `Lean.ofReduceBool`, or opaque proof escapes.
        - Do not delete audits or lower maxErrors.  Do not comment out code.
        - Prefer qualified current Mathlib names, explicit type annotations,
          local `letI`, extensionality, `change`, `simpa`, and small helper lemmas.
        - Fix the common cause of cascades rather than hard-coding dozens of goals.
        - It is acceptable to add local helper lemmas/instances and to mark a
          genuinely noncomputable definition `noncomputable`.
        - Keep public names and interfaces intact.
        - Address as many of the supplied earliest independent diagnostics as can
          be fixed coherently in one patch, but keep the diff below 500 changed lines.

        FILE IMPORT/OPEN PREFIX:
        {imports}

        EARLIEST LEAN DIAGNOSTICS:
        {'\n\n===== NEXT DIAGNOSTIC =====\n\n'.join(blocks)}

        RELEVANT SOURCE CONTEXT:
        {context}

        NAMESPACE/SECTION CONTEXT:
        {namespace}

        LOCAL MATHLIB/PROJECT API SEARCH RESULTS:
        {search}
        """
    )[:118000]


def call_model(prompt: str, call_index: int) -> tuple[str, str]:
    token = os.environ.get("GITHUB_TOKEN") or os.environ.get("GH_TOKEN")
    if not token:
        raise RuntimeError("GITHUB_TOKEN/GH_TOKEN is required for GitHub Models")
    errors: list[str] = []
    for endpoint, model in MODELS:
        payload = {
            "model": model,
            "messages": [
                {
                    "role": "system",
                    "content": (
                        "You are a meticulous Lean 4 and Mathlib proof engineer. "
                        "Obey the trust constraints exactly and emit a minimal unified diff."
                    ),
                },
                {"role": "user", "content": prompt},
            ],
            "temperature": 0.1,
            "max_tokens": 12000,
        }
        req = request.Request(
            endpoint,
            data=json.dumps(payload).encode("utf-8"),
            headers={
                "Authorization": f"Bearer {token}",
                "Content-Type": "application/json",
                "Accept": "application/json",
                "User-Agent": "pass327-lean-repair-agent",
            },
            method="POST",
        )
        try:
            with request.urlopen(req, timeout=240) as response:
                raw = response.read().decode("utf-8", errors="replace")
            data = json.loads(raw)
            content = data["choices"][0]["message"]["content"]
            (EVIDENCE / "model").mkdir(parents=True, exist_ok=True)
            (EVIDENCE / "model" / f"call-{call_index:03d}-{model.replace('/', '_')}.txt").write_text(
                content, encoding="utf-8"
            )
            return content, model
        except (error.HTTPError, error.URLError, TimeoutError, KeyError, json.JSONDecodeError) as exc:
            detail = str(exc)
            if isinstance(exc, error.HTTPError):
                try:
                    detail += " " + exc.read().decode("utf-8", errors="replace")[:4000]
                except Exception:
                    pass
            errors.append(f"{endpoint} {model}: {detail}")
            time.sleep(4)
    raise RuntimeError("all GitHub Models calls failed:\n" + "\n".join(errors))


def extract_diff(content: str) -> str:
    fenced = re.search(r"```diff\s*(.*?)```", content, flags=re.S)
    if fenced:
        return fenced.group(1).strip() + "\n"
    start = content.find("diff --git ")
    if start >= 0:
        return content[start:].strip() + "\n"
    raise RuntimeError("model response did not contain a unified diff")


def validate_diff(diff: str, path: Path, before_source: str) -> None:
    relative = str(path.relative_to(ROOT))
    if len(diff) > 180000:
        raise RuntimeError("diff is unreasonably large")
    headers = re.findall(r"^diff --git a/(.+?) b/(.+?)$", diff, flags=re.M)
    if not headers or any(left != relative or right != relative for left, right in headers):
        raise RuntimeError(f"diff may modify only {relative}; headers={headers}")
    changed = 0
    for line in diff.splitlines():
        if not line or line.startswith(("+++", "---", "@@", "diff --git", "index ")):
            continue
        if line[0] not in "+-":
            continue
        changed += 1
        body = line[1:]
        if re.match(r"^\s*(?:(?:private|protected|nonrec)\s+)*(theorem|lemma|corollary)\b", body):
            raise RuntimeError("repair attempted to edit a theorem/lemma/corollary header")
        if re.match(r"^\s*import\b", body):
            raise RuntimeError("repair attempted to alter imports")
        if line.startswith("+"):
            if re.search(
                r"\b(sorry|admit|axiom|unsafe|native_decide|Lean\.ofReduceBool)\b",
                body,
            ):
                raise RuntimeError("repair attempted to add a forbidden proof escape")
            if "set_option maxErrors" in body:
                raise RuntimeError("repair attempted to lower or hide the error frontier")
        if "#print axioms" in body:
            raise RuntimeError("repair attempted to alter an axiom audit command")
    if changed > 1000:
        raise RuntimeError(f"diff changes too many lines: {changed}")


def apply_diff(diff: str, path: Path) -> str:
    before = path.read_text(encoding="utf-8")
    before_headers = declaration_headers(before)
    patch_path = EVIDENCE / "candidate.patch"
    patch_path.write_text(diff, encoding="utf-8")
    check = run(["git", "apply", "--check", "--whitespace=error-all", str(patch_path)])
    if check.returncode != 0:
        raise RuntimeError("git apply --check failed:\n" + check.stdout)
    applied = run(["git", "apply", "--whitespace=fix", str(patch_path)])
    if applied.returncode != 0:
        raise RuntimeError("git apply failed:\n" + applied.stdout)
    after = path.read_text(encoding="utf-8")
    after_headers = declaration_headers(after)
    if before_headers != after_headers:
        path.write_text(before, encoding="utf-8")
        raise RuntimeError("theorem/lemma/corollary statement fingerprint changed")
    audit_source(path)
    return before


def improvement(before: dict[str, Any], after: dict[str, Any]) -> tuple[bool, str]:
    if after["passed"]:
        return True, "module passed"
    b_count = int(before["error_count"])
    a_count = int(after["error_count"])
    b_line = before["first_error_line"] or 0
    a_line = after["first_error_line"] or 0
    if a_count < b_count:
        return True, f"error count decreased {b_count}->{a_count}"
    if a_line > b_line:
        return True, f"first error advanced {b_line}->{a_line}"
    return False, f"no measured progress: errors {b_count}->{a_count}, first line {b_line}->{a_line}"


def load_state() -> dict[str, Any]:
    if STATE_PATH.exists():
        return json.loads(STATE_PATH.read_text(encoding="utf-8"))
    return {
        "baseline": "PASS 327 run 31159696948 job 92827136991",
        "phase": "Mock2_FunctionalAnalysis",
        "round": 0,
        "model_calls": 0,
        "accepted_patches": 0,
        "rejected_patches": 0,
        "started_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "history": [],
    }


def save_state(state: dict[str, Any]) -> None:
    STATE_PATH.parent.mkdir(parents=True, exist_ok=True)
    state["updated_utc"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    STATE_PATH.write_text(json.dumps(state, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def local_commit(message: str, paths: list[Path]) -> None:
    relative = [str(path.relative_to(ROOT)) for path in paths if path.exists()]
    run(["git", "add", "--", *relative], check=True)
    if run(["git", "diff", "--cached", "--quiet"]).returncode == 0:
        return
    run(
        [
            "git",
            "-c",
            "user.name=github-actions[bot]",
            "-c",
            "user.email=41898282+github-actions[bot]@users.noreply.github.com",
            "commit",
            "-m",
            message,
        ],
        check=True,
    )


def verify_twice(path: Path, label: str) -> tuple[bool, dict[str, Any]]:
    first = compile_module(path, f"{label}-verify-1")
    if not first["passed"]:
        return False, first
    audit_source(path)
    second = compile_module(path, f"{label}-verify-2")
    return bool(second["passed"]), second


def target_sequence() -> list[Path]:
    targets = [TARGET_DIR / "Mock2_FunctionalAnalysis.lean"]
    integrated = TARGET_DIR / "Mock2_FunctionalAnalysis_Integrated.lean"
    if integrated.exists():
        targets.append(integrated)
    targets.extend(sorted(TARGET_DIR.glob("Mock3*.lean")))
    qym = TARGET_DIR / "QYM.lean"
    if qym.exists():
        targets.append(qym)
    return targets


def repair_target(path: Path, state: dict[str, Any], max_rounds: int, deadline: float) -> bool:
    state["phase"] = path.stem
    save_state(state)
    # Persist the exact recovered PASS 327 candidate as the local baseline.
    local_commit(f"wip: materialize PASS 327 candidate for {path.stem}", [path, STATE_PATH])
    current = compile_module(path, f"{path.stem}-initial-r{state['round']}")
    if current["passed"]:
        ok, final = verify_twice(path, path.stem)
        if ok:
            state["history"].append({"target": path.stem, "status": "passed-without-new-patch", **final})
            save_state(state)
            local_commit(f"ci: verify {path.stem} twice from PASS 327 baseline", [STATE_PATH])
            return True
    stagnant = 0
    for _ in range(max_rounds):
        if time.time() >= deadline:
            state["history"].append({"target": path.stem, "status": "deadline-checkpoint", **current})
            save_state(state)
            local_commit(f"wip: checkpoint PASS 327 repair for {path.stem}", [path, STATE_PATH])
            return False
        state["round"] += 1
        state["model_calls"] += 1
        save_state(state)
        prompt = build_prompt(path, current)
        prompt_path = EVIDENCE / "prompts" / f"{state['round']:03d}-{path.stem}.txt"
        prompt_path.parent.mkdir(parents=True, exist_ok=True)
        prompt_path.write_text(prompt, encoding="utf-8")
        before_source = path.read_text(encoding="utf-8")
        try:
            response, model = call_model(prompt, state["model_calls"])
            diff = extract_diff(response)
            validate_diff(diff, path, before_source)
            backup = apply_diff(diff, path)
            candidate = compile_module(path, f"{path.stem}-candidate-r{state['round']}")
            accepted, reason = improvement(current, candidate)
            record = {
                "target": path.stem,
                "round": state["round"],
                "model": model,
                "accepted": accepted,
                "reason": reason,
                "before": current,
                "after": candidate,
                "patch_sha256": sha256_text(diff),
            }
            state["history"].append(record)
            if accepted:
                state["accepted_patches"] += 1
                stagnant = 0
                current = candidate
                patch_archive = EVIDENCE / "accepted-patches"
                patch_archive.mkdir(parents=True, exist_ok=True)
                (patch_archive / f"{state['round']:03d}-{path.stem}.patch").write_text(diff, encoding="utf-8")
                save_state(state)
                local_commit(
                    f"fix({path.stem}): PASS 327 repair round {state['round']}",
                    [path, STATE_PATH],
                )
                if current["passed"]:
                    ok, final = verify_twice(path, path.stem)
                    if ok:
                        state["history"].append({"target": path.stem, "status": "passed-twice", **final})
                        save_state(state)
                        local_commit(f"ci: verify {path.stem} twice", [STATE_PATH])
                        return True
            else:
                state["rejected_patches"] += 1
                stagnant += 1
                path.write_text(backup, encoding="utf-8")
                save_state(state)
            if stagnant >= 4:
                # Enlarge the diagnostic batch on the next call by compiling once
                # from the unchanged accepted source; this also guards against a
                # flaky or stale candidate log.
                current = compile_module(path, f"{path.stem}-refresh-r{state['round']}")
                stagnant = 0
        except Exception as exc:
            state["rejected_patches"] += 1
            stagnant += 1
            path.write_text(before_source, encoding="utf-8")
            state["history"].append(
                {
                    "target": path.stem,
                    "round": state["round"],
                    "accepted": False,
                    "reason": f"agent exception: {type(exc).__name__}: {exc}",
                }
            )
            save_state(state)
            (EVIDENCE / "agent-errors.log").parent.mkdir(parents=True, exist_ok=True)
            with (EVIDENCE / "agent-errors.log").open("a", encoding="utf-8") as handle:
                handle.write(f"round {state['round']} {path}: {type(exc).__name__}: {exc}\n")
            time.sleep(min(60, 5 * stagnant))
    state["history"].append({"target": path.stem, "status": "round-limit", **current})
    save_state(state)
    local_commit(f"wip: checkpoint PASS 327 repair for {path.stem}", [path, STATE_PATH])
    return False


def final_gate(state: dict[str, Any], targets: list[Path]) -> None:
    # Dependency order is explicit and every requested target is checked twice.
    dependencies = [TARGET_DIR / "Mock2.lean", TARGET_DIR / "Mock2_Advanced.lean"]
    all_paths = [path for path in dependencies + targets if path.exists()]
    final_results: list[dict[str, Any]] = []
    for path in all_paths:
        audit_source(path)
        ok, result = verify_twice(path, f"final-{path.stem}")
        final_results.append(result)
        if not ok:
            raise RuntimeError(f"final two-pass gate failed for {path}: {result}")
    marker = {
        "baseline": "PASS 327",
        "run_id": 31159696948,
        "job_id": 92827136991,
        "status": "PASS",
        "runtime_repair_in_final_gate": False,
        "targets": [str(path.relative_to(ROOT)) for path in all_paths],
        "results": final_results,
        "forbidden_tokens": "0 for every audited source",
        "verified_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "head_before_commit": run(["git", "rev-parse", "HEAD"], check=True).stdout.strip(),
    }
    SUCCESS_PATH.parent.mkdir(parents=True, exist_ok=True)
    SUCCESS_PATH.write_text(json.dumps(marker, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    state["phase"] = "PASS_327_TARGETS_COMPLETE"
    state["completed_utc"] = marker["verified_utc"]
    save_state(state)
    local_commit(
        "fix: PASS 327 Mock2 Advanced FA Mock3 QYM direct-source gate",
        targets + [SUCCESS_PATH, STATE_PATH],
    )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-rounds-per-target", type=int, default=24)
    parser.add_argument("--minutes", type=int, default=315)
    args = parser.parse_args()
    EVIDENCE.mkdir(parents=True, exist_ok=True)
    state = load_state()
    deadline = time.time() + args.minutes * 60
    targets = target_sequence()
    if not targets or targets[0].name != "Mock2_FunctionalAnalysis.lean":
        raise RuntimeError(f"unexpected target sequence: {targets}")
    for path in targets:
        if not repair_target(path, state, args.max_rounds_per_target, deadline):
            save_state(state)
            print(json.dumps({"status": "CHECKPOINT", "state": state}, ensure_ascii=False))
            return 20
    final_gate(state, targets)
    print(json.dumps({"status": "PASS", "state": state}, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
