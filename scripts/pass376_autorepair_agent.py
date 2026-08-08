from __future__ import annotations

import json
import os
import re
import shutil
import subprocess
import sys
import time
import urllib.error
import urllib.request
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
LOG_ROOT = ROOT / "build-logs" / "pass376-autorepair"
SUMMARY = ROOT / "build-logs" / "pass376-autorepair-summary.json"
SUCCESS_MARKER = ROOT / "build-logs" / "pass376-fa-mock3-qym-2x-pass.txt"
EXPECTED_PASS375C_SHA256 = "d2e1b383b9e60fd18607094ce104679cd604e8c90ffc0261d8a877e700b99b8e"

FORBIDDEN_RE = re.compile(
    r"\b(?:sorry|admit|native_decide)\b|Lean\.ofReduceBool|"
    r"(?m)^\s*(?:unsafe\s+|axiom\s+)"
)
DECL_RE = re.compile(r"(?m)^(?P<indent>\s*)(?P<private>private\s+)?"
                     r"(?P<kind>theorem|lemma|corollary)\s+(?P<name>[^\s(:{]+)")
IMPORT_RE = re.compile(r"(?m)^\s*(?:public\s+)?import\s+([^\s]+)")
ERROR_POS_RE = re.compile(r"\.lean:(\d+):(\d+):\s+error:")


@dataclass(frozen=True)
class CompileResult:
    returncode: int
    error_count: int
    first_line: int
    first_col: int
    log_path: Path
    elapsed_seconds: float

    @property
    def passed(self) -> bool:
        return self.returncode == 0 and self.error_count == 0

    def score(self) -> tuple[int, int, int]:
        if self.passed:
            return (1, 10**9, 0)
        return (0, self.first_line, -self.error_count)


def run(cmd: list[str], *, cwd: Path = ROOT, input_text: str | None = None,
        timeout: int | None = None, check: bool = False) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        cmd,
        cwd=cwd,
        input=input_text,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=timeout,
        check=check,
    )


def sha256_file(path: Path) -> str:
    import hashlib
    return hashlib.sha256(path.read_bytes()).hexdigest()


def strip_comments_and_strings(text: str) -> str:
    """Remove Lean comments and string/character contents while preserving newlines."""
    out: list[str] = []
    i = 0
    block_depth = 0
    line_comment = False
    in_string = False
    in_char = False
    escape = False
    while i < len(text):
        ch = text[i]
        nxt = text[i + 1] if i + 1 < len(text) else ""
        if line_comment:
            if ch == "\n":
                line_comment = False
                out.append("\n")
            else:
                out.append(" ")
            i += 1
            continue
        if block_depth:
            if ch == "/" and nxt == "-":
                block_depth += 1
                out.extend("  ")
                i += 2
            elif ch == "-" and nxt == "/":
                block_depth -= 1
                out.extend("  ")
                i += 2
            else:
                out.append("\n" if ch == "\n" else " ")
                i += 1
            continue
        if in_string:
            out.append("\n" if ch == "\n" else " ")
            if escape:
                escape = False
            elif ch == "\\":
                escape = True
            elif ch == '"':
                in_string = False
            i += 1
            continue
        if in_char:
            out.append("\n" if ch == "\n" else " ")
            if escape:
                escape = False
            elif ch == "\\":
                escape = True
            elif ch == "'":
                in_char = False
            i += 1
            continue
        if ch == "-" and nxt == "-":
            line_comment = True
            out.extend("  ")
            i += 2
        elif ch == "/" and nxt == "-":
            block_depth = 1
            out.extend("  ")
            i += 2
        elif ch == '"':
            in_string = True
            out.append(" ")
            i += 1
        elif ch == "'" and (i == 0 or not (text[i - 1].isalnum() or text[i - 1] == "_")):
            in_char = True
            out.append(" ")
            i += 1
        else:
            out.append(ch)
            i += 1
    return "".join(out)


def declaration_headers(text: str) -> dict[str, str]:
    """Record existing non-private theorem/lemma/corollary headers through :=/where."""
    clean = strip_comments_and_strings(text)
    headers: dict[str, str] = {}
    for match in DECL_RE.finditer(clean):
        if match.group("private"):
            continue
        name = match.group("name")
        start = match.start()
        depth_round = depth_square = depth_curly = 0
        i = match.end()
        end = None
        while i < len(clean):
            ch = clean[i]
            if ch == "(": depth_round += 1
            elif ch == ")": depth_round = max(0, depth_round - 1)
            elif ch == "[": depth_square += 1
            elif ch == "]": depth_square = max(0, depth_square - 1)
            elif ch == "{": depth_curly += 1
            elif ch == "}": depth_curly = max(0, depth_curly - 1)
            if depth_round == depth_square == depth_curly == 0:
                if clean.startswith(":=", i):
                    end = i
                    break
                if clean.startswith(" where", i) or clean.startswith("\nwhere", i):
                    end = i
                    break
            i += 1
        if end is None:
            continue
        normalized = re.sub(r"\s+", " ", clean[start:end]).strip()
        headers[name] = normalized
    return headers


def validate_candidate(original_headers: dict[str, str], original_imports: set[str], text: str) -> tuple[bool, str]:
    clean = strip_comments_and_strings(text)
    bad = FORBIDDEN_RE.search(clean)
    if bad:
        return False, f"forbidden executable token: {bad.group(0)!r}"
    current_headers = declaration_headers(text)
    missing = sorted(set(original_headers) - set(current_headers))
    if missing:
        return False, f"public declarations removed: {missing[:8]}"
    changed = [name for name, header in original_headers.items() if current_headers.get(name) != header]
    if changed:
        return False, f"public declaration headers changed: {changed[:8]}"
    current_imports = set(IMPORT_RE.findall(clean))
    if not original_imports.issubset(current_imports):
        return False, f"existing imports removed: {sorted(original_imports - current_imports)}"
    return True, "ok"


def clean_artifacts_for(path: Path) -> None:
    stem = path.stem
    out_dir = ROOT / ".lake" / "build" / "lib" / "lean" / "PrimalitySheafVerification"
    if out_dir.exists():
        for suffix in (".olean", ".ilean", ".olean.hash", ".ilean.hash"):
            candidate = out_dir / f"{stem}{suffix}"
            candidate.unlink(missing_ok=True)


def compile_file(path: Path, label: str, *, max_errors: int = 8, timeout: int = 1800) -> CompileResult:
    LOG_ROOT.mkdir(parents=True, exist_ok=True)
    log_path = LOG_ROOT / f"{label}.log"
    started = time.monotonic()
    proc = run(
        ["lake", "env", "lean", f"-DmaxErrors={max_errors}", str(path.relative_to(ROOT))],
        timeout=timeout,
    )
    elapsed = time.monotonic() - started
    log_path.write_text(proc.stdout, encoding="utf-8")
    positions = [(int(a), int(b)) for a, b in ERROR_POS_RE.findall(proc.stdout)]
    if positions:
        first_line, first_col = positions[0]
    else:
        first_line, first_col = (10**9 if proc.returncode == 0 else 0), 0
    return CompileResult(
        returncode=proc.returncode,
        error_count=len(positions),
        first_line=first_line,
        first_col=first_col,
        log_path=log_path,
        elapsed_seconds=elapsed,
    )


def error_context(log_text: str, source_text: str, max_chars: int = 52000) -> str:
    source_lines = source_text.splitlines()
    positions = [(int(a), int(b)) for a, b in ERROR_POS_RE.findall(log_text)]
    chunks: list[str] = []
    seen: set[int] = set()
    for line, col in positions[:8]:
        if line in seen:
            continue
        seen.add(line)
        lo = max(1, line - 55)
        hi = min(len(source_lines), line + 65)
        numbered = "\n".join(f"{n:6d}: {source_lines[n - 1]}" for n in range(lo, hi + 1))
        chunks.append(f"SOURCE CONTEXT AROUND {line}:{col}\n{numbered}")
    error_excerpt = log_text[:24000]
    combined = "\n\n".join(["LEAN ERROR OUTPUT\n" + error_excerpt, *chunks])
    return combined[:max_chars]


def extract_unified_diff(response: str) -> str | None:
    fenced = re.search(r"```(?:diff|patch)?\s*\n(.*?)```", response, flags=re.S)
    if fenced:
        response = fenced.group(1)
    starts = [i for token in ("diff --git ", "--- a/") if (i := response.find(token)) >= 0]
    if not starts:
        return None
    diff = response[min(starts):].strip() + "\n"
    # Only the target source may be edited.
    paths = re.findall(r"^(?:\+\+\+|---)\s+[ab]/([^\t\n]+)", diff, flags=re.M)
    allowed = str(TARGET.relative_to(ROOT))
    if not paths or any(path != allowed for path in paths):
        return None
    return diff


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
                    "You are an expert Lean 4/mathlib repair engineer. Return only a minimal unified diff. "
                    "Never use sorry, admit, axiom, unsafe, native_decide, Lean.ofReduceBool, or weaken a theorem."
                ),
            },
            {"role": "user", "content": prompt},
        ],
        "temperature": 0.05,
        "max_tokens": 7000,
    }
    request = urllib.request.Request(
        "https://models.github.ai/inference/chat/completions",
        data=json.dumps(payload).encode("utf-8"),
        headers={
            "Authorization": f"Bearer {token}",
            "Content-Type": "application/json",
            "Accept": "application/json",
            "User-Agent": "pass376-lean-repair",
        },
        method="POST",
    )
    try:
        with urllib.request.urlopen(request, timeout=180) as response:
            body = json.loads(response.read().decode("utf-8"))
        return body["choices"][0]["message"]["content"]
    except (urllib.error.URLError, urllib.error.HTTPError, KeyError, IndexError, json.JSONDecodeError) as exc:
        (LOG_ROOT / "model-errors.log").open("a", encoding="utf-8").write(
            f"REST {model}: {type(exc).__name__}: {exc}\n"
        )
        return None


def cli_model_call(prompt: str, model: str) -> str | None:
    if shutil.which("gh") is None:
        return None
    env = os.environ.copy()
    env.setdefault("GH_TOKEN", env.get("GITHUB_TOKEN", ""))
    commands = [
        ["gh", "models", "run", model, "--prompt", prompt],
        ["gh", "models", "run", model, prompt],
        ["gh", "models", "run", model],
    ]
    for idx, command in enumerate(commands):
        try:
            proc = subprocess.run(
                command,
                cwd=ROOT,
                input=prompt if idx == 2 else None,
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                timeout=240,
                env=env,
            )
        except (OSError, subprocess.TimeoutExpired):
            continue
        if proc.returncode == 0 and proc.stdout.strip():
            return proc.stdout
    return None


def model_response(prompt: str, iteration: int, attempt: int) -> str | None:
    models = [
        "openai/gpt-4.1",
        "openai/gpt-4o",
        "openai/gpt-4o-mini",
        "openai/gpt-5-mini",
    ]
    model = models[(iteration + attempt) % len(models)]
    response = rest_model_call(prompt, model)
    if response is None:
        response = cli_model_call(prompt, model)
    if response:
        (LOG_ROOT / f"iteration-{iteration:02d}-attempt-{attempt}-{model.replace('/', '_')}.txt").write_text(
            response, encoding="utf-8"
        )
    return response


def build_prompt(result: CompileResult, source_text: str, rejection: str = "") -> str:
    context = error_context(result.log_path.read_text(encoding="utf-8", errors="replace"), source_text)
    return f"""
Repair the first independent Lean errors in this exact file:
`PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean`.

Hard constraints:
- Output ONLY a unified diff for that one file.
- Keep every existing public theorem/lemma/corollary name, binder, assumption, and conclusion byte-for-byte unchanged.
- You may rewrite proof bodies and add `private lemma`/`private theorem` helpers.
- Do not add or use `sorry`, `admit`, new global `axiom`, `unsafe`, `native_decide`, or `Lean.ofReduceBool`.
- Do not delete existing imports. Add an import only when genuinely required.
- Use current Lean 4.33.0-rc1 and the checked-out mathlib API.
- Fix at most the first three independent errors so the patch stays small and reviewable.
- Avoid broad `simp` or heartbeat increases unless the error output specifically proves they are needed.

Current compiler result: exit={result.returncode}, error_headers={result.error_count}, first={result.first_line}:{result.first_col}.
Previous patch rejection, if any: {rejection or '(none)'}

{context}
""".strip()


def try_patch(iteration: int, baseline: CompileResult, original_headers: dict[str, str],
              original_imports: set[str]) -> tuple[bool, CompileResult, str]:
    before_bytes = TARGET.read_bytes()
    before_text = before_bytes.decode("utf-8")
    rejection = ""
    for attempt in range(4):
        prompt = build_prompt(baseline, before_text, rejection)
        response = model_response(prompt, iteration, attempt)
        if response is None:
            rejection = "model endpoint/CLI produced no usable response"
            continue
        diff = extract_unified_diff(response)
        if diff is None:
            rejection = "response was not a one-file unified diff"
            continue
        patch_path = LOG_ROOT / f"iteration-{iteration:02d}-attempt-{attempt}.patch"
        patch_path.write_text(diff, encoding="utf-8")
        TARGET.write_bytes(before_bytes)
        check = run(["git", "apply", "--check", str(patch_path)])
        if check.returncode != 0:
            rejection = "git apply --check failed: " + check.stdout[-1600:]
            continue
        applied = run(["git", "apply", "--whitespace=nowarn", str(patch_path)])
        if applied.returncode != 0:
            rejection = "git apply failed: " + applied.stdout[-1600:]
            continue
        candidate_text = TARGET.read_text(encoding="utf-8")
        valid, reason = validate_candidate(original_headers, original_imports, candidate_text)
        if not valid:
            TARGET.write_bytes(before_bytes)
            rejection = reason
            continue
        candidate = compile_file(TARGET, f"iteration-{iteration:02d}-attempt-{attempt}", max_errors=8)
        if candidate.passed or candidate.score() > baseline.score():
            return True, candidate, "accepted"
        TARGET.write_bytes(before_bytes)
        rejection = (
            f"compiler did not advance: baseline={baseline.score()} candidate={candidate.score()}; "
            f"first candidate error={candidate.first_line}:{candidate.first_col}"
        )
    TARGET.write_bytes(before_bytes)
    return False, baseline, rejection


def verify_twice(path: Path, label: str) -> tuple[bool, list[CompileResult]]:
    results: list[CompileResult] = []
    for run_number in (1, 2):
        clean_artifacts_for(path)
        result = compile_file(path, f"verify-{label}-run{run_number}", max_errors=2000, timeout=3600)
        results.append(result)
        if not result.passed:
            return False, results
    return True, results


def downstream_targets() -> list[Path]:
    directory = ROOT / "PrimalitySheafVerification"
    targets: list[Path] = []
    integrated = directory / "Mock2_FunctionalAnalysis_Integrated.lean"
    if integrated.exists():
        targets.append(integrated)
    targets.extend(sorted(directory.glob("Mock3*.lean")))
    qym = directory / "QYM.lean"
    if qym.exists():
        targets.append(qym)
    return targets


def result_dict(result: CompileResult) -> dict[str, object]:
    return {
        "returncode": result.returncode,
        "error_count": result.error_count,
        "first_line": result.first_line,
        "first_col": result.first_col,
        "elapsed_seconds": round(result.elapsed_seconds, 3),
        "log": str(result.log_path.relative_to(ROOT)),
    }


def main() -> int:
    LOG_ROOT.mkdir(parents=True, exist_ok=True)
    SUCCESS_MARKER.unlink(missing_ok=True)
    if not TARGET.exists():
        raise FileNotFoundError(TARGET)
    start_sha = sha256_file(TARGET)
    if start_sha != EXPECTED_PASS375C_SHA256:
        print(f"[pass376] starting from noncanonical candidate {start_sha}")
    original_text = TARGET.read_text(encoding="utf-8")
    original_headers = declaration_headers(original_text)
    original_imports = set(IMPORT_RE.findall(strip_comments_and_strings(original_text)))
    valid, reason = validate_candidate(original_headers, original_imports, original_text)
    if not valid:
        raise RuntimeError(f"initial source violates trust gate: {reason}")

    max_iterations = int(os.environ.get("PASS376_MAX_ITERATIONS", "36"))
    baseline = compile_file(TARGET, "baseline-pass375c", max_errors=8, timeout=3600)
    history: list[dict[str, object]] = [{"iteration": 0, **result_dict(baseline)}]
    stalled = 0

    for iteration in range(1, max_iterations + 1):
        if baseline.passed:
            break
        accepted, candidate, note = try_patch(
            iteration, baseline, original_headers, original_imports
        )
        history.append({"iteration": iteration, "accepted": accepted, "note": note, **result_dict(candidate)})
        if accepted:
            baseline = candidate
            stalled = 0
            print(
                f"[pass376] iteration={iteration} advanced to "
                f"first={baseline.first_line}:{baseline.first_col} errors={baseline.error_count}"
            )
        else:
            stalled += 1
            print(f"[pass376] iteration={iteration} stalled: {note}")
            if stalled >= 5:
                break

    fa_ok = False
    downstream_ok = False
    fa_verification: list[CompileResult] = []
    downstream_verification: dict[str, list[CompileResult]] = {}

    if baseline.passed:
        fa_ok, fa_verification = verify_twice(TARGET, "Mock2_FunctionalAnalysis")
        if fa_ok:
            downstream_ok = True
            for target in downstream_targets():
                ok, results = verify_twice(target, target.stem)
                downstream_verification[target.name] = results
                if not ok:
                    downstream_ok = False
                    break

    final_text = TARGET.read_text(encoding="utf-8")
    final_valid, final_reason = validate_candidate(original_headers, original_imports, final_text)
    status = {
        "start_sha256": start_sha,
        "final_sha256": sha256_file(TARGET),
        "trust_gate": {"ok": final_valid, "reason": final_reason},
        "frontier_passed": baseline.passed,
        "fa_two_pass": fa_ok,
        "downstream_two_pass": downstream_ok,
        "success": bool(final_valid and fa_ok and downstream_ok),
        "history": history,
        "fa_verification": [result_dict(item) for item in fa_verification],
        "downstream_verification": {
            name: [result_dict(item) for item in results]
            for name, results in downstream_verification.items()
        },
        "targets": [str(path.relative_to(ROOT)) for path in downstream_targets()],
    }
    SUMMARY.parent.mkdir(parents=True, exist_ok=True)
    SUMMARY.write_text(json.dumps(status, ensure_ascii=False, indent=2), encoding="utf-8")

    if status["success"]:
        SUCCESS_MARKER.write_text(
            "Mock2_FunctionalAnalysis, Integrated, all Mock3 bridges, and QYM passed twice.\n"
            f"source_sha256={status['final_sha256']}\n",
            encoding="utf-8",
        )
        print("[pass376] SUCCESS: FA + Integrated/Mock3 + QYM all passed twice")
        return 0

    print(
        "[pass376] INCOMPLETE: "
        f"frontier={baseline.passed} fa2x={fa_ok} downstream2x={downstream_ok}"
    )
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
