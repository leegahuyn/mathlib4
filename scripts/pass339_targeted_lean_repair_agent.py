from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import time
from typing import Iterable
from urllib import error, request

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / os.environ.get(
    "TARGET_FILE", "PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean"
)
MODULE = os.environ.get("TARGET_MODULE", "Mock2_FunctionalAnalysis")
MAX_ROUNDS = int(os.environ.get("PASS339_AGENT_ROUNDS", "24"))
MAX_ERRORS = int(os.environ.get("PASS339_AGENT_MAX_ERRORS", "40"))
EVIDENCE = Path(os.environ.get("EVIDENCE_DIR", "/tmp/pass339-targeted-agent"))
PASS339_SHA = os.environ.get(
    "BASELINE_SHA256",
    "57f084029aff8e8a4b95d13e0daa9890eaa036716da48b3a3352ac3023be1c25",
)
OUTDIR = ROOT / ".lake/build/lib/lean/PrimalitySheafVerification"

EVIDENCE.mkdir(parents=True, exist_ok=True)
(EVIDENCE / "rounds").mkdir(exist_ok=True)
OUTDIR.mkdir(parents=True, exist_ok=True)

ERROR_HEADER = re.compile(
    r"(?m)^(?P<header>.*Mock2_FunctionalAnalysis\.lean:(?P<line>\d+):(?P<col>\d+): error(?:\([^)]*\))?:.*)$"
)
DECL_START = re.compile(
    r"^\s*(?:private\s+)?(?:protected\s+)?(?:noncomputable\s+)?"
    r"(?P<kind>theorem|lemma|corollary)\s+(?P<name>[^\s:{(]+)"
)
FORBIDDEN = {
    "sorry": re.compile(r"\bsorry\b"),
    "admit": re.compile(r"\badmit\b"),
    "global_axiom": re.compile(r"(?m)^\s*axiom\b"),
    "unsafe": re.compile(r"\bunsafe\b"),
    "native_decide": re.compile(r"\bnative_decide\b"),
    "Lean.ofReduceBool": re.compile(r"\bLean\.ofReduceBool\b"),
}


def sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def run(
    args: list[str], *, cwd: Path = ROOT, input_text: str | None = None, timeout: int = 1800
) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        args,
        cwd=cwd,
        input=input_text,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=timeout,
        check=False,
    )


def strip_comments_and_strings(source: str) -> str:
    out: list[str] = []
    i = 0
    depth = 0
    in_string = False
    escaped = False
    while i < len(source):
        if depth:
            if source.startswith("/-", i):
                depth += 1
                out.extend("  ")
                i += 2
            elif source.startswith("-/", i):
                depth -= 1
                out.extend("  ")
                i += 2
            else:
                out.append("\n" if source[i] == "\n" else " ")
                i += 1
        elif in_string:
            ch = source[i]
            out.append("\n" if ch == "\n" else " ")
            if escaped:
                escaped = False
            elif ch == "\\":
                escaped = True
            elif ch == '"':
                in_string = False
            i += 1
        elif source.startswith("/-", i):
            depth = 1
            out.extend("  ")
            i += 2
        elif source.startswith("--", i):
            while i < len(source) and source[i] != "\n":
                out.append(" ")
                i += 1
        elif source[i] == '"':
            in_string = True
            out.append(" ")
            i += 1
        else:
            out.append(source[i])
            i += 1
    if depth or in_string:
        raise RuntimeError("unterminated comment or string")
    return "".join(out)


def forbidden_counts(source: str) -> dict[str, int]:
    code = strip_comments_and_strings(source)
    return {name: len(pattern.findall(code)) for name, pattern in FORBIDDEN.items()}


def declaration_headers(source: str) -> dict[str, str]:
    """Record public theorem-like signatures up to the proof assignment.

    This is deliberately conservative. Any model edit that alters a recorded
    header is rejected, while edits inside proof bodies remain possible.
    """
    lines = source.splitlines()
    result: dict[str, str] = {}
    i = 0
    while i < len(lines):
        match = DECL_START.match(lines[i])
        if not match:
            i += 1
            continue
        line = lines[i]
        is_private = bool(re.match(r"^\s*private\b", line))
        name = match.group("name")
        block: list[str] = []
        j = i
        found_assignment = False
        while j < len(lines) and j < i + 160:
            current = lines[j]
            if ":=" in current:
                block.append(current.split(":=", 1)[0])
                found_assignment = True
                break
            block.append(current)
            j += 1
        if found_assignment and not is_private:
            result[name] = "\n".join(block).rstrip()
        i = max(i + 1, j + 1)
    return result


def compile_target(label: str) -> dict[str, object]:
    log = EVIDENCE / "rounds" / f"{label}.log"
    olean = OUTDIR / f"{MODULE}.olean"
    ilean = OUTDIR / f"{MODULE}.ilean"
    for path in (olean, ilean, OUTDIR / f"{MODULE}.olean.private"):
        path.unlink(missing_ok=True)
    proc = run(
        [
            "lake",
            "env",
            "lean",
            f"-DmaxErrors={MAX_ERRORS}",
            str(TARGET.relative_to(ROOT)),
            "-o",
            str(olean.relative_to(ROOT)),
            "-i",
            str(ilean.relative_to(ROOT)),
        ],
        timeout=2400,
    )
    log.write_text(proc.stdout, encoding="utf-8")
    matches = list(ERROR_HEADER.finditer(proc.stdout))
    distinct_lines: list[int] = []
    for match in matches:
        line = int(match.group("line"))
        if line not in distinct_lines:
            distinct_lines.append(line)
    result: dict[str, object] = {
        "label": label,
        "exit_code": proc.returncode,
        "error_count": len(matches),
        "first_error_line": distinct_lines[0] if distinct_lines else 10**9,
        "error_lines": distinct_lines,
        "source_sha256": sha256_text(TARGET.read_text(encoding="utf-8")),
        "olean": olean.is_file() and olean.stat().st_size > 0,
        "ilean": ilean.is_file() and ilean.stat().st_size > 0,
    }
    (EVIDENCE / "rounds" / f"{label}.json").write_text(
        json.dumps(result, indent=2), encoding="utf-8"
    )
    return result


def is_success(result: dict[str, object]) -> bool:
    return (
        int(result["exit_code"]) == 0
        and int(result["error_count"]) == 0
        and bool(result["olean"])
        and bool(result["ilean"])
    )


def is_progress(before: dict[str, object], after: dict[str, object]) -> bool:
    before_line = int(before["first_error_line"])
    after_line = int(after["first_error_line"])
    before_errors = int(before["error_count"])
    after_errors = int(after["error_count"])
    if is_success(after):
        return True
    if after_line > before_line:
        return True
    return after_line == before_line and after_errors < before_errors


def error_blocks(log_text: str, limit: int = 12) -> str:
    matches = list(ERROR_HEADER.finditer(log_text))
    blocks: list[str] = []
    for index, match in enumerate(matches[:limit]):
        start = match.start()
        end = matches[index + 1].start() if index + 1 < len(matches) else len(log_text)
        block = log_text[start:end]
        blocks.append(block[:6000])
    return "\n\n".join(blocks)[:50000]


def source_context(source: str, lines: Iterable[int]) -> str:
    src_lines = source.splitlines()
    chunks: list[str] = []
    seen: set[tuple[int, int]] = set()
    for line in list(lines)[:10]:
        start = max(1, line - 90)
        end = min(len(src_lines), line + 120)
        key = (start, end)
        if key in seen:
            continue
        seen.add(key)
        chunk = [f"--- {TARGET.relative_to(ROOT)} lines {start}-{end} ---"]
        chunk.extend(f"{n}: {src_lines[n - 1]}" for n in range(start, end + 1))
        chunks.append("\n".join(chunk))
    return "\n\n".join(chunks)[:90000]


def catalog_models(token: str) -> list[str]:
    static = [
        "openai/gpt-5",
        "openai/gpt-4.1",
        "openai/gpt-4o",
        "openai/gpt-4.1-mini",
        "mistral-ai/Codestral-2501",
        "deepseek/DeepSeek-V3-0324",
    ]
    req = request.Request(
        "https://models.github.ai/catalog/models",
        headers={
            "Accept": "application/vnd.github+json",
            "Authorization": f"Bearer {token}",
            "X-GitHub-Api-Version": "2022-11-28",
        },
    )
    try:
        with request.urlopen(req, timeout=60) as response:
            payload = json.loads(response.read().decode("utf-8"))
        records = payload.get("models", payload) if isinstance(payload, dict) else payload
        ids: list[str] = []
        if isinstance(records, list):
            for item in records:
                if isinstance(item, dict):
                    identifier = item.get("id") or item.get("name")
                    if isinstance(identifier, str):
                        ids.append(identifier)
        preferred: list[str] = []
        needles = ("gpt-5", "gpt-4.1", "codestral", "deepseek", "gpt-4o")
        for needle in needles:
            preferred.extend(identifier for identifier in ids if needle.lower() in identifier.lower())
        for identifier in static:
            if identifier not in preferred:
                preferred.append(identifier)
        return preferred[:12]
    except Exception as exc:  # catalog availability must not block static fallbacks
        (EVIDENCE / "catalog-error.txt").write_text(repr(exc), encoding="utf-8")
        return static


def call_rest_model(token: str, model: str, prompt: str) -> str:
    payload = {
        "model": model,
        "temperature": 0,
        "max_tokens": 12000,
        "messages": [
            {
                "role": "system",
                "content": (
                    "You repair Lean 4/mathlib source. Return only one unified diff. "
                    "Do not weaken theorem statements, add assumptions, use sorry/admit/axiom/unsafe/"
                    "native_decide/Lean.ofReduceBool, or edit any file except the requested target."
                ),
            },
            {"role": "user", "content": prompt},
        ],
    }
    req = request.Request(
        "https://models.github.ai/inference/chat/completions",
        data=json.dumps(payload).encode("utf-8"),
        method="POST",
        headers={
            "Accept": "application/vnd.github+json",
            "Content-Type": "application/json",
            "Authorization": f"Bearer {token}",
            "X-GitHub-Api-Version": "2022-11-28",
        },
    )
    with request.urlopen(req, timeout=300) as response:
        data = json.loads(response.read().decode("utf-8"))
    return data["choices"][0]["message"]["content"]


def call_gh_models(model: str, prompt: str) -> str:
    if shutil.which("gh") is None:
        raise RuntimeError("gh CLI unavailable")
    install = run(["gh", "extension", "install", "github/gh-models", "--force"], timeout=300)
    if install.returncode != 0 and "already exists" not in install.stdout:
        raise RuntimeError(install.stdout)
    proc = run(["gh", "models", "run", model, "-p", prompt], timeout=600)
    if proc.returncode != 0:
        raise RuntimeError(proc.stdout)
    return proc.stdout


def extract_diff(response_text: str) -> str:
    fenced = re.search(r"```(?:diff|patch)?\s*(.*?)```", response_text, re.S)
    text = fenced.group(1).strip() if fenced else response_text.strip()
    start_positions = [position for marker in ("diff --git ", "--- a/") if (position := text.find(marker)) >= 0]
    if not start_positions:
        raise RuntimeError("model response did not contain a unified diff")
    return text[min(start_positions):].rstrip() + "\n"


def normalize_patch(patch: str) -> str:
    rel = str(TARGET.relative_to(ROOT))
    if patch.startswith("--- ") and not patch.startswith("--- a/"):
        lines = patch.splitlines()
        if len(lines) >= 2 and lines[0].startswith("--- ") and lines[1].startswith("+++ "):
            lines[0] = f"--- a/{rel}"
            lines[1] = f"+++ b/{rel}"
            patch = "\n".join(lines) + "\n"
    return patch


def main() -> int:
    if not TARGET.is_file():
        raise FileNotFoundError(TARGET)
    initial_source = TARGET.read_text(encoding="utf-8")
    initial_sha = sha256_text(initial_source)
    if initial_sha != PASS339_SHA:
        raise RuntimeError(f"PASS 339 input mismatch: {initial_sha} != {PASS339_SHA}")
    headers = declaration_headers(initial_source)
    initial_forbidden = forbidden_counts(initial_source)
    if any(initial_forbidden.values()):
        raise RuntimeError(f"forbidden token already present: {initial_forbidden}")
    token = os.environ.get("MODELS_TOKEN") or os.environ.get("GH_TOKEN") or os.environ.get("GITHUB_TOKEN")
    if not token:
        raise RuntimeError("GitHub Models token is unavailable")
    models = catalog_models(token)
    (EVIDENCE / "models.json").write_text(json.dumps(models, indent=2), encoding="utf-8")

    current = compile_target("round-000-baseline")
    if is_success(current):
        verify = compile_target("round-000-verify")
        return 0 if is_success(verify) else 1

    for round_number in range(1, MAX_ROUNDS + 1):
        source = TARGET.read_text(encoding="utf-8")
        log_path = EVIDENCE / "rounds" / f"{current['label']}.log"
        log_text = log_path.read_text(encoding="utf-8", errors="replace")
        error_lines = [int(x) for x in current.get("error_lines", [])]
        prompt = f"""
Target file: {TARGET.relative_to(ROOT)}
Lean version and dependencies are pinned by the repository.
PASS 339 candidate SHA-256: {PASS339_SHA}
Current source SHA-256: {sha256_text(source)}
Current compile result: exit={current['exit_code']}, errors={current['error_count']}, first_error_line={current['first_error_line']}.

Produce ONE unified diff for only `{TARGET.relative_to(ROOT)}`. Fix as many independent errors shown below as can be fixed safely in one coherent patch. Preserve every existing public theorem/lemma/corollary statement exactly. You may change proof bodies and add private helper lemmas. Do not add imports unless a missing existing Mathlib theorem genuinely requires one. Never use sorry, admit, new axiom, unsafe, native_decide, Lean.ofReduceBool, or weaken a conclusion.

COMPILER ERRORS:
{error_blocks(log_text)}

SOURCE CONTEXT:
{source_context(source, error_lines)}
""".strip()
        round_dir = EVIDENCE / "rounds" / f"round-{round_number:03d}"
        round_dir.mkdir(exist_ok=True)
        (round_dir / "prompt.txt").write_text(prompt, encoding="utf-8")

        accepted = False
        for model in models:
            safe_model = re.sub(r"[^A-Za-z0-9_.-]+", "_", model)
            try:
                try:
                    response_text = call_rest_model(token, model, prompt)
                except Exception as rest_exc:
                    (round_dir / f"{safe_model}-rest-error.txt").write_text(
                        repr(rest_exc), encoding="utf-8"
                    )
                    response_text = call_gh_models(model, prompt)
                (round_dir / f"{safe_model}-response.txt").write_text(
                    response_text, encoding="utf-8"
                )
                patch = normalize_patch(extract_diff(response_text))
                (round_dir / f"{safe_model}.patch").write_text(patch, encoding="utf-8")

                before = TARGET.read_text(encoding="utf-8")
                backup = round_dir / "before.lean"
                backup.write_text(before, encoding="utf-8")
                check = run(["git", "apply", "--check", str(round_dir / f"{safe_model}.patch")])
                if check.returncode != 0:
                    raise RuntimeError(check.stdout)
                applied = run(["git", "apply", "--whitespace=nowarn", str(round_dir / f"{safe_model}.patch")])
                if applied.returncode != 0:
                    raise RuntimeError(applied.stdout)

                changed = run(["git", "diff", "--name-only"]).stdout.splitlines()
                rel = str(TARGET.relative_to(ROOT))
                if any(path != rel for path in changed):
                    raise RuntimeError(f"patch changed unexpected files: {changed}")
                candidate = TARGET.read_text(encoding="utf-8")
                if declaration_headers(candidate) != headers:
                    raise RuntimeError("public theorem/lemma/corollary statement fingerprint changed")
                counts = forbidden_counts(candidate)
                if any(counts.values()):
                    raise RuntimeError(f"forbidden token introduced: {counts}")

                after = compile_target(f"round-{round_number:03d}-{safe_model}")
                if not is_progress(current, after):
                    raise RuntimeError(
                        f"no compiler progress: before={current}, after={after}"
                    )
                (round_dir / "accepted-model.txt").write_text(model, encoding="utf-8")
                current = after
                accepted = True
                if is_success(current):
                    verify = compile_target(f"round-{round_number:03d}-verify")
                    if is_success(verify):
                        (EVIDENCE / "status.txt").write_text(
                            "PASS339_TARGETED_AGENT=SUCCESS\n", encoding="utf-8"
                        )
                        return 0
                    current = verify
                break
            except Exception as exc:
                (round_dir / f"{safe_model}-rejected.txt").write_text(
                    repr(exc), encoding="utf-8"
                )
                # Restore exactly the last accepted source before trying another model.
                if (round_dir / "before.lean").exists():
                    TARGET.write_text(
                        (round_dir / "before.lean").read_text(encoding="utf-8"),
                        encoding="utf-8",
                    )
                run(["git", "restore", "--worktree", "--", str(TARGET.relative_to(ROOT))])
                # git restore returns the checked-in pre-PASS339 source, so restore the
                # accepted source snapshot maintained for this round when necessary.
                if (round_dir / "before.lean").exists():
                    TARGET.write_text(
                        (round_dir / "before.lean").read_text(encoding="utf-8"),
                        encoding="utf-8",
                    )
                continue
        if not accepted:
            (EVIDENCE / "status.txt").write_text(
                f"PASS339_TARGETED_AGENT=STALLED_AT_ROUND_{round_number}\n",
                encoding="utf-8",
            )
            return 2

    (EVIDENCE / "status.txt").write_text(
        f"PASS339_TARGETED_AGENT=ROUND_LIMIT_{MAX_ROUNDS}\n", encoding="utf-8"
    )
    return 3


if __name__ == "__main__":
    raise SystemExit(main())
