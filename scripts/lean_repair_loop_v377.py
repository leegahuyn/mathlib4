from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time
import urllib.error
import urllib.request
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
OUT_ROOT = Path("/tmp/lean-repair-v377")
OUT_ROOT.mkdir(parents=True, exist_ok=True)

FORBIDDEN = (
    r"\bsorry\b",
    r"\badmit\b",
    r"^\s*axiom\b",
    r"\bunsafe\b",
    r"\bnative_decide\b",
    r"\bLean\.ofReduceBool\b",
)

DECL_RE = re.compile(
    r"^\s*(?P<prefix>(?:(?:noncomputable|protected|private|local)\s+)*)"
    r"(?P<kind>theorem|lemma|corollary|def|abbrev|structure|class)\s+"
    r"(?P<name>[^\s({:]+)"
)


def sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def strip_comments_and_strings(text: str) -> str:
    # This is deliberately conservative. It strips ordinary comments and quoted strings
    # before looking for executable escape hatches.
    text = re.sub(r"/\*.*?\*/", "", text, flags=re.S)
    text = re.sub(r"--[^\n]*", "", text)
    text = re.sub(r'"(?:\\.|[^"\\])*"', '""', text)
    return text


def forbidden_hits(text: str) -> list[str]:
    executable = strip_comments_and_strings(text)
    return [pat for pat in FORBIDDEN if re.search(pat, executable, flags=re.M)]


def declaration_headers(text: str) -> dict[str, str]:
    lines = text.splitlines()
    result: dict[str, str] = {}
    i = 0
    while i < len(lines):
        m = DECL_RE.match(lines[i])
        if not m:
            i += 1
            continue
        prefix = m.group("prefix") or ""
        if "private" in prefix.split():
            i += 1
            continue
        name = m.group("name")
        kind = m.group("kind")
        block = [lines[i]]
        j = i + 1
        while j < len(lines):
            block.append(lines[j])
            joined = "\n".join(block)
            if ":=" in joined or re.search(r"\n\s*where\s*$", joined) or re.search(
                r"\n\s*by\s*$", joined
            ):
                break
            if j - i > 120:
                break
            j += 1
        header = "\n".join(block)
        if ":=" in header:
            header = header.split(":=", 1)[0]
        header = re.sub(r"\n\s*where\s*$", "", header)
        header = re.sub(r"\n\s*by\s*$", "", header)
        header = re.sub(r"\s+", " ", header).strip()
        result[f"{kind}:{name}"] = header
        i = j + 1
    return result


def imports(text: str) -> set[str]:
    return {
        line.strip()
        for line in text.splitlines()
        if re.match(r"^\s*(?:public\s+)?import\s+", line)
    }


def artifact_paths(target: Path) -> list[Path]:
    stem = target.stem
    base = ROOT / ".lake" / "build" / "lib" / "lean" / "PrimalitySheafVerification"
    return [base / f"{stem}.olean", base / f"{stem}.ilean"]


def compile_target(target: Path, label: str, max_errors: int = 100) -> dict[str, Any]:
    for p in artifact_paths(target):
        p.unlink(missing_ok=True)
    out_dir = OUT_ROOT / target.stem
    out_dir.mkdir(parents=True, exist_ok=True)
    log = out_dir / f"{label}.log"
    env = os.environ.copy()
    env["PATH"] = f"{Path.home() / '.elan' / 'bin'}:{env.get('PATH', '')}"
    start = time.monotonic()
    try:
        proc = subprocess.run(
            [
                "lake",
                "env",
                "lean",
                f"-DmaxErrors={max_errors}",
                str(target.relative_to(ROOT)),
            ],
            cwd=ROOT,
            env=env,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=1800,
            check=False,
        )
        output = proc.stdout
        returncode = proc.returncode
    except subprocess.TimeoutExpired as exc:
        output = (exc.stdout or "") + "\n[repair-agent] compiler timeout\n"
        returncode = 124
    elapsed = time.monotonic() - start
    log.write_text(output, encoding="utf-8")
    matches = list(
        re.finditer(
            r"^(?P<path>.*?\.lean):(?P<line>\d+):(?P<col>\d+): error:\s*(?P<msg>.*)$",
            output,
            flags=re.M,
        )
    )
    first = matches[0] if matches else None
    return {
        "label": label,
        "returncode": returncode,
        "error_headers": len(matches),
        "first_error_line": int(first.group("line")) if first else None,
        "first_error_col": int(first.group("col")) if first else None,
        "first_error_message": first.group("msg").strip() if first else "",
        "elapsed_seconds": round(elapsed, 2),
        "log": str(log),
        "output": output,
    }


def nearest_declaration(lines: list[str], line_no: int) -> tuple[int, str]:
    idx = max(0, min(len(lines) - 1, line_no - 1))
    for i in range(idx, -1, -1):
        m = DECL_RE.match(lines[i])
        if m:
            return i + 1, f"{m.group('kind')} {m.group('name')}"
    return 1, "file start"


def source_excerpts(text: str, compiler_output: str, limit: int = 12) -> str:
    lines = text.splitlines()
    error_lines: list[int] = []
    for m in re.finditer(r"\.lean:(\d+):(\d+): error:", compiler_output):
        line = int(m.group(1))
        if line not in error_lines:
            error_lines.append(line)
        if len(error_lines) >= limit:
            break
    chunks: list[str] = []
    seen_decls: set[str] = set()
    for line in error_lines:
        decl_line, decl = nearest_declaration(lines, line)
        if decl in seen_decls:
            continue
        seen_decls.add(decl)
        lo = max(1, min(decl_line, line - 35))
        hi = min(len(lines), max(line + 35, decl_line + 90))
        chunks.append(f"===== {decl} | lines {lo}-{hi} | error line {line} =====")
        chunks.extend(f"{i}: {lines[i - 1]}" for i in range(lo, hi + 1))
    return "\n".join(chunks)


def concise_errors(output: str, max_chars: int = 28000) -> str:
    lines = output.splitlines()
    kept: list[str] = []
    active = 0
    for line in lines:
        if re.search(r"\.lean:\d+:\d+: error:", line):
            active = 12
        if active > 0:
            kept.append(line)
            active -= 1
        if sum(len(x) + 1 for x in kept) >= max_chars:
            break
    return "\n".join(kept)


def model_request(prompt: str, attempt: int) -> tuple[str, str]:
    token = os.environ.get("GITHUB_TOKEN", "").strip()
    if not token:
        raise RuntimeError("GITHUB_TOKEN is unavailable")
    endpoint = "https://models.github.ai/inference/chat/completions"
    model_candidates = [
        x.strip()
        for x in os.environ.get(
            "MODEL_CANDIDATES", "openai/gpt-5,openai/gpt-4.1,openai/gpt-4o"
        ).split(",")
        if x.strip()
    ]
    errors: list[str] = []
    for model in model_candidates:
        body = {
            "model": model,
            "messages": [
                {
                    "role": "system",
                    "content": (
                        "You are a senior Lean 4/mathlib proof engineer. Produce conservative, "
                        "kernel-checked source repairs. Never weaken statements or introduce proof escapes."
                    ),
                },
                {"role": "user", "content": prompt},
            ],
            "temperature": 0,
            "max_tokens": 12000,
        }
        req = urllib.request.Request(
            endpoint,
            data=json.dumps(body).encode("utf-8"),
            method="POST",
            headers={
                "Authorization": f"Bearer {token}",
                "Content-Type": "application/json",
                "Accept": "application/json",
                "User-Agent": "lean-repair-v377",
            },
        )
        try:
            with urllib.request.urlopen(req, timeout=240) as response:
                payload = json.loads(response.read().decode("utf-8"))
            content = payload["choices"][0]["message"]["content"]
            if not isinstance(content, str) or not content.strip():
                raise RuntimeError("model returned an empty response")
            return model, content
        except (urllib.error.HTTPError, urllib.error.URLError, TimeoutError, KeyError, RuntimeError) as exc:
            errors.append(f"{model}: {exc}")
            time.sleep(min(10, 2 + attempt))
    raise RuntimeError("all GitHub Models candidates failed: " + " | ".join(errors))


def extract_diff(response: str) -> str:
    fenced = re.findall(r"```(?:diff|patch)?\s*\n(.*?)```", response, flags=re.S)
    candidates = fenced + [response]
    for text in candidates:
        start = text.find("--- ")
        if start < 0:
            continue
        diff = text[start:].strip() + "\n"
        if "+++ " in diff and "@@" in diff:
            return diff
    raise RuntimeError("model response contained no unified diff")


def diff_targets(diff: str) -> set[str]:
    targets = set()
    for line in diff.splitlines():
        if line.startswith("+++ "):
            path = line[4:].strip().split("\t", 1)[0]
            if path != "/dev/null":
                targets.add(path.removeprefix("b/"))
    return targets


def apply_diff(diff: str) -> None:
    subprocess.run(
        ["git", "apply", "--check", "--whitespace=nowarn", "-"],
        cwd=ROOT,
        input=diff,
        text=True,
        check=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    subprocess.run(
        ["git", "apply", "--whitespace=nowarn", "-"],
        cwd=ROOT,
        input=diff,
        text=True,
        check=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )


def objectively_better(new: dict[str, Any], old: dict[str, Any]) -> bool:
    if new["returncode"] == 0:
        return True
    if int(new["error_headers"]) < int(old["error_headers"]):
        return True
    old_line = old.get("first_error_line")
    new_line = new.get("first_error_line")
    if isinstance(old_line, int) and isinstance(new_line, int) and new_line > old_line:
        return True
    return False


def prompt_for(
    target: Path,
    source: str,
    result: dict[str, Any],
    iteration: int,
    rejection: str = "",
) -> str:
    rel = target.relative_to(ROOT)
    errors = concise_errors(str(result["output"]))
    excerpts = source_excerpts(source, str(result["output"]))
    return f"""Repair the Lean source `{rel}` for Lean 4.33.0-rc1 and the pinned mathlib checkout.

Hard constraints:
1. Return ONLY one unified diff with paths `a/{rel}` and `b/{rel}`.
2. Do not change any existing public theorem, lemma, corollary, def, abbrev, structure, or class header.
3. Do not weaken a conclusion, add an assumption, rename a public declaration, or delete an existing import.
4. Do not use `sorry`, `admit`, a new global `axiom`, `unsafe`, `native_decide`, or `Lean.ofReduceBool`.
5. New helper declarations must be `private` and genuinely proved.
6. Prefer current mathlib APIs, explicit type annotations, `change`, `show`, `simpa only`, extensionality, and small helper lemmas.
7. Fix the first independent compiler error and nearby cascades. Do not rewrite unrelated parts of this very large file.

Iteration: {iteration}
Current result: exit={result['returncode']}, errors={result['error_headers']}, first line={result['first_error_line']}
{('Previous candidate rejection: ' + rejection) if rejection else ''}

Compiler errors:
```text
{errors}
```

Relevant source excerpts:
```lean
{excerpts}
```
"""


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--target", required=True)
    parser.add_argument("--iterations", type=int, default=8)
    parser.add_argument("--attempts-per-iteration", type=int, default=3)
    args = parser.parse_args()

    target = (ROOT / args.target).resolve()
    if ROOT not in target.parents or not target.exists():
        raise SystemExit(f"invalid target: {target}")
    rel = str(target.relative_to(ROOT))
    run_dir = OUT_ROOT / target.stem
    run_dir.mkdir(parents=True, exist_ok=True)

    source = target.read_text(encoding="utf-8")
    original_headers = declaration_headers(source)
    original_imports = imports(source)
    original_forbidden = forbidden_hits(source)
    if original_forbidden:
        raise SystemExit(f"baseline source already has forbidden executable token(s): {original_forbidden}")

    history: list[dict[str, Any]] = []
    current = compile_target(target, "initial", max_errors=100)
    current.pop("output", None)
    # Re-read the log only when preparing a prompt, keeping the JSON concise.
    history.append(dict(current))
    progress = False

    for iteration in range(1, args.iterations + 1):
        if current["returncode"] == 0:
            break
        source = target.read_text(encoding="utf-8")
        current_with_output = dict(current)
        current_with_output["output"] = Path(str(current["log"])).read_text(
            encoding="utf-8", errors="replace"
        )
        rejection = ""
        accepted = False
        for attempt in range(1, args.attempts_per_iteration + 1):
            prompt = prompt_for(target, source, current_with_output, iteration, rejection)
            prompt_path = run_dir / f"iteration-{iteration}-attempt-{attempt}.prompt.txt"
            prompt_path.write_text(prompt, encoding="utf-8")
            try:
                model, response = model_request(prompt, attempt)
                (run_dir / f"iteration-{iteration}-attempt-{attempt}.response.txt").write_text(
                    response, encoding="utf-8"
                )
                diff = extract_diff(response)
                (run_dir / f"iteration-{iteration}-attempt-{attempt}.patch").write_text(
                    diff, encoding="utf-8"
                )
                if diff_targets(diff) != {rel}:
                    raise RuntimeError(f"diff touches disallowed paths: {sorted(diff_targets(diff))}")
                before = target.read_text(encoding="utf-8")
                apply_diff(diff)
                after = target.read_text(encoding="utf-8")
                if declaration_headers(after) != original_headers:
                    raise RuntimeError("existing public declaration header fingerprint changed")
                if not original_imports.issubset(imports(after)):
                    raise RuntimeError("an existing import was removed")
                hits = forbidden_hits(after)
                if hits:
                    raise RuntimeError(f"forbidden executable token(s): {hits}")
                candidate = compile_target(
                    target, f"iteration-{iteration}-attempt-{attempt}", max_errors=100
                )
                candidate_output = candidate.pop("output", None)
                candidate["model"] = model
                candidate["iteration"] = iteration
                candidate["attempt"] = attempt
                candidate["source_sha256"] = sha256_text(after)
                if objectively_better(candidate, current):
                    history.append(dict(candidate))
                    current = candidate
                    progress = True
                    accepted = True
                    break
                target.write_text(before, encoding="utf-8")
                rejection = (
                    f"Patch compiled but did not improve: exit={candidate['returncode']}, "
                    f"errors={candidate['error_headers']}, first={candidate['first_error_line']}."
                )
            except Exception as exc:  # Every rejected model candidate is evidence, not a fatal job error.
                target.write_text(source, encoding="utf-8")
                subprocess.run(
                    ["git", "apply", "--abort"],
                    cwd=ROOT,
                    stdout=subprocess.DEVNULL,
                    stderr=subprocess.DEVNULL,
                    check=False,
                )
                rejection = str(exc)
                (run_dir / f"iteration-{iteration}-attempt-{attempt}.rejected.txt").write_text(
                    rejection + "\n", encoding="utf-8"
                )
        if not accepted:
            break

    final_source = target.read_text(encoding="utf-8")
    status = {
        "target": rel,
        "progress": progress,
        "pass": current["returncode"] == 0,
        "final_source_sha256": sha256_text(final_source),
        "final": current,
        "history": history,
    }
    status_path = run_dir / "status.json"
    status_path.write_text(json.dumps(status, indent=2), encoding="utf-8")
    print(json.dumps(status, indent=2))
    if current["returncode"] == 0:
        return 0
    return 2 if progress else 3


if __name__ == "__main__":
    raise SystemExit(main())
