from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time
import urllib.error
import urllib.request
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
PSV = ROOT / "PrimalitySheafVerification"
OUTDIR = ROOT / ".lake" / "build" / "lib" / "lean" / "PrimalitySheafVerification"
LOGDIR = ROOT / "build-evidence" / "bounded-agent-logs"
DIAGNOSTIC = ROOT / "build-evidence" / "bounded-agent-latest.json"
PASS_EVIDENCE = ROOT / "build-evidence" / "mock2-advanced-functional-qym-pass.json"
TOKEN = os.environ.get("GITHUB_TOKEN", "")
BRANCH = os.environ.get("BRANCH", "fix/primality-sheaf-clean-build")
MODEL_ENDPOINT = "https://models.github.ai/inference/chat/completions"
CATALOG_ENDPOINT = "https://models.github.ai/catalog/models"

TARGETS = [
    "Mock2_Advanced",
    "Mock2_FunctionalAnalysis",
    "QYM",
]
CHAIN = [
    "Mock2",
    "Mock2_Advanced",
    "Mock2_FunctionalAnalysis",
    "Mock2_FunctionalAnalysis_Integrated",
    "QYM",
]
BANNED = {
    "sorry": re.compile(r"\bsorry\b"),
    "admit": re.compile(r"\badmit\b"),
    "line_start_axiom": re.compile(r"(?m)^\s*axiom\b"),
    "unsafe": re.compile(r"\bunsafe\b"),
    "native_decide": re.compile(r"\bnative_decide\b"),
    "Lean.ofReduceBool": re.compile(r"\bLean\.ofReduceBool\b"),
    "by_contra!": re.compile(r"\bby_contra!\b"),
    "placeholder": re.compile(r"\bplaceholder\b"),
}
DECL_RE = re.compile(
    r"(?m)^\s*(?:noncomputable\s+)?(?:private\s+|protected\s+|local\s+)?"
    r"(theorem|lemma|def|abbrev|structure|class|inductive)\s+([^\s(:{]+)"
)
IMPORT_RE = re.compile(r"(?m)^\s*(?:public\s+)?import\s+.+$")
LOCATION_RE = re.compile(
    r"(?m)^(?P<path>[^\n]+?\.lean):(?P<line>\d+):(?P<col>\d+):\s*error:\s*(?P<msg>.*)$"
)


def run(
    args: list[str],
    *,
    cwd: Path = ROOT,
    check: bool = True,
    capture: bool = True,
    timeout: int | None = None,
) -> subprocess.CompletedProcess[str]:
    print("+", " ".join(args), flush=True)
    cp = subprocess.run(
        args,
        cwd=cwd,
        text=True,
        stdout=subprocess.PIPE if capture else None,
        stderr=subprocess.STDOUT if capture else None,
        timeout=timeout,
    )
    if capture and cp.stdout:
        print(cp.stdout, flush=True)
    if check and cp.returncode != 0:
        raise RuntimeError(f"command failed ({cp.returncode}): {' '.join(args)}")
    return cp


def sha256(path: Path) -> str | None:
    if not path.is_file():
        return None
    return hashlib.sha256(path.read_bytes()).hexdigest()


def strip_comments_and_strings(src: str) -> str:
    out: list[str] = []
    i = 0
    depth = 0
    in_string = False
    escaped = False
    while i < len(src):
        if depth:
            if src.startswith("/-", i):
                depth += 1
                out.extend("  ")
                i += 2
            elif src.startswith("-/", i):
                depth -= 1
                out.extend("  ")
                i += 2
            else:
                out.append("\n" if src[i] == "\n" else " ")
                i += 1
            continue
        if in_string:
            ch = src[i]
            out.append("\n" if ch == "\n" else " ")
            if escaped:
                escaped = False
            elif ch == "\\":
                escaped = True
            elif ch == '"':
                in_string = False
            i += 1
            continue
        if src.startswith("/-", i):
            depth = 1
            out.extend("  ")
            i += 2
        elif src.startswith("--", i):
            while i < len(src) and src[i] != "\n":
                out.append(" ")
                i += 1
        elif src[i] == '"':
            in_string = True
            out.append(" ")
            i += 1
        else:
            out.append(src[i])
            i += 1
    if depth or in_string:
        raise RuntimeError("unterminated comment or string")
    return "".join(out)


def trust_counts(src: str) -> dict[str, int]:
    code = strip_comments_and_strings(src)
    return {name: len(pattern.findall(code)) for name, pattern in BANNED.items()}


def declaration_names(src: str) -> list[tuple[str, str]]:
    code = strip_comments_and_strings(src)
    return DECL_RE.findall(code)


def imports(src: str) -> list[str]:
    code = strip_comments_and_strings(src)
    return [m.group(0).strip() for m in IMPORT_RE.finditer(code)]


def remove_artifacts(module: str) -> None:
    OUTDIR.mkdir(parents=True, exist_ok=True)
    for suffix in (".olean", ".ilean", ".olean.private"):
        (OUTDIR / f"{module}{suffix}").unlink(missing_ok=True)


def compile_module(module: str, label: str) -> dict[str, Any]:
    remove_artifacts(module)
    LOGDIR.mkdir(parents=True, exist_ok=True)
    source = PSV / f"{module}.lean"
    log_path = LOGDIR / f"{module}-{label}.log"
    args = [
        "lake",
        "env",
        "lean",
        str(source.relative_to(ROOT)),
        "-o",
        str((OUTDIR / f"{module}.olean").relative_to(ROOT)),
        "-i",
        str((OUTDIR / f"{module}.ilean").relative_to(ROOT)),
    ]
    cp = run(args, check=False, timeout=7200)
    text = cp.stdout or ""
    log_path.write_text(text, encoding="utf-8")
    locations = list(LOCATION_RE.finditer(text))
    errors = [m.group(0).strip() for m in locations]
    if not errors:
        errors = [line.strip() for line in text.splitlines() if "error:" in line]
    warnings = [line.strip() for line in text.splitlines() if "warning:" in line]
    return {
        "module": module,
        "label": label,
        "exit_code": cp.returncode,
        "error_count": len(errors),
        "warning_count": len(warnings),
        "errors": errors,
        "log": text,
        "log_path": str(log_path.relative_to(ROOT)),
        "olean_exists": (OUTDIR / f"{module}.olean").is_file(),
        "ilean_exists": (OUTDIR / f"{module}.ilean").is_file(),
        "olean_sha256": sha256(OUTDIR / f"{module}.olean"),
        "ilean_sha256": sha256(OUTDIR / f"{module}.ilean"),
    }


def compile_prefix(target: str, label: str) -> dict[str, Any]:
    index = CHAIN.index(target)
    result: dict[str, Any] | None = None
    for module in CHAIN[: index + 1]:
        result = compile_module(module, f"{label}-{module}")
        if result["exit_code"] != 0:
            return result
    assert result is not None
    return result


def error_rank(result: dict[str, Any]) -> tuple[int, int, int]:
    if result["exit_code"] == 0:
        return (0, 0, 0)
    first_line = 0
    match = LOCATION_RE.search(result["log"])
    if match:
        first_line = int(match.group("line"))
    # Fewer errors is better; for equal counts, a later first error is better.
    return (1, int(result["error_count"]), -first_line)


def extract_error_blocks(log: str, limit: int = 12) -> list[dict[str, Any]]:
    matches = list(LOCATION_RE.finditer(log))
    blocks: list[dict[str, Any]] = []
    seen: set[str] = set()
    for idx, match in enumerate(matches):
        start = match.start()
        end = matches[idx + 1].start() if idx + 1 < len(matches) else min(len(log), start + 5000)
        block = log[start:end].strip()
        normalized = re.sub(r"\s+", " ", block)
        if normalized in seen:
            continue
        seen.add(normalized)
        blocks.append(
            {
                "path": match.group("path"),
                "line": int(match.group("line")),
                "column": int(match.group("col")),
                "message": match.group("msg"),
                "block": block[:5000],
            }
        )
        if len(blocks) >= limit:
            break
    if not blocks:
        for line in log.splitlines():
            if "error:" in line:
                blocks.append({"path": "", "line": 0, "column": 0, "message": line, "block": line})
                if len(blocks) >= limit:
                    break
    return blocks


def source_context(path: Path, line: int, radius: int = 45) -> str:
    lines = path.read_text(encoding="utf-8").splitlines()
    lo = max(1, line - radius)
    hi = min(len(lines), line + radius)
    return "\n".join(f"{i:06d}: {lines[i - 1]}" for i in range(lo, hi + 1))


def symbol_search(error_text: str, limit: int = 20) -> str:
    symbols = re.findall(r"`([^`\n]{2,100})`", error_text)
    symbols += re.findall(r"unknown (?:constant|identifier) '([^']+)'", error_text)
    out: list[str] = []
    seen: set[str] = set()
    for symbol in symbols:
        symbol = symbol.strip()
        if not re.fullmatch(r"[A-Za-z0-9_.'«»]+", symbol) or symbol in seen:
            continue
        seen.add(symbol)
        cp = run(
            ["rg", "-n", "-F", "--glob", "*.lean", "--", symbol, "Mathlib", "PrimalitySheafVerification"],
            check=False,
            timeout=60,
        )
        hits = (cp.stdout or "").splitlines()[:12]
        if hits:
            out.append(f"## {symbol}\n" + "\n".join(hits))
        if len(out) >= limit:
            break
    return "\n\n".join(out)[:20000]


def choose_model() -> str:
    requested = os.environ.get("GITHUB_MODELS_MODEL")
    if requested:
        return requested
    if not TOKEN:
        raise RuntimeError("GITHUB_TOKEN is missing")
    req = urllib.request.Request(
        CATALOG_ENDPOINT,
        headers={
            "Authorization": f"Bearer {TOKEN}",
            "Accept": "application/vnd.github+json",
            "X-GitHub-Api-Version": "2022-11-28",
        },
    )
    try:
        with urllib.request.urlopen(req, timeout=60) as response:
            catalog = json.load(response)
        if isinstance(catalog, dict):
            catalog = catalog.get("models", catalog.get("data", []))
        ids: list[str] = []
        for item in catalog if isinstance(catalog, list) else []:
            if isinstance(item, dict):
                value = item.get("id") or item.get("name")
                if isinstance(value, str):
                    ids.append(value)
        preferences = (
            "openai/gpt-5",
            "openai/gpt-4.1",
            "openai/gpt-4o",
            "deepseek/deepseek-r1",
        )
        for prefix in preferences:
            exact = [model for model in ids if model == prefix]
            if exact:
                return exact[0]
            starts = [model for model in ids if model.startswith(prefix)]
            if starts:
                return sorted(starts)[-1]
    except Exception as exc:
        print(f"catalog lookup failed: {exc!r}", flush=True)
    return "openai/gpt-4.1"


def call_model(model: str, system: str, user: str, label: str) -> dict[str, Any]:
    if not TOKEN:
        raise RuntimeError("GITHUB_TOKEN is missing")
    payload = {
        "model": model,
        "messages": [
            {"role": "system", "content": system},
            {"role": "user", "content": user},
        ],
        "temperature": 0.1,
        "max_tokens": 7000,
        "response_format": {"type": "json_object"},
    }
    request = urllib.request.Request(
        MODEL_ENDPOINT,
        data=json.dumps(payload).encode("utf-8"),
        method="POST",
        headers={
            "Authorization": f"Bearer {TOKEN}",
            "Content-Type": "application/json",
            "Accept": "application/json",
        },
    )
    raw = ""
    for attempt in range(1, 5):
        try:
            with urllib.request.urlopen(request, timeout=300) as response:
                raw = response.read().decode("utf-8")
            break
        except urllib.error.HTTPError as exc:
            body = exc.read().decode("utf-8", errors="replace")
            print(f"model HTTP error attempt {attempt}: {exc.code} {body[:1000]}", flush=True)
            if exc.code not in {408, 429, 500, 502, 503, 504} or attempt == 4:
                raise
            time.sleep(15 * attempt)
        except Exception:
            if attempt == 4:
                raise
            time.sleep(15 * attempt)
    LOGDIR.mkdir(parents=True, exist_ok=True)
    (LOGDIR / f"model-{label}-raw.json").write_text(raw, encoding="utf-8")
    envelope = json.loads(raw)
    content = envelope["choices"][0]["message"]["content"]
    if not isinstance(content, str):
        raise RuntimeError("model content was not text")
    content = content.strip()
    if content.startswith("```"):
        content = re.sub(r"^```(?:json)?\s*", "", content)
        content = re.sub(r"\s*```$", "", content)
    result = json.loads(content)
    (LOGDIR / f"model-{label}-parsed.json").write_text(
        json.dumps(result, ensure_ascii=False, indent=2) + "\n", encoding="utf-8"
    )
    return result


def plan_prompt(module: str, result: dict[str, Any]) -> str:
    source = PSV / f"{module}.lean"
    blocks = extract_error_blocks(result["log"])
    contexts: list[str] = []
    for block in blocks:
        path = Path(block["path"])
        if not path.is_absolute():
            path = ROOT / path
        if not path.is_file():
            path = source
        contexts.append(
            f"### Diagnostic\n{block['block']}\n\n"
            f"### Source context\n{source_context(path, int(block['line']) or 1)}"
        )
    diagnostics = "\n\n".join(contexts)[:70000]
    searches = symbol_search(result["log"])
    return f"""Repair the Lean 4 module `{source.relative_to(ROOT)}` for the pinned repository.

Hard constraints:
- Do not change theorem, lemma, definition, structure, class, or inductive statements.
- Do not delete proof content or imports.
- Do not add assumptions or weaken conclusions.
- Never use sorry, admit, axiom, unsafe, native_decide, Lean.ofReduceBool, by_contra!, or placeholders.
- Prefer current Mathlib API lemmas, explicit universes, exact typeclass paths, `simpa`, `change`, `rw`, or explicit arguments.
- Return at most 8 exact textual replacements and change only this target file.
- Every `old` string must be copied byte-for-byte from a displayed source context and should occur exactly once.
- Do not include markdown fences. Return JSON only.

Required JSON schema:
{{
  "diagnosis": "brief technical diagnosis",
  "edits": [
    {{"old": "exact existing text", "new": "replacement text", "reason": "why it typechecks"}}
  ]
}}

Current compile result: exit={result['exit_code']}, errors={result['error_count']}.

{diagnostics}

Repository symbol search:
{searches or '(no focused symbol hits)'}
"""


def critic_prompt(module: str, result: dict[str, Any], plan: dict[str, Any]) -> str:
    source = PSV / f"{module}.lean"
    return f"""You are the strict verification agent for a Lean 4 repair plan.
Review the proposed exact replacements against the diagnostics and constraints.
Reject any theorem-statement change, import deletion/change, hidden assumption,
proof escape, unsupported namespace guess, or non-exact source text.
When a repair is sound, return the same edits. When it is unsound, either return
corrected exact replacements or an empty edit list. JSON only, no markdown.

Schema:
{{"approved": true, "analysis": "...", "edits": [{{"old":"...","new":"...","reason":"..."}}]}}

Target: {source.relative_to(ROOT)}
Compile errors: {json.dumps(extract_error_blocks(result['log']), ensure_ascii=False)[:40000]}
Planner proposal: {json.dumps(plan, ensure_ascii=False)[:50000]}
"""


def validate_and_apply(module: str, proposal: dict[str, Any]) -> tuple[bool, str]:
    path = PSV / f"{module}.lean"
    before = path.read_text(encoding="utf-8")
    before_decls = declaration_names(before)
    before_imports = imports(before)
    edits = proposal.get("edits", [])
    if not isinstance(edits, list) or not 1 <= len(edits) <= 8:
        return False, "edit list must contain 1..8 entries"
    after = before
    for index, edit in enumerate(edits, start=1):
        if not isinstance(edit, dict):
            return False, f"edit {index} is not an object"
        old = edit.get("old")
        new = edit.get("new")
        if not isinstance(old, str) or not isinstance(new, str) or not old:
            return False, f"edit {index} has invalid old/new"
        if len(old) > 20000 or len(new) > 20000:
            return False, f"edit {index} is too large"
        if any(pattern.search(strip_comments_and_strings(new)) for pattern in BANNED.values()):
            return False, f"edit {index} introduces a forbidden token"
        if IMPORT_RE.search(old) or IMPORT_RE.search(new):
            return False, f"edit {index} changes an import"
        # Declaration headers must not be directly replaced. Local instance
        # repairs remain allowed because `instance` is intentionally excluded.
        if DECL_RE.search(strip_comments_and_strings(old)) or DECL_RE.search(strip_comments_and_strings(new)):
            return False, f"edit {index} touches a declaration header"
        count = after.count(old)
        if count != 1:
            return False, f"edit {index} old text occurs {count} times"
        after = after.replace(old, new, 1)
    if declaration_names(after) != before_decls:
        return False, "declaration name ledger changed"
    if imports(after) != before_imports:
        return False, "import ledger changed"
    counts = trust_counts(after)
    if any(counts.values()):
        return False, f"trust scan failed: {counts}"
    before_lines = before.splitlines()
    after_lines = after.splitlines()
    if abs(len(after_lines) - len(before_lines)) > 250:
        return False, "line-count delta exceeds bound"
    path.write_text(after, encoding="utf-8")
    return True, "applied"


def repair_target(model: str, module: str, max_iterations: int = 6) -> dict[str, Any]:
    history: list[dict[str, Any]] = []
    result = compile_prefix(module, "initial")
    if result["exit_code"] == 0:
        return {"module": module, "status": "already-pass", "history": history, "result": result}
    for iteration in range(1, max_iterations + 1):
        path = PSV / f"{module}.lean"
        before = path.read_text(encoding="utf-8")
        before_rank = error_rank(result)
        planner = call_model(
            model,
            "You are a Lean 4 and current Mathlib proof repair specialist. Follow the JSON schema exactly.",
            plan_prompt(module, result),
            f"{module}-iter{iteration}-planner",
        )
        critic = call_model(
            model,
            "You are an adversarial Lean 4 proof-review agent. Return strict JSON only.",
            critic_prompt(module, result, planner),
            f"{module}-iter{iteration}-critic",
        )
        proposal = critic if critic.get("edits") else planner
        applied, reason = validate_and_apply(module, proposal)
        entry: dict[str, Any] = {
            "iteration": iteration,
            "before_rank": before_rank,
            "planner": planner,
            "critic": critic,
            "applied": applied,
            "validation": reason,
        }
        if not applied:
            history.append(entry)
            continue
        candidate = compile_prefix(module, f"iter{iteration}")
        entry["after_rank"] = error_rank(candidate)
        entry["after_exit"] = candidate["exit_code"]
        entry["after_errors"] = candidate["error_count"]
        if candidate["exit_code"] == 0:
            history.append(entry)
            return {"module": module, "status": "repaired", "history": history, "result": candidate}
        if error_rank(candidate) >= before_rank:
            path.write_text(before, encoding="utf-8")
            entry["reverted"] = True
            history.append(entry)
            result = compile_prefix(module, f"iter{iteration}-reverted")
        else:
            entry["reverted"] = False
            history.append(entry)
            result = candidate
    return {"module": module, "status": "failed", "history": history, "result": result}


def final_gate() -> tuple[bool, dict[str, Any]]:
    data: dict[str, Any] = {
        "commit_before": run(["git", "rev-parse", "HEAD"]).stdout.strip(),
        "toolchain": (ROOT / "lean-toolchain").read_text().strip(),
        "passes": {},
        "trust": {},
    }
    for module in CHAIN:
        source = PSV / f"{module}.lean"
        if not source.is_file():
            data["passes"][module] = {"missing_source": True}
            return False, data
        counts = trust_counts(source.read_text(encoding="utf-8"))
        data["trust"][module] = counts
        if any(counts.values()):
            return False, data
    for pass_number in (1, 2):
        for module in CHAIN:
            result = compile_module(module, f"final-pass{pass_number}")
            data["passes"].setdefault(module, []).append(
                {key: result[key] for key in (
                    "exit_code", "error_count", "warning_count", "olean_exists", "ilean_exists",
                    "olean_sha256", "ilean_sha256", "log_path"
                )}
            )
            if result["exit_code"] != 0 or result["error_count"] != 0:
                return False, data
            if not result["olean_exists"] or not result["ilean_exists"]:
                return False, data
            if re.search(r"sorryAx|maximum number of errors|PANIC|segmentation fault|stack overflow|missing object file", result["log"], re.I):
                return False, data
    data["sources"] = {
        module: {
            "sha256": sha256(PSV / f"{module}.lean"),
            "lines": len((PSV / f"{module}.lean").read_text(encoding="utf-8").splitlines()),
        }
        for module in CHAIN
    }
    return True, data


def write_diagnostic(payload: dict[str, Any]) -> None:
    DIAGNOSTIC.parent.mkdir(parents=True, exist_ok=True)
    DIAGNOSTIC.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def remote_head() -> str:
    cp = run(["git", "ls-remote", "origin", f"refs/heads/{BRANCH}"])
    return cp.stdout.split()[0]


def commit_and_push(paths: list[Path], message: str) -> None:
    trigger = run(["git", "rev-parse", "HEAD"]).stdout.strip()
    remote = remote_head()
    print(f"trigger_head={trigger}\nremote_head={remote}", flush=True)
    if trigger != remote:
        raise RuntimeError("branch moved; refusing to overwrite concurrent work")
    run(["git", "config", "user.name", "github-actions[bot]"])
    run(["git", "config", "user.email", "41898282+github-actions[bot]@users.noreply.github.com"])
    run(["git", "add", *[str(path.relative_to(ROOT)) for path in paths]])
    staged = run(["git", "diff", "--cached", "--name-only"]).stdout.splitlines()
    allowed = {str(path.relative_to(ROOT)) for path in paths}
    if not staged or any(path not in allowed for path in staged):
        raise RuntimeError(f"unexpected staged files: {staged}")
    run(["git", "commit", "-m", message])
    run(["git", "push", "origin", f"HEAD:{BRANCH}"], capture=False)


def main() -> int:
    os.chdir(ROOT)
    LOGDIR.mkdir(parents=True, exist_ok=True)
    model = choose_model()
    print(f"selected model: {model}", flush=True)
    start_decls = {
        module: declaration_names((PSV / f"{module}.lean").read_text(encoding="utf-8"))
        for module in TARGETS
    }
    start_imports = {
        module: imports((PSV / f"{module}.lean").read_text(encoding="utf-8"))
        for module in TARGETS
    }
    repair_results: list[dict[str, Any]] = []
    try:
        for module in TARGETS:
            result = repair_target(model, module)
            repair_results.append(result)
            write_diagnostic({"model": model, "repair_results": repair_results})
            if result["status"] == "failed":
                print(f"bounded repair failed at {module}", flush=True)
                return 2
        for module in TARGETS:
            src = (PSV / f"{module}.lean").read_text(encoding="utf-8")
            if declaration_names(src) != start_decls[module]:
                raise RuntimeError(f"declaration ledger changed for {module}")
            if imports(src) != start_imports[module]:
                raise RuntimeError(f"import ledger changed for {module}")
        passed, evidence = final_gate()
        payload = {"model": model, "repair_results": repair_results, "final_gate": evidence, "overall_pass": passed}
        write_diagnostic(payload)
        if not passed:
            return 3
        PASS_EVIDENCE.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
        changed_sources = [PSV / f"{module}.lean" for module in TARGETS]
        changed_sources = [path for path in changed_sources if run(["git", "diff", "--quiet", "--", str(path.relative_to(ROOT))], check=False).returncode != 0]
        commit_and_push(changed_sources + [DIAGNOSTIC, PASS_EVIDENCE], "fix: complete bounded repair of Mock2 Advanced FunctionalAnalysis and QYM")
        return 0
    except Exception as exc:
        payload = {
            "model": model,
            "repair_results": repair_results,
            "exception": repr(exc),
            "overall_pass": False,
        }
        write_diagnostic(payload)
        print(json.dumps(payload, ensure_ascii=False, indent=2), flush=True)
        return 4


if __name__ == "__main__":
    raise SystemExit(main())
