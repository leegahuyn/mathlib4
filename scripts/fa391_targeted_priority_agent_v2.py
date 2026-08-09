#!/usr/bin/env python3
from __future__ import annotations

import argparse
import concurrent.futures
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
import urllib.error
import urllib.request

ROOT = Path(__file__).resolve().parents[1]
PV = ROOT / "PrimalitySheafVerification"
OUT = ROOT / "build-logs" / "fa391-targeted"
TOKEN = os.environ.get("GITHUB_TOKEN", "")
ENDPOINT = os.environ.get(
    "GITHUB_MODELS_ENDPOINT",
    "https://models.github.ai/inference/chat/completions",
)
MODELS = [
    x.strip()
    for x in os.environ.get(
        "FA391_MODELS",
        "openai/gpt-5,openai/o4-mini,openai/gpt-4.1,xai/grok-3,"
        "deepseek/DeepSeek-V3-0324,mistral-ai/Mistral-Large-2411",
    ).split(",")
    if x.strip()
]

ERROR_RE = re.compile(r"\.lean:(\d+):(\d+):\s*error:")
DECL_RE = re.compile(
    r"(?m)^(?:public\s+|private\s+|protected\s+|noncomputable\s+)*"
    r"(theorem|lemma|corollary|def|abbrev)\s+([^\s(:]+)"
)
FORBIDDEN = {
    "sorry": re.compile(r"\bsorry\b"),
    "admit": re.compile(r"\badmit\b"),
    "global_axiom": re.compile(r"(?m)^\s*(?:public\s+)?axiom\b"),
    "unsafe": re.compile(r"(?m)^\s*unsafe\b"),
    "native_decide": re.compile(r"\bnative_decide\b"),
    "Lean.ofReduceBool": re.compile(r"\bLean\.ofReduceBool\b"),
}


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(cmd: list[str], *, timeout: int = 1200, cwd: Path = ROOT) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        cmd,
        cwd=cwd,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=timeout,
        check=False,
    )


def strip_comments_strings(text: str) -> str:
    out: list[str] = []
    i = 0
    depth = 0
    string = False
    escape = False
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1
                out.extend("  ")
                i += 2
                continue
            if text.startswith("-/", i):
                depth -= 1
                out.extend("  ")
                i += 2
                continue
            out.append("\n" if text[i] == "\n" else " ")
            i += 1
            continue
        if string:
            c = text[i]
            out.append("\n" if c == "\n" else " ")
            if escape:
                escape = False
            elif c == "\\":
                escape = True
            elif c == '"':
                string = False
            i += 1
            continue
        if text.startswith("/-", i):
            depth = 1
            out.extend("  ")
            i += 2
            continue
        if text.startswith("--", i):
            while i < len(text) and text[i] != "\n":
                out.append(" ")
                i += 1
            continue
        if text[i] == '"':
            string = True
            out.append(" ")
            i += 1
            continue
        out.append(text[i])
        i += 1
    return "".join(out)


def audit_text(text: str) -> dict[str, int]:
    clean = strip_comments_strings(text)
    return {name: len(rx.findall(clean)) for name, rx in FORBIDDEN.items()}


def public_headers(text: str) -> dict[str, str]:
    matches = list(DECL_RE.finditer(text))
    result: dict[str, str] = {}
    for index, match in enumerate(matches):
        kind, name = match.group(1), match.group(2)
        if kind not in {"theorem", "lemma", "corollary", "def", "abbrev"}:
            continue
        end = matches[index + 1].start() if index + 1 < len(matches) else len(text)
        block = text[match.start():end]
        if kind in {"theorem", "lemma", "corollary"}:
            cut = re.search(r"\s*:=\s*by\b|\n\s*by\s*$", block, re.S)
            header = block[:cut.start()] if cut else block.splitlines()[0]
        else:
            cut = re.search(r"\s*:=|\n\s*where\b", block)
            header = block[:cut.start()] if cut else block.splitlines()[0]
        result[f"{kind}:{name}"] = re.sub(r"\s+", " ", header).strip()
    return result


def output_paths(path: Path, tag: str) -> tuple[Path, Path]:
    safe = path.stem.replace("_", "-")
    base = OUT / "compiled" / f"{safe}-{tag}"
    base.parent.mkdir(parents=True, exist_ok=True)
    return base.with_suffix(".olean"), base.with_suffix(".ilean")


def compile_file(path: Path, tag: str, max_errors: int = 80, timeout: int = 1500) -> dict[str, object]:
    olean, ilean = output_paths(path, tag)
    olean.unlink(missing_ok=True)
    ilean.unlink(missing_ok=True)
    cmd = [
        "lake", "env", "lean", f"-DmaxErrors={max_errors}",
        "-o", str(olean), "-i", str(ilean), str(path.relative_to(ROOT)),
    ]
    started = time.time()
    try:
        proc = run(cmd, timeout=timeout)
        output = proc.stdout
        code = proc.returncode
    except subprocess.TimeoutExpired as exc:
        output = (exc.stdout or "") + "\n[TIMEOUT]"
        code = 124
    log_path = OUT / "logs" / f"{path.stem}-{tag}.log"
    log_path.parent.mkdir(parents=True, exist_ok=True)
    log_path.write_text(output, encoding="utf-8", errors="replace")
    errors = len(ERROR_RE.findall(output))
    first = ERROR_RE.search(output)
    first_line = int(first.group(1)) if first else (10**9 if code == 0 else 0)
    return {
        "exit_code": code,
        "errors": errors,
        "first_line": first_line,
        "source_sha256": sha(path),
        "elapsed_seconds": round(time.time() - started, 3),
        "log": str(log_path.relative_to(ROOT)),
        "olean": str(olean.relative_to(ROOT)),
        "ilean": str(ilean.relative_to(ROOT)),
        "artifacts_exist": olean.exists() and ilean.exists(),
    }


def better(candidate: dict[str, object], baseline: dict[str, object]) -> bool:
    if int(candidate["exit_code"]) == 0:
        return True
    if int(candidate["first_line"]) > int(baseline["first_line"]):
        return True
    if int(candidate["first_line"]) == int(baseline["first_line"]):
        return int(candidate["errors"]) < int(baseline["errors"])
    return False


def declaration_region(text: str, line: int) -> tuple[int, int, int, int]:
    lines = text.splitlines(keepends=True)
    target = max(0, min(len(lines) - 1, line - 1))
    starts: list[int] = []
    for i, value in enumerate(lines):
        if re.match(
            r"^(?:public\s+|private\s+|protected\s+|noncomputable\s+)*"
            r"(?:theorem|lemma|corollary|def|abbrev|instance|section|namespace)\b",
            value,
        ):
            starts.append(i)
    decl_start = max((i for i in starts if i <= target), default=max(0, target - 40))
    decl_end = min((i for i in starts if i > target), default=min(len(lines), target + 100))
    context_start = max(0, decl_start - 180)
    context_end = min(len(lines), decl_end + 120)
    return decl_start, decl_end, context_start, context_end


def numbered_context(text: str, start: int, end: int) -> str:
    lines = text.splitlines()
    return "\n".join(f"{i + 1}: {lines[i]}" for i in range(start, min(end, len(lines))))


def api_search(block: str) -> str:
    words = sorted(
        set(re.findall(r"\b[A-Za-z][A-Za-z0-9_'.]{3,}\b", block)),
        key=len,
        reverse=True,
    )[:35]
    chunks: list[str] = []
    for word in words:
        proc = run(
            ["rg", "-n", "--glob", "*.lean", "--max-count", "8", "--fixed-strings", word,
             "Mathlib", "PrimalitySheafVerification"],
            timeout=20,
        )
        if proc.stdout.strip():
            chunks.append(f"## {word}\n{proc.stdout[:5000]}")
        if sum(len(x) for x in chunks) > 30000:
            break
    return "\n".join(chunks)


def extract_json(raw: str) -> dict[str, object] | None:
    raw = raw.strip()
    if raw.startswith("```"):
        raw = re.sub(r"^```(?:json)?\s*", "", raw)
        raw = re.sub(r"\s*```$", "", raw)
    try:
        value = json.loads(raw)
        return value if isinstance(value, dict) else None
    except json.JSONDecodeError:
        left = raw.find("{")
        right = raw.rfind("}")
        if left >= 0 and right > left:
            try:
                value = json.loads(raw[left:right + 1])
                return value if isinstance(value, dict) else None
            except json.JSONDecodeError:
                return None
    return None


def call_model(model: str, prompt: str) -> tuple[str, str]:
    if not TOKEN:
        return model, "ERROR: missing GITHUB_TOKEN"
    payload = {
        "model": model,
        "messages": [
            {
                "role": "system",
                "content": (
                    "You are repairing Lean 4.33.0-rc1 code against the checked-out Mathlib. "
                    "Never weaken a theorem statement or add assumptions. Never use sorry, admit, "
                    "axiom, unsafe, native_decide, or Lean.ofReduceBool. Return JSON only."
                ),
            },
            {"role": "user", "content": prompt},
        ],
        "temperature": 0.15,
        "max_tokens": 7000,
    }
    request = urllib.request.Request(
        ENDPOINT,
        data=json.dumps(payload).encode("utf-8"),
        headers={
            "Authorization": f"Bearer {TOKEN}",
            "Content-Type": "application/json",
            "Accept": "application/json",
        },
        method="POST",
    )
    try:
        with urllib.request.urlopen(request, timeout=180) as response:
            body = json.loads(response.read().decode("utf-8"))
        return model, str(body["choices"][0]["message"]["content"])
    except (urllib.error.URLError, urllib.error.HTTPError, KeyError, ValueError) as exc:
        return model, f"ERROR: {type(exc).__name__}: {exc}"


def apply_edits(text: str, payload: dict[str, object]) -> str | None:
    edits = payload.get("edits")
    if not isinstance(edits, list) or not edits:
        return None
    candidate = text
    changed = 0
    for edit in edits:
        if not isinstance(edit, dict):
            return None
        old = edit.get("old")
        new = edit.get("new")
        if not isinstance(old, str) or not isinstance(new, str) or old == new:
            return None
        if candidate.count(old) != 1:
            return None
        candidate = candidate.replace(old, new, 1)
        changed += len(old) + len(new)
    if changed > 120000:
        return None
    return candidate


def prompt_for(path: Path, metric: dict[str, object], log: str, text: str) -> str:
    first_line = int(metric["first_line"])
    ds, de, cs, ce = declaration_region(text, first_line)
    region = numbered_context(text, cs, ce)
    exact = api_search("\n".join(text.splitlines()[cs:ce]))
    return f"""
Repair the FIRST INDEPENDENT Lean error in `{path.relative_to(ROOT)}`.

Current metric:
{json.dumps(metric, indent=2)}

Compiler error window:
```text
{log[:50000]}
```

Source context with exact line numbers (the failing declaration is approximately lines {ds + 1}-{de}):
```lean
{region[:65000]}
```

Exact-name/API search results from this checkout:
```text
{exact[:30000]}
```

Return exactly one JSON object of this form:
{{
  "edits": [
    {{"old": "an exact unique source substring", "new": "its replacement"}}
  ],
  "reason": "brief technical reason"
}}

Rules:
- Make the smallest kernel-checked repair that advances the first error.
- Preserve every existing public theorem/lemma/corollary/def name, binder, assumption, and conclusion exactly.
- You may change proof bodies, local `letI`/`haveI` declarations, local instance bodies, explicit type annotations, namespace qualification, and current Mathlib API calls.
- For the line-{first_line} cluster, pay special attention to definitionally unequal NormedSpace/InnerProductSpace/Completion instances and make all terms use one coherent local instance family.
- Do not add imports unless the exact declaration is proven to exist in the checkout.
- Do not use forbidden proof escapes.
- `old` must be copied byte-for-byte from the supplied source context and should be as small as possible while remaining unique.
""".strip()


def repair_target(path: Path, rounds: int, models_per_round: int) -> tuple[bool, dict[str, object]]:
    OUT.mkdir(parents=True, exist_ok=True)
    original_headers = public_headers(path.read_text(encoding="utf-8"))
    history: list[dict[str, object]] = []
    metric = compile_file(path, "baseline", max_errors=100)
    for round_index in range(1, rounds + 1):
        if int(metric["exit_code"]) == 0:
            break
        text = path.read_text(encoding="utf-8")
        log = (ROOT / str(metric["log"])).read_text(encoding="utf-8", errors="replace")
        prompt = prompt_for(path, metric, log, text)
        selected_models = MODELS[:max(1, models_per_round)]
        with concurrent.futures.ThreadPoolExecutor(max_workers=len(selected_models)) as pool:
            responses = list(pool.map(lambda model: call_model(model, prompt), selected_models))
        best_text: str | None = None
        best_metric = metric
        round_dir = OUT / "responses" / path.stem / f"round-{round_index:02d}"
        round_dir.mkdir(parents=True, exist_ok=True)
        for candidate_index, (model, raw) in enumerate(responses, 1):
            (round_dir / f"{candidate_index:02d}-{model.replace('/', '_')}.txt").write_text(
                raw, encoding="utf-8", errors="replace"
            )
            payload = extract_json(raw)
            if payload is None:
                continue
            candidate = apply_edits(text, payload)
            if candidate is None or candidate == text:
                continue
            if public_headers(candidate) != original_headers:
                continue
            if any(audit_text(candidate).values()):
                continue
            backup = path.read_text(encoding="utf-8")
            path.write_text(candidate, encoding="utf-8")
            candidate_metric = compile_file(
                path,
                f"r{round_index:02d}-c{candidate_index:02d}",
                max_errors=100,
            )
            path.write_text(backup, encoding="utf-8")
            if better(candidate_metric, best_metric):
                best_text = candidate
                best_metric = candidate_metric
        accepted = best_text is not None
        if accepted:
            path.write_text(best_text, encoding="utf-8")
            metric = compile_file(path, f"accepted-{round_index:02d}", max_errors=140)
        history.append({
            "round": round_index,
            "accepted": accepted,
            "metric": metric,
            "source_sha256": sha(path),
        })
        (OUT / "state.json").write_text(
            json.dumps({"target": str(path.relative_to(ROOT)), "history": history}, indent=2),
            encoding="utf-8",
        )
        if not accepted:
            break
    if int(metric["exit_code"]) != 0:
        return False, metric
    verify: list[dict[str, object]] = []
    for run_index in (1, 2):
        result = compile_file(path, f"verify-{run_index}", max_errors=2000, timeout=2400)
        verify.append(result)
        if int(result["exit_code"]) != 0 or not bool(result["artifacts_exist"]):
            return False, result
    return True, {"status": "PASS_2X", "runs": verify, "source_sha256": sha(path)}


def targets() -> list[Path]:
    return [
        PV / "Mock2_FunctionalAnalysis.lean",
        PV / "Mock2_FunctionalAnalysis_Integrated.lean",
        *sorted(PV.glob("Mock3*.lean")),
        PV / "QYM.lean",
    ]


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--rounds", type=int, default=10)
    parser.add_argument("--models-per-round", type=int, default=5)
    args = parser.parse_args()
    OUT.mkdir(parents=True, exist_ok=True)
    ordered = targets()
    report: dict[str, object] = {
        "complete": False,
        "required_order": [str(p.relative_to(ROOT)) for p in ordered],
        "modules": [],
    }
    for path in ordered:
        if not path.exists():
            report["modules"].append({"module": str(path.relative_to(ROOT)), "status": "MISSING"})
            report["stage"] = str(path.relative_to(ROOT))
            break
        ok, result = repair_target(path, args.rounds, args.models_per_round)
        report["modules"].append({
            "module": str(path.relative_to(ROOT)),
            "status": "PASS_2X" if ok else "FAIL",
            "result": result,
            "source_sha256": sha(path),
        })
        if not ok:
            report["stage"] = str(path.relative_to(ROOT))
            break
    else:
        report["complete"] = True
        report["stage"] = "complete"
        (OUT / "ALL_REQUIRED_TARGETS_2X_PASS").write_text("PASS\n", encoding="utf-8")
    audit = {str(p.relative_to(ROOT)): audit_text(p.read_text(encoding="utf-8")) for p in ordered if p.exists()}
    report["forbidden_token_audit"] = audit
    if any(any(counts.values()) for counts in audit.values()):
        report["complete"] = False
        report["stage"] = "forbidden-token-audit"
        (OUT / "ALL_REQUIRED_TARGETS_2X_PASS").unlink(missing_ok=True)
    report["source_sha256"] = {str(p.relative_to(ROOT)): sha(p) for p in ordered if p.exists()}
    (OUT / "AUTHORITATIVE_STATUS.json").write_text(json.dumps(report, indent=2), encoding="utf-8")
    lines = [
        f"complete={str(report['complete']).lower()}",
        f"stage={report.get('stage')}",
    ]
    for module in report["modules"]:
        lines.append(f"{module['module']}={module['status']} sha256={module.get('source_sha256', '')}")
    (OUT / "AUTHORITATIVE_STATUS.txt").write_text("\n".join(lines) + "\n", encoding="utf-8")
    print("\n".join(lines))
    return 0 if report["complete"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
