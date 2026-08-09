#!/usr/bin/env python3
from __future__ import annotations

import argparse
import concurrent.futures
import dataclasses
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time
import urllib.error
import urllib.request
from typing import Sequence

ROOT = Path(__file__).resolve().parents[1]
PVS = ROOT / "PrimalitySheafVerification"
DEFAULT_EVIDENCE = ROOT / "build-logs" / "fa392-iterative"
MODEL_ENDPOINT = "https://models.github.ai/inference/chat/completions"

DECL_RE = re.compile(
    r"^(?:(?:noncomputable|private|protected|public|opaque)\s+)*"
    r"(?:theorem|lemma|corollary|def|abbrev|instance|structure|class|inductive)\b"
)
PUBLIC_DECL_RE = re.compile(
    r"^(?:(?:noncomputable|protected|public|opaque)\s+)*"
    r"(theorem|lemma|corollary|def|abbrev)\s+([A-Za-z0-9_'.]+)"
)
ERROR_RE = re.compile(r"\.lean:(\d+):(\d+):\s+error:")
FORBIDDEN = {
    "sorry": re.compile(r"\bsorry\b"),
    "admit": re.compile(r"\badmit\b"),
    "global_axiom": re.compile(r"(?m)^\s*(?:public\s+)?axiom\b"),
    "unsafe": re.compile(r"(?m)^\s*unsafe\b"),
    "native_decide": re.compile(r"\bnative_decide\b"),
    "Lean.ofReduceBool": re.compile(r"\bLean\.ofReduceBool\b"),
}


@dataclasses.dataclass(frozen=True)
class Metric:
    exit_code: int
    errors: int
    first_line: int
    first_column: int
    source_sha256: str
    elapsed_seconds: float

    @property
    def passed(self) -> bool:
        return self.exit_code == 0 and self.errors == 0

    def score(self) -> tuple[int, int, int]:
        if self.passed:
            return (2, 10**9, 0)
        return (1, self.first_line, -self.errors)

    def better_than(self, other: "Metric") -> bool:
        return self.score() > other.score()

    def to_json(self) -> dict[str, object]:
        return dataclasses.asdict(self) | {"passed": self.passed}


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def run(
    args: Sequence[str],
    *,
    cwd: Path = ROOT,
    input_text: str | None = None,
    timeout: int | None = None,
    env: dict[str, str] | None = None,
) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        list(args),
        cwd=cwd,
        input=input_text,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=timeout,
        env=env,
        check=False,
    )


def strip_comments_and_strings(text: str) -> str:
    out: list[str] = []
    i = 0
    depth = 0
    in_string = False
    escaped = False
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
            in_string = True
            out.append(" ")
            i += 1
            continue
        out.append(text[i])
        i += 1
    return "".join(out)


def forbidden_counts(text: str) -> dict[str, int]:
    clean = strip_comments_and_strings(text)
    return {name: len(pat.findall(clean)) for name, pat in FORBIDDEN.items()}


def declaration_headers(text: str) -> list[tuple[str, str, str]]:
    """Conservative public header fingerprint, stopping before := / where / terminal by."""
    lines = text.splitlines()
    result: list[tuple[str, str, str]] = []
    i = 0
    while i < len(lines):
        m = PUBLIC_DECL_RE.match(lines[i])
        if not m or lines[i].lstrip().startswith("private "):
            i += 1
            continue
        start = i
        buf = [lines[i]]
        while i + 1 < len(lines) and i - start < 80:
            joined = "\n".join(buf)
            if ":=" in joined or re.search(r"\bwhere\s*$", joined) or re.search(r"\bby\s*$", joined):
                break
            i += 1
            buf.append(lines[i])
        joined = "\n".join(buf)
        if ":=" in joined:
            header = joined.split(":=", 1)[0].rstrip()
        elif re.search(r"\bwhere\s*$", joined):
            header = re.sub(r"\bwhere\s*$", "", joined).rstrip()
        elif re.search(r"\bby\s*$", joined):
            header = re.sub(r"\bby\s*$", "", joined).rstrip()
        else:
            header = joined.rstrip()
        result.append((m.group(1), m.group(2), header))
        i += 1
    return result


def clean_artifacts(module_stem: str) -> None:
    rel = Path("PrimalitySheafVerification") / module_stem
    for base in (
        ROOT / ".lake" / "build" / "lib" / "lean",
        ROOT / ".lake" / "build" / "ir",
    ):
        for suffix in (".olean", ".ilean", ".c", ".o", ".trace"):
            p = base / rel.with_suffix(suffix)
            if p.exists():
                p.unlink()


def compile_file(path: Path, log_path: Path, max_errors: int = 160, timeout: int = 1500) -> Metric:
    log_path.parent.mkdir(parents=True, exist_ok=True)
    clean_artifacts(path.stem)
    started = time.monotonic()
    try:
        proc = run(
            ["lake", "env", "lean", f"-DmaxErrors={max_errors}", str(path.relative_to(ROOT))],
            timeout=timeout,
        )
        output = proc.stdout
        rc = proc.returncode
    except subprocess.TimeoutExpired as exc:
        output = (exc.stdout or "") + "\n[TIMEOUT]\n"
        rc = 124
    elapsed = time.monotonic() - started
    log_path.write_text(output, encoding="utf-8", errors="replace")
    hits = [tuple(map(int, m.groups())) for m in ERROR_RE.finditer(output)]
    if not hits:
        alt = re.findall(r":(\d+):(\d+):\s+error:", output)
        hits = [tuple(map(int, x)) for x in alt]
    first_line, first_col = hits[0] if hits else (10**9 if rc == 0 else 0, 0)
    return Metric(
        exit_code=rc,
        errors=len(hits),
        first_line=first_line,
        first_column=first_col,
        source_sha256=sha256_file(path),
        elapsed_seconds=round(elapsed, 3),
    )


def log_context(log_text: str, radius: int = 90) -> str:
    lines = log_text.splitlines()
    idx = next((i for i, line in enumerate(lines) if " error:" in line), 0)
    lo = max(0, idx - radius)
    hi = min(len(lines), idx + radius + 1)
    return "\n".join(f"{i + 1}: {lines[i]}" for i in range(lo, hi))


def declaration_bounds(lines: list[str], line_no: int) -> tuple[int, int]:
    idx = max(0, min(len(lines) - 1, line_no - 1))
    start = idx
    while start > 0 and not DECL_RE.match(lines[start]):
        start -= 1
    if not DECL_RE.match(lines[start]):
        start = max(0, idx - 180)
    end = start + 1
    while end < len(lines):
        if DECL_RE.match(lines[end]) or re.match(
            r"^(?:namespace|section|end|open|variable|universe|attribute)\b", lines[end]
        ):
            break
        end += 1
    start = max(0, start - 120)
    end = min(len(lines), end + 80)
    return start, end


def source_context(text: str, line_no: int, extra: int = 0) -> tuple[int, int, str]:
    lines = text.splitlines()
    start, end = declaration_bounds(lines, line_no)
    start = max(0, start - extra)
    end = min(len(lines), end + extra)
    rendered = "\n".join(f"{i + 1}: {lines[i]}" for i in range(start, end))
    return start + 1, end, rendered


def identifiers_from(text: str) -> list[str]:
    words = re.findall(r"\b[A-Za-z_][A-Za-z0-9_'.]{3,}\b", text)
    banned = {
        "error", "warning", "application", "type", "failed", "synthesize",
        "expected", "provided", "function", "argument", "instance", "unknown",
        "theorem", "lemma", "where", "this", "that", "have", "exact", "from",
        "with", "source", "target", "mismatch", "declaration", "unsolved",
    }
    result: list[str] = []
    for word in words:
        if word.lower() in banned or word.startswith("_"):
            continue
        if word not in result:
            result.append(word)
    return result[:24]


def exact_api_search(source_block: str, error_block: str, max_chars: int = 16000) -> str:
    identifiers = identifiers_from(error_block + "\n" + source_block)
    chunks: list[str] = []
    for ident in identifiers:
        proc = run(
            [
                "rg", "-n", "--glob", "*.lean", "--max-count", "12",
                rf"\b{re.escape(ident)}\b", "Mathlib", "PrimalitySheafVerification",
            ],
            timeout=30,
        )
        if proc.stdout.strip():
            chunks.append(f"### {ident}\n{proc.stdout[:2600]}")
        if sum(map(len, chunks)) >= max_chars:
            break
    return "\n".join(chunks)[:max_chars] or "(no exact-name hits)"


def extract_edits(content: str) -> list[tuple[str, str]]:
    edits: list[tuple[str, str]] = []
    pattern = re.compile(
        r"<EDIT>\s*<OLD>\s*(.*?)\s*</OLD>\s*<NEW>\s*(.*?)\s*</NEW>\s*</EDIT>",
        re.DOTALL,
    )
    for m in pattern.finditer(content):
        old = m.group(1)
        new = m.group(2)
        old = re.sub(r"^```(?:lean)?\s*\n", "", old)
        old = re.sub(r"\n```\s*$", "", old)
        new = re.sub(r"^```(?:lean)?\s*\n", "", new)
        new = re.sub(r"\n```\s*$", "", new)
        edits.append((old, new))
    return edits


def apply_edits(text: str, edits: Sequence[tuple[str, str]]) -> str | None:
    current = text
    for old, new in edits:
        count = current.count(old)
        if count != 1:
            return None
        current = current.replace(old, new, 1)
    return current


def model_request(model: str, prompt: str, token: str, seed: int) -> tuple[str, str]:
    body = {
        "model": model,
        "messages": [
            {
                "role": "system",
                "content": (
                    "You repair Lean 4/mathlib source. Return only exact tagged edits. "
                    "Never use sorry, admit, axioms, unsafe, native_decide, or Lean.ofReduceBool. "
                    "Never weaken or alter any existing public declaration header, theorem statement, "
                    "binder, hypothesis, or conclusion."
                ),
            },
            {"role": "user", "content": prompt},
        ],
        "max_tokens": 12000,
        "temperature": 0.15 + (seed % 3) * 0.1,
    }
    data = json.dumps(body).encode()
    req = urllib.request.Request(
        MODEL_ENDPOINT,
        data=data,
        method="POST",
        headers={
            "Authorization": f"Bearer {token}",
            "Accept": "application/vnd.github+json",
            "Content-Type": "application/json",
            "X-GitHub-Api-Version": "2022-11-28",
        },
    )
    try:
        with urllib.request.urlopen(req, timeout=240) as response:
            payload = json.loads(response.read().decode())
        return model, payload["choices"][0]["message"]["content"]
    except urllib.error.HTTPError as exc:
        if exc.code in {400, 422}:
            body.pop("temperature", None)
            req = urllib.request.Request(
                MODEL_ENDPOINT,
                data=json.dumps(body).encode(),
                method="POST",
                headers={
                    "Authorization": f"Bearer {token}",
                    "Accept": "application/vnd.github+json",
                    "Content-Type": "application/json",
                    "X-GitHub-Api-Version": "2022-11-28",
                },
            )
            try:
                with urllib.request.urlopen(req, timeout=240) as response:
                    payload = json.loads(response.read().decode())
                return model, payload["choices"][0]["message"]["content"]
            except Exception as retry_exc:
                return model, f"<ERROR>{retry_exc!r}</ERROR>"
        return model, f"<ERROR>HTTP {exc.code}: {exc.read().decode(errors='replace')[:1000]}</ERROR>"
    except Exception as exc:
        return model, f"<ERROR>{exc!r}</ERROR>"


def make_prompt(
    path: Path,
    metric: Metric,
    log_text: str,
    source_text: str,
    round_index: int,
    expanded: bool,
) -> str:
    first = metric.first_line if metric.first_line > 0 else 1
    extra = 220 if expanded else 40
    start, end, block = source_context(source_text, first, extra=extra)
    errors = log_context(log_text, radius=130 if expanded else 80)
    api = exact_api_search(block, errors)
    return f"""Repair the first independent Lean error cluster in:
{path.relative_to(ROOT)}

Current direct compiler metric:
{json.dumps(metric.to_json(), indent=2)}

Round: {round_index}
Source window: lines {start}-{end}

COMPILER CONTEXT
<ERRORS>
{errors}
</ERRORS>

CURRENT SOURCE WINDOW
<SOURCE>
{block}
</SOURCE>

EXACT-NAME SEARCH HITS FROM THIS CHECKOUT
<API_SEARCH>
{api}
</API_SEARCH>

Produce one or more exact edits in this format and nothing else:

<EDIT>
<OLD>
exact existing source text, copied byte-for-byte without line-number prefixes
</OLD>
<NEW>
replacement Lean source
</NEW>
</EDIT>

Rules:
1. OLD must occur exactly once in the current file.
2. Keep every existing public theorem/lemma/corollary/def/abbrev header byte-for-byte unchanged.
3. Do not change assumptions or conclusions. You may rewrite proof bodies and local/private helpers.
4. Prefer explicit `change`, `show`, `simpa only`, typed `letI`, and current Mathlib lemmas.
5. If typeclass instances disagree, make the intended local instance explicit and keep it coherent; do not add a global axiom.
6. No sorry/admit/unsafe/native_decide/Lean.ofReduceBool.
7. Fix the root error, not downstream cascade messages.
"""


def verify_candidate(
    path: Path,
    candidate_text: str,
    baseline_headers: list[tuple[str, str, str]],
    evidence: Path,
    label: str,
    max_errors: int,
) -> tuple[Metric | None, str]:
    if declaration_headers(candidate_text) != baseline_headers:
        return None, "public-header fingerprint changed"
    bad = forbidden_counts(candidate_text)
    if any(bad.values()):
        return None, f"forbidden tokens: {bad}"
    original = path.read_text(encoding="utf-8")
    path.write_text(candidate_text, encoding="utf-8")
    try:
        metric = compile_file(path, evidence / f"{label}.log", max_errors=max_errors)
        return metric, ""
    finally:
        path.write_text(original, encoding="utf-8")


def solve_file(
    path: Path,
    evidence: Path,
    *,
    token: str,
    models: Sequence[str],
    max_rounds: int,
    max_candidates: int,
    max_errors: int,
) -> Metric:
    evidence.mkdir(parents=True, exist_ok=True)
    current_text = path.read_text(encoding="utf-8")
    baseline_headers = declaration_headers(current_text)
    (evidence / "public-headers.sha256").write_text(
        sha256_bytes(json.dumps(baseline_headers, ensure_ascii=False).encode()) + "\n"
    )
    metric = compile_file(path, evidence / "round-000-baseline.log", max_errors=max_errors)
    history: list[dict[str, object]] = [{"round": 0, "metric": metric.to_json()}]
    (evidence / "history.json").write_text(json.dumps(history, indent=2))
    if metric.passed:
        return metric

    for round_index in range(1, max_rounds + 1):
        current_text = path.read_text(encoding="utf-8")
        current_log_path = evidence / (
            "round-000-baseline.log"
            if round_index == 1
            else f"round-{round_index - 1:03d}-accepted.log"
        )
        if not current_log_path.exists():
            accepted = sorted(evidence.glob(f"round-{round_index - 1:03d}-candidate-*.log"))
            current_log_path = accepted[-1] if accepted else evidence / "round-000-baseline.log"
        log_text = current_log_path.read_text(encoding="utf-8", errors="replace")
        expanded = round_index % 3 == 0
        prompt = make_prompt(path, metric, log_text, current_text, round_index, expanded)
        (evidence / f"round-{round_index:03d}-prompt.txt").write_text(prompt)

        jobs: list[tuple[str, int]] = []
        for seed in range(max(1, min(2, max_candidates))):
            for model in models:
                jobs.append((model, seed))
        responses: list[tuple[str, int, str]] = []
        with concurrent.futures.ThreadPoolExecutor(max_workers=min(8, len(jobs))) as pool:
            future_map = {
                pool.submit(model_request, model, prompt, token, seed): (model, seed)
                for model, seed in jobs
            }
            for future in concurrent.futures.as_completed(future_map):
                model, seed = future_map[future]
                try:
                    _, content = future.result()
                except Exception as exc:
                    content = f"<ERROR>{exc!r}</ERROR>"
                responses.append((model, seed, content))

        candidates: list[tuple[str, str]] = []
        seen_hashes: set[str] = set()
        for model, seed, content in responses:
            safe_model = re.sub(r"[^A-Za-z0-9_.-]+", "_", model)
            (evidence / f"round-{round_index:03d}-response-{safe_model}-{seed}.txt").write_text(
                content, encoding="utf-8"
            )
            edits = extract_edits(content)
            if not edits:
                continue
            candidate = apply_edits(current_text, edits)
            if candidate is None or candidate == current_text:
                continue
            digest = sha256_bytes(candidate.encode())
            if digest in seen_hashes:
                continue
            seen_hashes.add(digest)
            candidates.append((f"{safe_model}-{seed}-{digest[:10]}", candidate))
        candidates = sorted(candidates, key=lambda item: abs(len(item[1]) - len(current_text)))
        candidates = candidates[:max_candidates]

        best_metric: Metric | None = None
        best_text: str | None = None
        best_label = ""
        diagnostics: list[dict[str, object]] = []
        for idx, (label, candidate) in enumerate(candidates):
            candidate_path = evidence / f"round-{round_index:03d}-candidate-{idx:02d}.lean"
            candidate_path.write_text(candidate, encoding="utf-8")
            cand_metric, reject = verify_candidate(
                path,
                candidate,
                baseline_headers,
                evidence,
                f"round-{round_index:03d}-candidate-{idx:02d}",
                max_errors,
            )
            diagnostics.append(
                {
                    "label": label,
                    "reject": reject,
                    "metric": cand_metric.to_json() if cand_metric else None,
                    "sha256": sha256_bytes(candidate.encode()),
                }
            )
            if cand_metric and cand_metric.better_than(metric):
                if best_metric is None or cand_metric.better_than(best_metric):
                    best_metric = cand_metric
                    best_text = candidate
                    best_label = f"round-{round_index:03d}-candidate-{idx:02d}"

        (evidence / f"round-{round_index:03d}-candidates.json").write_text(
            json.dumps(diagnostics, indent=2)
        )
        if best_metric is None or best_text is None:
            history.append(
                {
                    "round": round_index,
                    "accepted": False,
                    "metric": metric.to_json(),
                    "candidate_count": len(candidates),
                }
            )
            (evidence / "history.json").write_text(json.dumps(history, indent=2))
            if len(history) >= 3 and not history[-2].get("accepted", False):
                break
            continue

        path.write_text(best_text, encoding="utf-8")
        metric = compile_file(
            path, evidence / f"round-{round_index:03d}-accepted.log", max_errors=max_errors
        )
        history.append(
            {
                "round": round_index,
                "accepted": True,
                "label": best_label,
                "metric": metric.to_json(),
            }
        )
        (evidence / "history.json").write_text(json.dumps(history, indent=2))
        (evidence / "best-source.lean").write_text(best_text, encoding="utf-8")
        if metric.passed:
            break
    return metric


def artifact_paths(path: Path) -> tuple[Path, Path]:
    rel = Path("PrimalitySheafVerification") / path.stem
    base = ROOT / ".lake" / "build" / "lib" / "lean"
    return base / rel.with_suffix(".olean"), base / rel.with_suffix(".ilean")


def verify_twice(path: Path, evidence: Path, max_errors: int = 200) -> tuple[bool, list[Metric]]:
    evidence.mkdir(parents=True, exist_ok=True)
    metrics: list[Metric] = []
    for run_index in (1, 2):
        metric = compile_file(
            path, evidence / f"direct-run-{run_index}.log", max_errors=max_errors, timeout=1800
        )
        metrics.append(metric)
        olean, ilean = artifact_paths(path)
        record = {
            "metric": metric.to_json(),
            "olean": str(olean.relative_to(ROOT)),
            "olean_exists": olean.exists(),
            "ilean": str(ilean.relative_to(ROOT)),
            "ilean_exists": ilean.exists(),
        }
        (evidence / f"direct-run-{run_index}.json").write_text(json.dumps(record, indent=2))
        if not metric.passed or not olean.exists() or not ilean.exists():
            return False, metrics
    return True, metrics


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--evidence-dir", type=Path, default=DEFAULT_EVIDENCE)
    parser.add_argument("--fa-rounds", type=int, default=12)
    parser.add_argument("--downstream-rounds", type=int, default=6)
    parser.add_argument("--max-candidates", type=int, default=4)
    parser.add_argument("--max-errors", type=int, default=180)
    args = parser.parse_args()

    token = os.environ.get("GITHUB_TOKEN", "")
    if not token:
        raise SystemExit("GITHUB_TOKEN is required")
    model_text = os.environ.get(
        "FA392_MODELS",
        "openai/gpt-5,openai/o3,openai/o4-mini,openai/gpt-4.1,"
        "xai/grok-3-mini,deepseek/DeepSeek-V3-0324,"
        "mistral-ai/Mistral-Large-2411,qwen/Qwen3-235B-A22B",
    )
    models = [x.strip() for x in model_text.split(",") if x.strip()]
    evidence = args.evidence_dir
    evidence.mkdir(parents=True, exist_ok=True)

    targets = [
        PVS / "Mock2_FunctionalAnalysis.lean",
        PVS / "Mock2_FunctionalAnalysis_Integrated.lean",
        *sorted(PVS.glob("Mock3*.lean")),
        PVS / "QYM.lean",
    ]
    audit = {str(p.relative_to(ROOT)): forbidden_counts(p.read_text()) for p in targets if p.exists()}
    (evidence / "initial-forbidden-audit.json").write_text(json.dumps(audit, indent=2))
    if any(any(v.values()) for v in audit.values()):
        raise SystemExit(f"forbidden proof escape in checked-in source: {audit}")

    summary: dict[str, object] = {
        "complete": False,
        "stage": "Mock2_FunctionalAnalysis",
        "modules": [],
    }

    fa = PVS / "Mock2_FunctionalAnalysis.lean"
    fa_metric = solve_file(
        fa,
        evidence / "Mock2_FunctionalAnalysis",
        token=token,
        models=models,
        max_rounds=args.fa_rounds,
        max_candidates=args.max_candidates,
        max_errors=args.max_errors,
    )
    summary["fa_solver_metric"] = fa_metric.to_json()
    if not fa_metric.passed:
        summary["reason"] = "FA solver did not reach exit code 0"
        (evidence / "FINAL_STATUS.json").write_text(json.dumps(summary, indent=2))
        return 2
    ok, metrics = verify_twice(fa, evidence / "Mock2_FunctionalAnalysis" / "two-pass")
    summary["modules"].append(
        {"module": fa.name, "status": "PASS_2X" if ok else "FAIL", "runs": [m.to_json() for m in metrics]}
    )
    if not ok:
        summary["reason"] = "FA failed independent two-pass verification"
        (evidence / "FINAL_STATUS.json").write_text(json.dumps(summary, indent=2))
        return 3

    ordered_downstream = [
        PVS / "Mock2_FunctionalAnalysis_Integrated.lean",
        *sorted(PVS.glob("Mock3*.lean")),
        PVS / "QYM.lean",
    ]
    for target in ordered_downstream:
        if not target.exists():
            continue
        summary["stage"] = target.name
        initial = compile_file(target, evidence / target.stem / "initial.log", max_errors=args.max_errors)
        if not initial.passed:
            final_metric = solve_file(
                target,
                evidence / target.stem,
                token=token,
                models=models,
                max_rounds=args.downstream_rounds,
                max_candidates=args.max_candidates,
                max_errors=args.max_errors,
            )
        else:
            final_metric = initial
        if not final_metric.passed:
            summary["modules"].append(
                {"module": target.name, "status": "FAIL", "metric": final_metric.to_json()}
            )
            summary["reason"] = f"{target.name} solver did not reach exit code 0"
            (evidence / "FINAL_STATUS.json").write_text(json.dumps(summary, indent=2))
            return 4
        ok, metrics = verify_twice(target, evidence / target.stem / "two-pass")
        summary["modules"].append(
            {
                "module": target.name,
                "status": "PASS_2X" if ok else "FAIL",
                "runs": [m.to_json() for m in metrics],
            }
        )
        if not ok:
            summary["reason"] = f"{target.name} failed independent two-pass verification"
            (evidence / "FINAL_STATUS.json").write_text(json.dumps(summary, indent=2))
            return 5

    final_audit = {str(p.relative_to(ROOT)): forbidden_counts(p.read_text()) for p in targets if p.exists()}
    (evidence / "FINAL_FORBIDDEN_AUDIT.json").write_text(json.dumps(final_audit, indent=2))
    if any(any(v.values()) for v in final_audit.values()):
        summary["reason"] = "final forbidden-token audit failed"
        (evidence / "FINAL_STATUS.json").write_text(json.dumps(summary, indent=2))
        return 6

    summary["complete"] = True
    summary["stage"] = "complete"
    summary["status"] = "SUCCESS_ALL_REQUIRED_TARGETS_2X_PASS"
    summary["sources"] = {
        str(p.relative_to(ROOT)): sha256_file(p) for p in targets if p.exists()
    }
    (evidence / "FINAL_STATUS.json").write_text(json.dumps(summary, indent=2))
    (evidence / "ALL_REQUIRED_TARGETS_2X_PASS").write_text(
        "SUCCESS_ALL_REQUIRED_TARGETS_2X_PASS\n"
    )
    print(json.dumps(summary, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
