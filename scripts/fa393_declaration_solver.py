#!/usr/bin/env python3
from __future__ import annotations

import argparse
import concurrent.futures
import importlib.util
import json
import os
from pathlib import Path
import re
import urllib.error
import urllib.request

ROOT = Path(__file__).resolve().parents[1]
HELPER_PATH = ROOT / "scripts" / "fa392_iterative_solver.py"
spec = importlib.util.spec_from_file_location("fa392_helper", HELPER_PATH)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot import {HELPER_PATH}")
H = importlib.util.module_from_spec(spec)
spec.loader.exec_module(H)

FA = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
EVIDENCE = ROOT / "build-logs" / "fa393-declaration"
ENDPOINT = "https://models.github.ai/inference/chat/completions"


def top_level_decl_indices(lines: list[str]) -> list[int]:
    return [i for i, line in enumerate(lines) if H.DECL_RE.match(line)]


def replacement_slice(text: str, line_no: int, previous: int = 2) -> tuple[int, int, str]:
    lines = text.splitlines(keepends=True)
    decls = top_level_decl_indices([line.rstrip("\n") for line in lines])
    idx = max(0, line_no - 1)
    prior = [d for d in decls if d <= idx]
    if prior:
        current_start = prior[-1]
        pos = decls.index(current_start)
        start_line = decls[max(0, pos - previous)]
        end_line = decls[pos + 1] if pos + 1 < len(decls) else len(lines)
    else:
        start_line = max(0, idx - 180)
        end_line = min(len(lines), idx + 220)
    start_char = sum(len(x) for x in lines[:start_line])
    end_char = sum(len(x) for x in lines[:end_line])
    return start_char, end_char, text[start_char:end_char]


def model_call(model: str, prompt: str, token: str, seed: int) -> tuple[str, str]:
    body = {
        "model": model,
        "messages": [
            {
                "role": "system",
                "content": (
                    "You are a Lean 4 and Mathlib proof repair expert. Return only one "
                    "<REPLACEMENT> block containing compilable Lean source. Preserve every "
                    "existing public declaration header byte-for-byte. Never use sorry, admit, "
                    "axioms, unsafe, native_decide, or Lean.ofReduceBool."
                ),
            },
            {"role": "user", "content": prompt},
        ],
        "max_tokens": 16000,
        "temperature": 0.1 + 0.1 * (seed % 3),
    }
    request = urllib.request.Request(
        ENDPOINT,
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
        with urllib.request.urlopen(request, timeout=300) as response:
            payload = json.loads(response.read().decode())
        return model, payload["choices"][0]["message"]["content"]
    except urllib.error.HTTPError as exc:
        if exc.code in {400, 422}:
            body.pop("temperature", None)
            request = urllib.request.Request(
                ENDPOINT,
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
                with urllib.request.urlopen(request, timeout=300) as response:
                    payload = json.loads(response.read().decode())
                return model, payload["choices"][0]["message"]["content"]
            except Exception as retry_exc:
                return model, f"<ERROR>{retry_exc!r}</ERROR>"
        return model, f"<ERROR>HTTP {exc.code}: {exc.read().decode(errors='replace')[:1000]}</ERROR>"
    except Exception as exc:
        return model, f"<ERROR>{exc!r}</ERROR>"


def extract_replacement(content: str) -> str | None:
    match = re.search(r"<REPLACEMENT>\s*(.*?)\s*</REPLACEMENT>", content, re.DOTALL)
    if not match:
        return None
    value = match.group(1)
    value = re.sub(r"^```(?:lean)?\s*\n", "", value)
    value = re.sub(r"\n```\s*$", "", value)
    if value and not value.endswith("\n"):
        value += "\n"
    return value


def prompt_for(metric, log_text: str, source_text: str, round_index: int) -> tuple[str, int, int]:
    line_no = metric.first_line if metric.first_line > 0 else 1
    start, end, block = replacement_slice(source_text, line_no, previous=3 if round_index % 2 == 0 else 2)
    errors = H.log_context(log_text, radius=140)
    api = H.exact_api_search(block, errors, max_chars=22000)
    prompt = f"""The direct Lean compiler fails in:
PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean

Current metric:
{json.dumps(metric.to_json(), indent=2)}

Replace the exact contiguous source slice below with a corrected slice. It contains the
failing declaration and nearby local instance/helper roots. The replacement may alter
proof bodies, private helpers, and local instances, but every existing public
theorem/lemma/corollary/def/abbrev header must remain byte-for-byte identical.

<COMPILER>
{errors}
</COMPILER>

<EXACT_SOURCE_SLICE>
{block}
</EXACT_SOURCE_SLICE>

<API_SEARCH>
{api}
</API_SEARCH>

Return exactly:
<REPLACEMENT>
corrected Lean source for the entire exact slice
</REPLACEMENT>

No markdown. No explanation. No sorry/admit/axiom/unsafe/native_decide/Lean.ofReduceBool.
Fix the earliest independent error, not downstream cascades. Prefer explicit types,
`letI`, `change`, `show`, and `simpa only` over broad automation.
"""
    return prompt, start, end


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--rounds", type=int, default=10)
    parser.add_argument("--candidates", type=int, default=6)
    parser.add_argument("--max-errors", type=int, default=180)
    args = parser.parse_args()

    token = os.environ.get("GITHUB_TOKEN", "")
    if not token:
        raise SystemExit("GITHUB_TOKEN is required")
    models = [
        x.strip()
        for x in os.environ.get(
            "FA393_MODELS",
            "openai/gpt-5,openai/o3,openai/o4-mini,openai/gpt-4.1,"
            "xai/grok-3-mini,deepseek/DeepSeek-V3-0324,"
            "mistral-ai/Mistral-Large-2411,qwen/Qwen3-235B-A22B",
        ).split(",")
        if x.strip()
    ]
    EVIDENCE.mkdir(parents=True, exist_ok=True)
    baseline_headers = H.declaration_headers(FA.read_text(encoding="utf-8"))
    metric = H.compile_file(FA, EVIDENCE / "round-000-baseline.log", max_errors=args.max_errors)
    history = [{"round": 0, "metric": metric.to_json()}]
    (EVIDENCE / "history.json").write_text(json.dumps(history, indent=2))
    if metric.passed:
        return 0

    for round_index in range(1, args.rounds + 1):
        source = FA.read_text(encoding="utf-8")
        log_path = EVIDENCE / (
            "round-000-baseline.log" if round_index == 1 else f"round-{round_index - 1:03d}-accepted.log"
        )
        if not log_path.exists():
            log_path = EVIDENCE / "round-000-baseline.log"
        log_text = log_path.read_text(encoding="utf-8", errors="replace")
        prompt, start, end = prompt_for(metric, log_text, source, round_index)
        (EVIDENCE / f"round-{round_index:03d}-prompt.txt").write_text(prompt)

        jobs = [(model, seed) for model in models for seed in range(2)]
        responses: list[tuple[str, int, str]] = []
        with concurrent.futures.ThreadPoolExecutor(max_workers=min(10, len(jobs))) as pool:
            futures = {
                pool.submit(model_call, model, prompt, token, seed): (model, seed)
                for model, seed in jobs
            }
            for future in concurrent.futures.as_completed(futures):
                model, seed = futures[future]
                try:
                    _, content = future.result()
                except Exception as exc:
                    content = f"<ERROR>{exc!r}</ERROR>"
                responses.append((model, seed, content))

        candidates: list[tuple[str, str]] = []
        seen: set[str] = set()
        for model, seed, content in responses:
            safe = re.sub(r"[^A-Za-z0-9_.-]+", "_", model)
            (EVIDENCE / f"round-{round_index:03d}-response-{safe}-{seed}.txt").write_text(content)
            replacement = extract_replacement(content)
            if replacement is None:
                continue
            candidate = source[:start] + replacement + source[end:]
            digest = H.sha256_bytes(candidate.encode())
            if digest in seen or candidate == source:
                continue
            seen.add(digest)
            candidates.append((f"{safe}-{seed}-{digest[:10]}", candidate))
        candidates.sort(key=lambda item: abs(len(item[1]) - len(source)))
        candidates = candidates[: args.candidates]

        best_metric = None
        best_text = None
        diagnostics = []
        for idx, (label, candidate) in enumerate(candidates):
            if H.declaration_headers(candidate) != baseline_headers:
                diagnostics.append({"label": label, "reject": "header fingerprint changed"})
                continue
            bad = H.forbidden_counts(candidate)
            if any(bad.values()):
                diagnostics.append({"label": label, "reject": f"forbidden {bad}"})
                continue
            original = FA.read_text(encoding="utf-8")
            FA.write_text(candidate, encoding="utf-8")
            try:
                cand_metric = H.compile_file(
                    FA,
                    EVIDENCE / f"round-{round_index:03d}-candidate-{idx:02d}.log",
                    max_errors=args.max_errors,
                )
            finally:
                FA.write_text(original, encoding="utf-8")
            diagnostics.append({"label": label, "metric": cand_metric.to_json()})
            if cand_metric.better_than(metric) and (
                best_metric is None or cand_metric.better_than(best_metric)
            ):
                best_metric = cand_metric
                best_text = candidate

        (EVIDENCE / f"round-{round_index:03d}-candidates.json").write_text(
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
            (EVIDENCE / "history.json").write_text(json.dumps(history, indent=2))
            if len(history) >= 3 and not history[-2].get("accepted", False):
                break
            continue

        FA.write_text(best_text, encoding="utf-8")
        metric = H.compile_file(
            FA, EVIDENCE / f"round-{round_index:03d}-accepted.log", max_errors=args.max_errors
        )
        history.append({"round": round_index, "accepted": True, "metric": metric.to_json()})
        (EVIDENCE / "history.json").write_text(json.dumps(history, indent=2))
        (EVIDENCE / "best-source.lean").write_text(best_text, encoding="utf-8")
        if metric.passed:
            break

    status = {"complete": metric.passed, "metric": metric.to_json()}
    (EVIDENCE / "FINAL_STATUS.json").write_text(json.dumps(status, indent=2))
    return 0 if metric.passed else 2


if __name__ == "__main__":
    raise SystemExit(main())
