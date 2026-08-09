from __future__ import annotations

import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time
import urllib.error
import urllib.request

BASE = Path(__file__).with_name("pass389_priority_repair_agent.py")
spec = importlib.util.spec_from_file_location("pass389_priority_beam_base", BASE)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load {BASE}")
agent = importlib.util.module_from_spec(spec)
spec.loader.exec_module(agent)


def stable_header_fingerprint(text: str) -> dict[str, str]:
    lines = text.splitlines()
    starts = [i for i, line in enumerate(lines) if agent.PUBLIC_PROOF_DECL.match(line)]
    result: dict[str, str] = {}
    occurrences: dict[str, int] = {}
    for index, start in enumerate(starts):
        end = starts[index + 1] if index + 1 < len(starts) else len(lines)
        header: list[str] = []
        for line in lines[start:end][:160]:
            if ":=" in line:
                header.append(line.split(":=", 1)[0].rstrip() + " :=")
                break
            header.append(line.rstrip())
            if re.search(r"\bwhere\s*$", line):
                break
        match = re.match(
            r"^(?:noncomputable\s+)?(?:theorem|lemma|corollary)\s+([^\s:{(]+)",
            lines[start],
        )
        name = match.group(1) if match else "anonymous"
        occurrence = occurrences.get(name, 0)
        occurrences[name] = occurrence + 1
        normalized = "\n".join(part.strip() for part in header if part.strip())
        result[f"{name}#{occurrence}"] = hashlib.sha256(normalized.encode()).hexdigest()
    return result


def robust_model(model: str, prompt: str) -> str | None:
    token = agent.TOKEN
    if not token:
        return None
    system = (
        "You repair Lean 4.33.0-rc1 proofs against current Mathlib. Preserve every public "
        "declaration header, binder, assumption and conclusion exactly. Never use sorry, admit, "
        "new axioms, unsafe, native_decide, or Lean.ofReduceBool."
    )
    for extra in ({"max_tokens": 12000}, {"max_tokens": 6000}, {"max_completion_tokens": 8000}, {}):
        payload = {
            "model": model,
            "messages": [
                {"role": "system", "content": system},
                {"role": "user", "content": prompt},
            ],
            **extra,
        }
        request = urllib.request.Request(
            "https://models.github.ai/inference/chat/completions",
            data=json.dumps(payload).encode(),
            method="POST",
            headers={
                "Authorization": f"Bearer {token}",
                "Content-Type": "application/json",
                "Accept": "application/json",
                "User-Agent": "pass389-beam-repair",
            },
        )
        try:
            with urllib.request.urlopen(request, timeout=360) as response:
                body = json.loads(response.read().decode())
            content = body.get("choices", [{}])[0].get("message", {}).get("content")
            if content:
                return content
        except urllib.error.HTTPError as exc:
            detail = exc.read().decode(errors="replace")
            print(f"model {model} HTTP {exc.code}: {detail[:1000]}")
            if exc.code in {401, 403, 404, 429}:
                break
        except Exception as exc:
            print(f"model {model} failed: {exc}")
    return None


def error_records(log: str) -> list[dict]:
    matches = list(agent.ERROR_LINE.finditer(log))
    result = []
    for index, match in enumerate(matches):
        start = match.start()
        end = matches[index + 1].start() if index + 1 < len(matches) else min(len(log), start + 7000)
        result.append({
            "line": int(match.group(1)),
            "col": int(match.group(2)),
            "text": log[start:end][-7000:],
        })
    return result


def declaration_items(source: str, records: list[dict], limit: int) -> list[dict]:
    seen: set[tuple[int, int]] = set()
    items: list[dict] = []
    lines = source.splitlines()
    for record in records:
        bounds = agent.declaration_bounds(source, record["line"])
        if bounds in seen:
            for item in items:
                if (item["start"], item["end"]) == bounds:
                    item["errors"].append(record["text"])
            continue
        seen.add(bounds)
        start, end = bounds
        items.append({
            "index": len(items) + 1,
            "start": start,
            "end": end,
            "line_start": start + 1,
            "line_end": end,
            "declaration": "\n".join(lines[start:end]),
            "context": "\n".join(
                f"{i + 1}: {lines[i]}"
                for i in range(max(0, start - 100), min(len(lines), end + 40))
            ),
            "errors": [record["text"]],
        })
        if len(items) >= limit:
            break
    return items


def beam_prompt(path: Path, source: str, items: list[dict]) -> str:
    parts = [
        f"Repair the following independent failing declarations in `{path.relative_to(agent.ROOT)}`.",
        "",
        "Rules:",
        "- Preserve each declaration header and statement exactly.",
        "- Replace only proof/implementation bodies.",
        "- Do not add public declarations or assumptions.",
        "- Do not use sorry, admit, axioms, unsafe, native_decide, or Lean.ofReduceBool.",
        "- Return every replacement using exactly this format:",
        "  BEGIN_DECLARATION N",
        "  ```lean",
        "  <complete replacement declaration>",
        "  ```",
        "  END_DECLARATION N",
        "- Include all listed declarations, even if one is left textually unchanged.",
        "",
        "Global imports/setup:",
        "```lean",
        "\n".join(source.splitlines()[:220]),
        "```",
    ]
    for item in items:
        parts += [
            "",
            f"## Declaration {item['index']} — source lines {item['line_start']}-{item['line_end']}",
            "Compiler errors:",
            "```text",
            "\n---\n".join(item["errors"]),
            "```",
            "Local context:",
            "```text",
            item["context"],
            "```",
            "Current declaration:",
            "```lean",
            item["declaration"],
            "```",
        ]
    return "\n".join(parts)


def parse_replacements(response: str, items: list[dict]) -> dict[int, str]:
    found: dict[int, str] = {}
    pattern = re.compile(
        r"BEGIN_DECLARATION\s+(\d+)\s*\n```(?:lean4?|Lean)?\s*\n(.*?)```\s*\nEND_DECLARATION\s+\1",
        re.S,
    )
    for match in pattern.finditer(response):
        found[int(match.group(1))] = match.group(2).strip() + "\n"
    if len(found) == len(items):
        return found
    blocks = re.findall(r"```(?:lean4?|Lean)?\s*\n(.*?)```", response, re.S)
    if len(blocks) == len(items):
        return {item["index"]: block.strip() + "\n" for item, block in zip(items, blocks)}
    return found


def apply_replacements(source: str, items: list[dict], replacements: dict[int, str]) -> str:
    lines = source.splitlines(keepends=True)
    by_index = {item["index"]: item for item in items}
    edits = []
    for index, replacement in replacements.items():
        item = by_index.get(index)
        if item:
            edits.append((item["start"], item["end"], replacement))
    for start, end, replacement in sorted(edits, reverse=True):
        lines[start:end] = [replacement]
    return "".join(lines)


def beam_repair(path: Path, rounds: int, models: list[str]) -> tuple[bool, dict]:
    agent.trust_audit(path)
    frozen = stable_header_fingerprint(path.read_text(encoding="utf-8"))
    agent.header_fingerprint = stable_header_fingerprint
    baseline = agent.compile_file(path, max_errors=40, tag=f"{path.stem}-beam-000")
    seen = {agent.sha256_file(path)}

    for round_no in range(1, rounds + 1):
        if baseline["exit_code"] == 0 and baseline["error_count"] == 0:
            return True, baseline
        log = (agent.EVIDENCE / f"{baseline['tag']}.log").read_text(encoding="utf-8", errors="replace")
        records = error_records(log)
        if not records:
            return False, baseline
        source = path.read_text(encoding="utf-8")
        item_limit = 6 if round_no <= 4 else 3
        items = declaration_items(source, records, item_limit)
        if not items:
            return False, baseline
        prompt = beam_prompt(path, source, items)
        improved = False
        for model in models:
            response = robust_model(model, prompt)
            if not response:
                continue
            (agent.EVIDENCE / f"beam-{round_no:02d}-{model.replace('/', '_')}.txt").write_text(response, encoding="utf-8")
            replacements = parse_replacements(response, items)
            if not replacements:
                continue
            candidate_text = apply_replacements(source, items, replacements)
            candidate_sha = agent.sha256_bytes(candidate_text.encode())
            if candidate_sha in seen:
                continue
            try:
                agent.ensure_headers_unchanged(frozen, candidate_text)
                tmp = agent.EVIDENCE / f"beam-candidate-{round_no:02d}.lean"
                tmp.write_text(candidate_text, encoding="utf-8")
                agent.trust_audit(tmp)
            except Exception as exc:
                print(f"beam candidate rejected before compile: {exc}")
                continue
            backup = path.read_bytes()
            path.write_text(candidate_text, encoding="utf-8")
            candidate = agent.compile_file(
                path,
                max_errors=40,
                tag=f"{path.stem}-beam-{round_no:02d}-{model.replace('/', '_')}",
            )
            if agent.better(candidate, baseline):
                print(
                    f"beam accepted {model}: first {baseline.get('first_error_line')} -> "
                    f"{candidate.get('first_error_line')}, errors {baseline['error_count']} -> "
                    f"{candidate['error_count']}"
                )
                baseline = candidate
                seen.add(candidate_sha)
                improved = True
                break
            path.write_bytes(backup)
        if not improved:
            break
    final = agent.compile_file(path, max_errors=250, tag=f"{path.stem}-beam-final")
    return final["exit_code"] == 0 and final["error_count"] == 0, final


def main() -> int:
    agent.EVIDENCE.mkdir(parents=True, exist_ok=True)
    agent.STATE.parent.mkdir(parents=True, exist_ok=True)
    fa = agent.PSV / "Mock2_FunctionalAnalysis.lean"
    bootstrap = agent.download_pass389_candidate(fa)
    agent.trust_audit(fa)
    models = [
        item.strip()
        for item in os.environ.get(
            "PASS389_MODELS",
            "openai/gpt-5-mini,openai/gpt-4.1,deepseek/DeepSeek-V3-0324,xai/grok-3-mini",
        ).split(",")
        if item.strip()
    ]
    state: dict = {
        "baseline": "PASS 389",
        "mode": "multi-declaration-beam",
        "bootstrap": bootstrap,
        "status": "RUNNING",
        "targets": {},
        "started_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
    }
    fa_ok, frontier = beam_repair(fa, rounds=12, models=models)
    state["targets"][fa.name] = {"repair_pass": fa_ok, "frontier": frontier}
    if fa_ok:
        fa_ok, direct = agent.verify_twice(fa)
        state["targets"][fa.name]["two_pass"] = fa_ok
        state["targets"][fa.name]["direct_runs"] = direct

    touched = [fa, agent.STATE]
    if not fa_ok:
        state["status"] = "FA_INCOMPLETE"
        state["finished_at"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
        agent.STATE.write_text(json.dumps(state, indent=2), encoding="utf-8")
        sha = agent.git_commit_to_branch(touched, agent.CHAIN_BRANCH, "fix: advance PASS 389 beam frontier")
        state["published_commit"] = sha
        print(json.dumps(state, indent=2))
        return 2

    ordered: list[Path] = []
    integrated = agent.PSV / "Mock2_FunctionalAnalysis_Integrated.lean"
    if integrated.exists():
        ordered.append(integrated)
    ordered.extend(agent.actual_mock3_files())
    qym = agent.PSV / "QYM.lean"
    if qym.exists():
        ordered.append(qym)

    agent.header_fingerprint = stable_header_fingerprint
    agent.call_model = robust_model
    for target in ordered:
        ok, target_frontier = agent.repair_until_pass(target, 24, models)
        state["targets"][target.name] = {"repair_pass": ok, "frontier": target_frontier}
        touched.append(target)
        if ok:
            ok, direct = agent.verify_twice(target)
            state["targets"][target.name]["two_pass"] = ok
            state["targets"][target.name]["direct_runs"] = direct
        if not ok:
            state["status"] = f"{target.name}_INCOMPLETE"
            state["finished_at"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
            agent.STATE.write_text(json.dumps(state, indent=2), encoding="utf-8")
            sha = agent.git_commit_to_branch(touched, agent.CHAIN_BRANCH, f"fix: advance PASS 389 beam {target.stem}")
            state["published_commit"] = sha
            print(json.dumps(state, indent=2))
            return 3

    state["status"] = "SUCCESS_ALL_REQUIRED_TARGETS_2X_PASS"
    state["finished_at"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    marker = agent.ROOT / "build-logs" / "PR9_FA_INTEGRATED_MOCK3_QYM_FINAL_2X_PASS.json"
    marker.write_text(json.dumps(state, indent=2), encoding="utf-8")
    agent.STATE.write_text(json.dumps(state, indent=2), encoding="utf-8")
    touched.extend([agent.STATE, marker])
    sha = agent.git_commit_to_branch(touched, agent.PR9_BRANCH, "fix: materialize PASS 389 beam two-pass sources")
    state["published_commit"] = sha
    print(json.dumps(state, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
