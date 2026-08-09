from __future__ import annotations

import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import urllib.error
import urllib.request

BASE = Path(__file__).with_name("pass389_priority_repair_agent.py")
spec = importlib.util.spec_from_file_location("pass389_priority_base_v3", BASE)
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
        chunk = lines[start:end]
        header_lines: list[str] = []
        for line in chunk[:160]:
            if ":=" in line:
                header_lines.append(line.split(":=", 1)[0].rstrip() + " :=")
                break
            header_lines.append(line.rstrip())
            if re.search(r"\bwhere\s*$", line):
                break
        first = lines[start]
        match = re.match(
            r"^(?:noncomputable\s+)?(?:theorem|lemma|corollary)\s+([^\s:{(]+)",
            first,
        )
        name = match.group(1) if match else "anonymous"
        occurrence = occurrences.get(name, 0)
        occurrences[name] = occurrence + 1
        normalized = "\n".join(part.strip() for part in header_lines if part.strip())
        result[f"{name}#{occurrence}"] = hashlib.sha256(normalized.encode()).hexdigest()
    return result


def robust_call_model(model: str, prompt: str) -> str | None:
    token = agent.TOKEN
    if not token:
        return None
    system = (
        "You are a Lean 4.33.0-rc1 and current Mathlib proof repair expert. "
        "Never weaken statements or assumptions. Never use sorry, admit, new axioms, "
        "unsafe, native_decide, or Lean.ofReduceBool. Return only the requested Lean code."
    )
    variants = [
        {"max_tokens": 8000, "temperature": 0.0},
        {"max_tokens": 4096},
        {"max_completion_tokens": 6000},
        {},
    ]
    for extra in variants:
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
            data=json.dumps(payload).encode("utf-8"),
            method="POST",
            headers={
                "Authorization": f"Bearer {token}",
                "Content-Type": "application/json",
                "Accept": "application/json",
                "User-Agent": "pass389-priority-repair-v3",
            },
        )
        try:
            with urllib.request.urlopen(request, timeout=300) as response:
                body = json.loads(response.read().decode("utf-8"))
            content = body.get("choices", [{}])[0].get("message", {}).get("content")
            if content:
                return content
        except urllib.error.HTTPError as exc:
            detail = exc.read().decode("utf-8", errors="replace")
            print(f"REST model {model} variant {extra} HTTP {exc.code}: {detail[:1200]}")
            if exc.code in {401, 403, 404, 429}:
                break
        except Exception as exc:
            print(f"REST model {model} variant {extra} failed: {exc}")

    # Official gh-models extension fallback. Try both stdin and prompt flag forms because
    # extension versions differ.
    env = os.environ.copy()
    env["GH_TOKEN"] = token
    subprocess.run(
        ["gh", "extension", "install", "github/gh-models"],
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        env=env,
        timeout=180,
    )
    commands = [
        ["gh", "models", "run", model],
        ["gh", "models", "run", model, "--prompt", prompt],
        ["gh", "models", "run", model, "-p", prompt],
    ]
    for index, command in enumerate(commands):
        try:
            proc = subprocess.run(
                command,
                text=True,
                input=prompt if index == 0 else None,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                env=env,
                timeout=360,
            )
        except Exception as exc:
            print(f"gh models {model} failed: {exc}")
            continue
        if proc.returncode == 0 and proc.stdout.strip():
            return proc.stdout
        print(f"gh models {model} rc={proc.returncode}: {proc.stdout[-1200:]}")
    return None


def robust_download(target: Path) -> dict:
    try:
        return agent.download_pass389_candidate(target)
    except Exception as primary:
        print(f"artifact bootstrap failed, trying branch fallback: {primary}")
    refs = agent.run(
        ["git", "ls-remote", "--heads", "origin"],
        timeout=180,
    )
    branches: list[tuple[str, str]] = []
    for line in refs.stdout.splitlines():
        if "\trefs/heads/" not in line:
            continue
        sha, ref = line.split("\t", 1)
        branch = ref.removeprefix("refs/heads/")
        if re.search(r"(?:fa389|pass389|389)", branch, re.I):
            branches.append((sha, branch))
    if not branches:
        raise RuntimeError("neither PASS 389 artifact nor matching branch was available")
    branches.sort(reverse=True)
    candidates: list[tuple[int, bytes, str, str]] = []
    for sha, branch in branches[:20]:
        agent.run(["git", "fetch", "--depth=5", "origin", branch], timeout=300)
        proc = agent.run(
            ["git", "show", "FETCH_HEAD:PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean"],
            timeout=180,
        )
        data = proc.stdout.encode("utf-8")
        if proc.returncode == 0 and len(data) > 100000:
            candidates.append((len(data), data, branch, sha))
    if not candidates:
        raise RuntimeError("PASS 389 branches did not contain a materialized FA source")
    candidates.sort(reverse=True)
    _, data, branch, sha = candidates[0]
    target.write_bytes(data)
    return {
        "mode": "branch-fallback",
        "branch": branch,
        "branch_sha": sha,
        "candidate_sha256": agent.sha256_file(target),
    }


agent.header_fingerprint = stable_header_fingerprint
agent.call_model = robust_call_model
agent.download_pass389_candidate = robust_download
raise SystemExit(agent.main())
