from __future__ import annotations

import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import time

BASE = Path(__file__).with_name("pass389_priority_repair_agent.py")
spec = importlib.util.spec_from_file_location("pass389_tactic_base", BASE)
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


def tactic_candidates(error: str) -> list[str]:
    candidates: list[str] = []
    lower = error.lower()
    if "continuous" in lower or "contdiff" in lower or "differentiable" in lower:
        candidates += ["fun_prop", "continuity", "aesop"]
    if "measurable" in lower or "aemeasurable" in lower:
        candidates += ["fun_prop", "measurability", "aesop"]
    if "integrable" in lower or "memlp" in lower:
        candidates += ["fun_prop", "aesop", "simp_all"]
    if "extensionality" in lower or "function expected" in lower or "application type mismatch" in lower:
        candidates += ["ext <;> simp_all", "aesop", "grind"]
    if "ring" in lower or "field" in lower or "algebra" in lower or "equality" in lower:
        candidates += ["ring_nf", "noncomm_ring", "norm_num at *", "simp_all"]
    candidates += [
        "aesop",
        "grind",
        "simp_all",
        "aesop (add safe constructors)",
        "first | rfl | simp_all | aesop | grind",
        "ext <;> simp_all",
    ]
    out: list[str] = []
    for candidate in candidates:
        if candidate not in out:
            out.append(candidate)
    return out


def replace_by_proof(declaration: str, tactic: str) -> str | None:
    marker = declaration.find(":= by")
    if marker < 0:
        return None
    # Do not erase a declaration-local `where` block.
    if re.search(r"(?m)^where\s*$", declaration[marker + 5 :]):
        return None
    header = declaration[: marker + 2]
    return f"{header} by\n  {tactic}\n"


def sweep(path: Path, cycles: int) -> tuple[bool, dict]:
    agent.header_fingerprint = stable_header_fingerprint
    source = path.read_text(encoding="utf-8")
    frozen = stable_header_fingerprint(source)
    agent.trust_audit(path)
    baseline = agent.compile_file(path, max_errors=1, tag=f"{path.stem}-tactic-000")
    seen = {agent.sha256_file(path)}
    for cycle in range(1, cycles + 1):
        if baseline["exit_code"] == 0 and baseline["error_count"] == 0:
            full = agent.compile_file(path, max_errors=250, tag=f"{path.stem}-tactic-full-{cycle}")
            if full["exit_code"] == 0 and full["error_count"] == 0:
                return True, full
            baseline = full
        line = baseline.get("first_error_line")
        if not line:
            break
        text = path.read_text(encoding="utf-8")
        start, end = agent.declaration_bounds(text, line)
        lines = text.splitlines(keepends=True)
        declaration = "".join(lines[start:end])
        improved = False
        for tactic in tactic_candidates(baseline.get("first_error", "")):
            replacement = replace_by_proof(declaration, tactic)
            if not replacement:
                break
            candidate_text = "".join(lines[:start] + [replacement] + lines[end:])
            candidate_sha = agent.sha256_bytes(candidate_text.encode())
            if candidate_sha in seen:
                continue
            try:
                agent.ensure_headers_unchanged(frozen, candidate_text)
                tmp = agent.EVIDENCE / f"tactic-candidate-{cycle:03d}.lean"
                tmp.parent.mkdir(parents=True, exist_ok=True)
                tmp.write_text(candidate_text, encoding="utf-8")
                agent.trust_audit(tmp)
            except Exception:
                continue
            backup = path.read_bytes()
            path.write_text(candidate_text, encoding="utf-8")
            candidate = agent.compile_file(
                path,
                max_errors=1,
                tag=f"{path.stem}-tactic-{cycle:03d}-{hashlib.sha1(tactic.encode()).hexdigest()[:8]}",
            )
            if agent.better(candidate, baseline):
                baseline = candidate
                seen.add(candidate_sha)
                improved = True
                print(f"accepted tactic at cycle {cycle}: {tactic}")
                break
            path.write_bytes(backup)
        if not improved:
            break
    final = agent.compile_file(path, max_errors=250, tag=f"{path.stem}-tactic-final")
    return final["exit_code"] == 0 and final["error_count"] == 0, final


def main() -> int:
    agent.EVIDENCE.mkdir(parents=True, exist_ok=True)
    agent.STATE.parent.mkdir(parents=True, exist_ok=True)
    fa = agent.PSV / "Mock2_FunctionalAnalysis.lean"
    previous = {}
    if agent.STATE.exists():
        try:
            previous = json.loads(agent.STATE.read_text(encoding="utf-8"))
        except Exception:
            previous = {}
    if previous.get("baseline") == "PASS 389" and fa.exists() and fa.stat().st_size > 100000:
        bootstrap = {"mode": "checked-in-tactic-source", "candidate_sha256": agent.sha256_file(fa)}
    else:
        bootstrap = agent.download_pass389_candidate(fa)
    state: dict = {
        "baseline": "PASS 389",
        "mode": "deterministic-tactic-sweep",
        "bootstrap": bootstrap,
        "status": "RUNNING",
        "targets": {},
        "started_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
    }
    fa_ok, frontier = sweep(fa, 90)
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
        sha = agent.git_commit_to_branch(touched, agent.CHAIN_BRANCH, "fix: advance PASS 389 tactic frontier")
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
    for target in ordered:
        ok, target_frontier = sweep(target, 50)
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
            sha = agent.git_commit_to_branch(touched, agent.CHAIN_BRANCH, f"fix: advance PASS 389 tactic {target.stem}")
            state["published_commit"] = sha
            print(json.dumps(state, indent=2))
            return 3

    state["status"] = "SUCCESS_ALL_REQUIRED_TARGETS_2X_PASS"
    state["finished_at"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    marker = agent.ROOT / "build-logs" / "PR9_FA_INTEGRATED_MOCK3_QYM_FINAL_2X_PASS.json"
    marker.write_text(json.dumps(state, indent=2), encoding="utf-8")
    agent.STATE.write_text(json.dumps(state, indent=2), encoding="utf-8")
    touched.extend([agent.STATE, marker])
    sha = agent.git_commit_to_branch(touched, agent.PR9_BRANCH, "fix: materialize PASS 389 tactic two-pass sources")
    state["published_commit"] = sha
    print(json.dumps(state, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
