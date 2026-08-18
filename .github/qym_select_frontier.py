#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import hashlib
import json
import re
import shutil
import sys


def rank(x: dict) -> tuple:
    first = x.get("first_error") or {}
    return (
        0 if x.get("semantic_pass") else 1,
        int(x.get("error_headers", 10**9)),
        -int(first.get("line") or 0),
        int(x.get("warning_headers", 10**9)),
    )


def git_blob(raw: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest()


def nearest_decl(source: Path, line: int) -> str:
    if not source.exists():
        return "unknown_declaration"
    lines = source.read_text(encoding="utf-8", errors="replace").splitlines()
    for i in range(min(max(line - 1, 0), len(lines) - 1), -1, -1):
        m = re.match(
            r"^(?:private\s+|noncomputable\s+|local\s+|protected\s+)*"
            r"(?:theorem|lemma|def|abbrev|instance)\s+([^\s(:]+)",
            lines[i],
        )
        if m:
            return m.group(1)
    return "unknown_declaration"


def main() -> None:
    if len(sys.argv) != 7:
        raise SystemExit(
            "usage: qym_select_frontier.py ARTIFACT_ROOT FRONTIER CANONICAL PROBE RUN_ID CANDIDATE_GLOB"
        )
    artifact_root = Path(sys.argv[1])
    frontier = Path(sys.argv[2])
    canonical = Path(sys.argv[3])
    probe = sys.argv[4]
    run_id = int(sys.argv[5])
    candidate_glob = sys.argv[6]
    frontier.mkdir(parents=True, exist_ok=True)

    choices: list[dict] = []
    for result_path in artifact_root.rglob("PROBE_RESULT.json"):
        try:
            result = json.loads(result_path.read_text(encoding="utf-8"))
        except Exception:
            continue
        errors = result.get("error_headers")
        if not isinstance(errors, int) or result.get("panic_lines") != 0:
            continue
        candidates = list(result_path.parent.glob(candidate_glob))
        if len(candidates) != 1:
            continue
        candidate = candidates[0]
        raw = candidate.read_bytes()
        sha = hashlib.sha256(raw).hexdigest()
        blob = git_blob(raw)
        if sha != (result.get("candidate_qym_sha256") or result.get("candidate_sha256")):
            continue
        if blob != (result.get("candidate_qym_blob") or result.get("candidate_blob")):
            continue
        first = result.get("first_error") or {}
        choice = {
            "probe": probe,
            "run_id": run_id,
            "variant": result.get("variant"),
            "candidate_qym_sha256": sha,
            "candidate_qym_blob": blob,
            "bytes": len(raw),
            "lf": raw.count(b"\n"),
            "exit": result.get("exit"),
            "error_headers": errors,
            "warning_headers": result.get("warning_headers", 10**9),
            "panic_lines": result.get("panic_lines"),
            "first_error": first,
            "last_error": result.get("last_error"),
            "semantic_pass": bool(result.get("semantic_pass")),
            "log_sha256": result.get("log_sha256"),
            "candidate_path": str(candidate),
            "result_path": str(result_path),
        }
        choices.append(choice)

    if not choices:
        raise SystemExit("no hash-valid full direct Lean candidate")
    choices.sort(key=rank)
    best_full = choices[0]
    candidate = Path(best_full["candidate_path"])
    result_path = Path(best_full["result_path"])
    best = {k: v for k, v in best_full.items() if k not in {"candidate_path", "result_path"}}

    # Persist this campaign independently of promotion.
    prefix = probe.upper()
    (frontier / f"{prefix}_SELECTION.json").write_text(
        json.dumps({"run_id": run_id, "best": best, "all": [
            {k: v for k, v in x.items() if k not in {"candidate_path", "result_path"}}
            for x in choices
        ]}, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    shutil.copy2(candidate, frontier / f"QYM_{prefix}_BEST.lean")
    shutil.copy2(result_path, frontier / f"{prefix}_RESULT.json")
    for name in ("QYM.error-headers.txt", "QYM.diagnostics.jsonl", "QYM.time"):
        src = result_path.parent / name
        if src.exists():
            shutil.copy2(src, frontier / f"{prefix}_{name.replace('QYM.', '')}")

    lines = candidate.read_text(encoding="utf-8", errors="replace").splitlines()
    first_line = int((best.get("first_error") or {}).get("line") or 1)
    lo, hi = max(1, first_line - 100), min(len(lines), first_line + 180)
    (frontier / f"{prefix}_FIRST_ERROR_CONTEXT.txt").write_text(
        "\n".join(f"{i}: {lines[i-1]}" for i in range(lo, hi + 1)) + "\n",
        encoding="utf-8",
    )

    floor = {
        "probe": "Probe35-flat_infer",
        "run_id": 32095253829,
        "variant": "flat_infer",
        "candidate_qym_sha256": "313c076645a51976237738bd10c7f22b54f2a483499e60b57fa0d69be007cc1e",
        "candidate_qym_blob": "ff49510790dd7ca136bf34c3ec7150617ee1c241",
        "exit": 1,
        "error_headers": 89,
        "warning_headers": 356,
        "panic_lines": 0,
        "first_error": {"line": 37775},
        "semantic_pass": False,
    }
    current_path = frontier / "CURRENT_GLOBAL_BEST.json"
    current = floor
    if current_path.exists():
        try:
            stored = json.loads(current_path.read_text(encoding="utf-8"))
            if rank(stored) < rank(current):
                current = stored
        except Exception:
            pass

    promoted = rank(best) < rank(current) or best["semantic_pass"]
    decision = {"promoted": promoted, "previous": current, "candidate": best}
    (frontier / f"{prefix}_PROMOTION_DECISION.json").write_text(
        json.dumps(decision, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    if promoted:
        shutil.copy2(candidate, frontier / "QYM_GLOBAL_BEST.lean")
        current_path.write_text(json.dumps(best, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    if best["semantic_pass"]:
        shutil.copy2(candidate, canonical)
        (frontier / "QYM_PASS_PENDING_CLEAN_RECHECK").write_text(
            best["candidate_qym_sha256"] + "\n", encoding="utf-8"
        )

    decoded = candidate.read_text(encoding="utf-8")
    forbidden = {
        "sorry": len(re.findall(r"\bsorry\b", decoded)),
        "admit": len(re.findall(r"\badmit\b", decoded)),
        "native_decide": len(re.findall(r"\bnative_decide\b", decoded)),
        "Lean.ofReduceBool": decoded.count("Lean.ofReduceBool"),
        "global_axiom": len(re.findall(r"(?m)^\s*axiom\s+", decoded)),
        "unsafe": len(re.findall(r"(?m)^\s*unsafe\s+", decoded)),
        "maxHeartbeats_zero": len(re.findall(r"set_option\s+maxHeartbeats\s+0\b", decoded)),
    }
    if any(forbidden.values()):
        raise SystemExit(f"forbidden token audit failed: {forbidden}")
    (frontier / f"{prefix}_FORBIDDEN_AUDIT.json").write_text(
        json.dumps(forbidden, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )

    declaration = nearest_decl(candidate, first_line)
    msg = re.sub(r"\s+", " ", str((best.get("first_error") or {}).get("message") or "")).strip()[:90]
    commit_message = (
        f"QYM frontier {probe} E{best['error_headers']} W{best['warning_headers']} "
        f"L{first_line} {declaration} [{best.get('variant')}] {msg}"
    )
    (frontier / "FRONTIER_STATUS.json").write_text(
        json.dumps({**best, "first_declaration": declaration, "promoted": promoted}, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    (frontier / "FRONTIER_COMMIT_MESSAGE.txt").write_text(commit_message + "\n", encoding="utf-8")
    print(json.dumps(decision, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
