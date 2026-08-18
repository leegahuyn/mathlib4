#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys

QYM_PATH = "PrimalitySheafVerification/QYM.lean"


def run(*args: str) -> str:
    return subprocess.check_output(args, text=True, stderr=subprocess.DEVNULL)


def git_blob(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def declaration_regex(owner: str) -> re.Pattern[str]:
    return re.compile(
        r"(?m)^(?:set_option[^\n]* in\n)*"
        r"(?:theorem|lemma|def|abbrev|instance|noncomputable\s+def|"
        r"noncomputable\s+instance)\s+" + re.escape(owner) + r"(?=[\s:(])"
    )


def all_declarations(text: str) -> list[tuple[int, int, str]]:
    pattern = re.compile(
        r"(?m)^(?:set_option[^\n]* in\n)*"
        r"(?:theorem|lemma|def|abbrev|instance|noncomputable\s+def|"
        r"noncomputable\s+instance)\s+([^\s:(]+)"
    )
    return [(match.start(), match.end(), match.group(1)) for match in pattern.finditer(text)]


def extract_declaration(text: str, owner: str) -> tuple[int, int, str] | None:
    match = declaration_regex(owner).search(text)
    if match is None:
        return None
    start = match.start()
    declarations = all_declarations(text)
    starts = [item[0] for item in declarations]
    later = [position for position in starts if position > start]
    end = min(later) if later else len(text)
    return start, end, text[start:end]


def split_signature_body(declaration: str) -> tuple[str, str] | None:
    # Preserve the current declaration signature exactly. Historical material supplies only the RHS.
    # The common theorem form is `:= by`; definitions using `:= inferInstance` are also supported.
    marker = re.search(r":=\s*(?:by\b)?", declaration)
    if marker is None:
        return None
    signature = declaration[: marker.start()]
    body = declaration[marker.start() :]
    return signature, body


def normalized_signature(signature: str) -> str:
    signature = re.sub(r"(?m)^set_option[^\n]* in\n", "", signature)
    signature = re.sub(r"\s+", " ", signature).strip()
    return signature


def forbidden_audit(text: str) -> dict[str, int]:
    return {
        "sorry": len(re.findall(r"\bsorry\b", text)),
        "admit": len(re.findall(r"\badmit\b", text)),
        "native_decide": len(re.findall(r"\bnative_decide\b", text)),
        "Lean.ofReduceBool": text.count("Lean.ofReduceBool"),
        "global_axiom": len(re.findall(r"(?m)^\s*axiom\s+", text)),
        "unsafe": len(re.findall(r"(?m)^\s*unsafe\s+", text)),
        "maxHeartbeats_zero": len(re.findall(r"set_option\s+maxHeartbeats\s+0\b", text)),
    }


def prepare(frontier: Path, result_path: Path, next_path: Path, out: Path) -> None:
    out.mkdir(parents=True, exist_ok=True)
    source_raw = frontier.read_bytes()
    source_sha = hashlib.sha256(source_raw).hexdigest()
    result = json.loads(result_path.read_text(encoding="utf-8"))
    next_data = json.loads(next_path.read_text(encoding="utf-8"))
    if source_sha != result.get("candidate_qym_sha256"):
        raise RuntimeError((source_sha, result.get("candidate_qym_sha256")))
    owner_data = next_data.get("first_owner") or {}
    owner = owner_data.get("name")
    if not isinstance(owner, str) or not owner:
        raise RuntimeError("next-blocker owner is missing")
    source = source_raw.decode("utf-8")
    current = extract_declaration(source, owner)
    if current is None:
        raise RuntimeError(f"current declaration not found: {owner}")
    current_start, current_end, current_decl = current
    current_split = split_signature_body(current_decl)
    if current_split is None:
        raise RuntimeError("current declaration has no supported RHS")
    current_signature, current_body = current_split
    signature_key = normalized_signature(current_signature)
    (out / "CURRENT_DECLARATION.lean").write_text(current_decl, encoding="utf-8")

    commits = run("git", "log", "--all", "--format=%H", "--", QYM_PATH).splitlines()
    # Keep recency order, remove duplicates, and bound archaeology cost.
    seen_commits: set[str] = set()
    commits = [c for c in commits if not (c in seen_commits or seen_commits.add(c))][:500]
    body_seen = {hashlib.sha256(current_body.encode()).hexdigest()}
    candidates = []

    for commit in commits:
        try:
            historical = run("git", "show", f"{commit}:{QYM_PATH}")
        except Exception:
            continue
        extracted = extract_declaration(historical, owner)
        if extracted is None:
            continue
        _, _, historical_decl = extracted
        historical_split = split_signature_body(historical_decl)
        if historical_split is None:
            continue
        historical_signature, historical_body = historical_split
        if normalized_signature(historical_signature) != signature_key:
            continue
        body_hash = hashlib.sha256(historical_body.encode()).hexdigest()
        if body_hash in body_seen:
            continue
        body_seen.add(body_hash)
        candidate_text = source[:current_start] + current_signature + historical_body + source[current_end:]
        audit = forbidden_audit(candidate_text)
        if any(audit.values()):
            continue
        raw = candidate_text.encode("utf-8")
        candidate_sha = hashlib.sha256(raw).hexdigest()
        candidate_id = f"{commit[:12]}-{body_hash[:10]}"
        candidate_file = out / f"QYM.{candidate_id}.lean"
        candidate_file.write_bytes(raw)
        metadata = {
            "id": candidate_id,
            "owner": owner,
            "historical_commit": commit,
            "historical_body_sha256": body_hash,
            "candidate_qym_sha256": candidate_sha,
            "candidate_qym_blob": git_blob(raw),
            "bytes": len(raw),
            "lf": raw.count(b"\n"),
            "forbidden": audit,
        }
        (out / f"META.{candidate_id}.json").write_text(
            json.dumps(metadata, indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )
        candidates.append(metadata)
        if len(candidates) >= 30:
            break

    matrix = {"include": [{"candidate_id": item["id"]} for item in candidates]}
    summary = {
        "schema": "qym-declaration-archaeology-prepare-v1",
        "owner": owner,
        "frontier_sha256": source_sha,
        "frontier_error_headers": result.get("error_headers"),
        "commit_count_examined": len(commits),
        "candidate_count": len(candidates),
        "candidates": candidates,
        "matrix": matrix,
    }
    (out / "PREPARE_RESULT.json").write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    (out / "matrix.json").write_text(json.dumps(matrix, separators=(",", ":")) + "\n")
    print(json.dumps(summary, indent=2, sort_keys=True))


def main() -> None:
    if len(sys.argv) != 6 or sys.argv[1] != "prepare":
        raise SystemExit(
            "usage: qym_declaration_archaeology.py prepare FRONTIER RESULT NEXT OUT"
        )
    prepare(Path(sys.argv[2]), Path(sys.argv[3]), Path(sys.argv[4]), Path(sys.argv[5]))


if __name__ == "__main__":
    main()
