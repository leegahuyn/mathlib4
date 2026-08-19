#!/usr/bin/env python3
from __future__ import annotations

from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass
from pathlib import Path
import argparse
import collections
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import time

DECL_RE = re.compile(
    r"^(?:(?:private|protected|noncomputable)\s+)*"
    r"(?:theorem|lemma|def|abbrev|opaque|instance)\s+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_'.]*)\b"
)
DIAG_RE = re.compile(
    r"^(?P<file>.*?\.lean):(?P<line>\d+):(?P<column>\d+): "
    r"(?P<severity>error|warning)(?:\((?P<code>[^)]*)\))?:\s*(?P<message>.*)$",
    re.M,
)
PANIC_RE = re.compile(
    r"(?im)^.*(?:internal error|uncaught exception|panic(?:!|:|\s)).*$"
)


@dataclass(frozen=True)
class Block:
    name: str
    start: int
    end: int
    text: str


@dataclass(frozen=True)
class Candidate:
    path: Path
    sha256: str
    blob: str
    donor: str
    mode: str
    target: str
    gate_line: int


def sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def git_blob(raw: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest()


def audit(text: str) -> dict[str, int]:
    return {
        "sorry": len(re.findall(r"\bsorry\b", text)),
        "admit": len(re.findall(r"\badmit\b", text)),
        "native_decide": len(re.findall(r"\bnative_decide\b", text)),
        "Lean.ofReduceBool": text.count("Lean.ofReduceBool"),
        "global_axiom": len(re.findall(r"(?m)^\s*axiom\s+", text)),
        "unsafe": len(re.findall(r"(?m)^\s*unsafe\s+", text)),
        "maxHeartbeats_zero": len(
            re.findall(r"set_option\s+maxHeartbeats\s+0\b", text)
        ),
    }


def parse_blocks(text: str) -> tuple[list[str], list[Block], dict[str, Block]]:
    lines = text.splitlines(keepends=True)
    marks: list[tuple[str, int]] = []
    for index, line in enumerate(lines):
        if line[:1].isspace():
            continue
        match = DECL_RE.match(line)
        if match:
            marks.append((match.group("name"), index))
    blocks: list[Block] = []
    mapping: dict[str, Block] = {}
    for i, (name, start) in enumerate(marks):
        end = marks[i + 1][1] if i + 1 < len(marks) else len(lines)
        block = Block(name, start, end, "".join(lines[start:end]))
        if name not in mapping:
            mapping[name] = block
            blocks.append(block)
    return lines, blocks, mapping


def normalize_space(text: str) -> str:
    return re.sub(r"\s+", " ", text).strip()


def proof_split(block: str) -> tuple[str, str] | None:
    marker = ":= by"
    pos = block.find(marker)
    if pos < 0:
        return None
    return block[: pos + len(marker)], block[pos + len(marker):]


def declaration_signature(block: str) -> str:
    split = proof_split(block)
    if split is not None:
        return normalize_space(split[0])
    pos = block.find(":=")
    return normalize_space(block if pos < 0 else block[:pos])


def target_block(text: str, first_line: int) -> Block:
    _, blocks, _ = parse_blocks(text)
    if not blocks:
        raise RuntimeError("no top-level declarations parsed")
    zero_line = max(0, first_line - 1)
    eligible = [block for block in blocks if block.start <= zero_line]
    if not eligible:
        return blocks[0]
    block = eligible[-1]
    if zero_line >= block.end:
        raise RuntimeError(f"first error line {first_line} is outside parsed declaration ranges")
    return block


def first_error_line(result: dict) -> int:
    return int((result.get("first_error") or {}).get("line") or 0)


def score(result: dict) -> tuple[int, int, int, int, str]:
    errors = int(result.get("error_headers", 10**9))
    panic = int(result.get("panic_lines", 10**9))
    first = first_error_line(result)
    warnings = int(result.get("warning_headers", 10**9))
    identity = str(result.get("candidate_qym_sha256") or "")
    return (errors, panic, -first, warnings, identity)


def parse_log(log_path: Path, exit_code: int, candidate: Candidate, baseline_errors: int) -> dict:
    raw = log_path.read_bytes() if log_path.exists() else b""
    text = raw.decode(errors="replace")
    rows = []
    for match in DIAG_RE.finditer(text):
        row = match.groupdict()
        row["line"] = int(row["line"])
        row["column"] = int(row["column"])
        rows.append(row)
    errors = [row for row in rows if row["severity"] == "error"]
    warnings = [row for row in rows if row["severity"] == "warning"]
    panics = PANIC_RE.findall(text)
    semantic = exit_code == 0 and not errors and not panics
    return {
        "schema": "qym-first-error-harvest-result-v1",
        "candidate_qym_sha256": candidate.sha256,
        "candidate_qym_blob": candidate.blob,
        "donor": candidate.donor,
        "mode": candidate.mode,
        "target": candidate.target,
        "gate_line": candidate.gate_line,
        "exit": exit_code,
        "error_headers": len(errors),
        "warning_headers": len(warnings),
        "panic_lines": len(panics),
        "first_error": errors[0] if errors else None,
        "last_error": errors[-1] if errors else None,
        "error_codes": dict(sorted(collections.Counter(
            row["code"] or "uncoded" for row in errors
        ).items())),
        "log_sha256": sha256(raw),
        "semantic_pass": semantic,
        "strict_error_improvement": semantic or (
            not panics and len(errors) < baseline_errors
        ),
        "diagnostics": rows,
        "panic_text": panics,
    }


def generate_candidates(
    current_path: Path,
    result: dict,
    donor_paths: list[Path],
    out_dir: Path,
    limit: int,
) -> tuple[Block, list[Candidate], dict]:
    current_raw = current_path.read_bytes()
    current_text = current_raw.decode("utf-8")
    current_audit = audit(current_text)
    current_lines, _, current_map = parse_blocks(current_text)
    line = first_error_line(result)
    if line <= 0:
        raise RuntimeError("current result has no first error line")
    target = target_block(current_text, line)
    current_signature = declaration_signature(target.text)
    out_dir.mkdir(parents=True, exist_ok=True)

    candidates: list[Candidate] = []
    seen = {sha256(current_raw)}
    donor_reports = []

    for donor_path in donor_paths:
        try:
            donor_raw = donor_path.read_bytes()
            donor_text = donor_raw.decode("utf-8")
        except Exception:
            continue
        _, donor_blocks, donor_map = parse_blocks(donor_text)
        donor_target = donor_map.get(target.name)
        if donor_target is None:
            continue
        if normalize_space(donor_target.text) == normalize_space(target.text):
            continue

        modes: list[tuple[str, str]] = []
        donor_signature = declaration_signature(donor_target.text)
        if donor_signature == current_signature:
            modes.append(("whole_declaration", donor_target.text))

        current_split = proof_split(target.text)
        donor_split = proof_split(donor_target.text)
        if current_split is not None and donor_split is not None:
            # Preserve the exact current statement and transplant only the proof.
            modes.append(("proof_body", current_split[0] + donor_split[1]))

        produced = []
        for mode, replacement in modes:
            new_lines = list(current_lines)
            new_lines[target.start:target.end] = [replacement]
            new_text = "".join(new_lines)
            if audit(new_text) != current_audit:
                continue
            raw = new_text.encode("utf-8")
            identity = sha256(raw)
            if identity in seen:
                continue
            seen.add(identity)
            index = len(candidates)
            path = out_dir / f"candidate-{index:03d}-{identity[:12]}.lean"
            path.write_bytes(raw)
            gate = target.start + replacement.count("\n") + 1
            candidate = Candidate(
                path=path,
                sha256=identity,
                blob=git_blob(raw),
                donor=str(donor_path),
                mode=mode,
                target=target.name,
                gate_line=gate,
            )
            candidates.append(candidate)
            produced.append({"mode": mode, "sha256": identity, "gate_line": gate})
            if len(candidates) >= limit:
                break
        if produced:
            donor_reports.append({
                "donor": str(donor_path),
                "donor_sha256": sha256(donor_raw),
                "target": target.name,
                "produced": produced,
            })
        if len(candidates) >= limit:
            break

    manifest = {
        "schema": "qym-first-error-harvest-manifest-v1",
        "current_sha256": sha256(current_raw),
        "current_error_headers": int(result.get("error_headers", 10**9)),
        "first_error": result.get("first_error"),
        "target": {
            "name": target.name,
            "start_line": target.start + 1,
            "end_line": target.end,
            "signature": current_signature,
        },
        "donor_files_scanned": len(donor_paths),
        "candidate_count": len(candidates),
        "donors_used": donor_reports,
        "candidates": [
            {
                "path": str(candidate.path),
                "sha256": candidate.sha256,
                "blob": candidate.blob,
                "donor": candidate.donor,
                "mode": candidate.mode,
                "target": candidate.target,
                "gate_line": candidate.gate_line,
            }
            for candidate in candidates
        ],
    }
    (out_dir / "MANIFEST.json").write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n"
    )
    return target, candidates, manifest


def compile_one(
    candidate: Candidate,
    out_dir: Path,
    project_root: Path,
    max_errors: int,
    timeout_seconds: int,
    baseline_errors: int,
    phase: str,
) -> tuple[Candidate, dict]:
    identity_dir = out_dir / candidate.sha256
    identity_dir.mkdir(parents=True, exist_ok=True)
    log_path = identity_dir / f"{phase}.log"
    exit_path = identity_dir / f"{phase}.exit"
    time_path = identity_dir / f"{phase}.seconds"
    olean = identity_dir / f"{phase}.olean"
    ilean = identity_dir / f"{phase}.ilean"
    command = [
        "lake", "env", "lean",
        f"-DmaxErrors={max_errors}",
        "-DwarningAsError=false",
        "-o", str(olean),
        "-i", str(ilean),
        str(candidate.path),
    ]
    started = time.monotonic()
    with log_path.open("wb") as log:
        try:
            process = subprocess.run(
                command,
                cwd=project_root,
                stdout=log,
                stderr=subprocess.STDOUT,
                timeout=timeout_seconds,
                check=False,
            )
            exit_code = process.returncode
        except subprocess.TimeoutExpired:
            exit_code = 124
            log.write(b"\nQYM_HARVEST_TIMEOUT\n")
    elapsed = time.monotonic() - started
    exit_path.write_text(str(exit_code) + "\n")
    time_path.write_text(f"{elapsed:.6f}\n")
    result = parse_log(log_path, exit_code, candidate, baseline_errors)
    result["phase"] = phase
    result["elapsed_seconds"] = elapsed
    result["source_path"] = str(candidate.path)
    (identity_dir / f"{phase}_RESULT.json").write_text(
        json.dumps({k: v for k, v in result.items() if k not in {"diagnostics", "panic_text"}},
                   indent=2, sort_keys=True) + "\n"
    )
    (identity_dir / f"{phase}_diagnostics.jsonl").write_text(
        "".join(json.dumps(row, sort_keys=True) + "\n" for row in result["diagnostics"])
    )
    return candidate, result


def local_gate_pass(result: dict, candidate: Candidate) -> bool:
    if int(result.get("panic_lines", 1)) != 0:
        return False
    first = result.get("first_error")
    return first is None or int(first.get("line", 0)) >= candidate.gate_line


def progress_over(candidate_result: dict, current_result: dict) -> bool:
    if int(candidate_result.get("panic_lines", 1)) != 0:
        return False
    if candidate_result.get("semantic_pass"):
        return True
    candidate_errors = int(candidate_result.get("error_headers", 10**9))
    current_errors = int(current_result.get("error_headers", 10**9))
    if candidate_errors < current_errors:
        return True
    if candidate_errors > current_errors:
        return False
    return first_error_line(candidate_result) > first_error_line(current_result)


def copy_result_without_bulk(result: dict) -> dict:
    return {k: v for k, v in result.items() if k not in {"diagnostics", "panic_text"}}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--current", required=True)
    parser.add_argument("--result", required=True)
    parser.add_argument("--donors", required=True)
    parser.add_argument("--work", required=True)
    parser.add_argument("--project-root", required=True)
    parser.add_argument("--rounds", type=int, default=8)
    parser.add_argument("--candidate-limit", type=int, default=48)
    parser.add_argument("--local-limit", type=int, default=24)
    parser.add_argument("--full-limit", type=int, default=4)
    parser.add_argument("--parallel-local", type=int, default=4)
    parser.add_argument("--parallel-full", type=int, default=2)
    args = parser.parse_args()

    current_path = Path(args.current).resolve()
    result_path = Path(args.result).resolve()
    donors_dir = Path(args.donors).resolve()
    work = Path(args.work).resolve()
    project_root = Path(args.project_root).resolve()
    work.mkdir(parents=True, exist_ok=True)

    current_result = json.loads(result_path.read_text())
    starting_result = dict(current_result)
    starting_sha = sha256(current_path.read_bytes())
    donor_paths = sorted(
        p for p in donors_dir.rglob("*.lean")
        if p.is_file() and p.stat().st_size > 100_000
    )
    # Deduplicate donor bytes before any expensive compilation.
    unique_donors: list[Path] = []
    seen_donors: set[str] = set()
    for path in donor_paths:
        identity = sha256(path.read_bytes())
        if identity in seen_donors:
            continue
        seen_donors.add(identity)
        unique_donors.append(path)
    donor_paths = unique_donors

    rounds_report = []
    visited_sources = {starting_sha}
    best_error_result = dict(current_result)
    best_error_source = current_path.read_bytes()

    for round_index in range(1, args.rounds + 1):
        round_dir = work / f"round-{round_index:02d}"
        candidate_dir = round_dir / "candidates"
        local_dir = round_dir / "local"
        full_dir = round_dir / "full"
        target, candidates, manifest = generate_candidates(
            current_path,
            current_result,
            donor_paths,
            candidate_dir,
            args.candidate_limit,
        )
        if not candidates:
            rounds_report.append({
                "round": round_index,
                "status": "no_candidates",
                "target": target.name,
                "manifest": manifest,
            })
            break

        candidates = candidates[: args.local_limit]
        local_results: list[tuple[Candidate, dict]] = []
        with ThreadPoolExecutor(max_workers=args.parallel_local) as executor:
            futures = {
                executor.submit(
                    compile_one,
                    candidate,
                    local_dir,
                    project_root,
                    1,
                    2400,
                    int(current_result.get("error_headers", 10**9)),
                    "local",
                ): candidate
                for candidate in candidates
            }
            for future in as_completed(futures):
                try:
                    local_results.append(future.result())
                except Exception as error:
                    candidate = futures[future]
                    local_results.append((candidate, {
                        "candidate_qym_sha256": candidate.sha256,
                        "panic_lines": 1,
                        "exception": repr(error),
                    }))

        survivors = [
            (candidate, result)
            for candidate, result in local_results
            if local_gate_pass(result, candidate)
        ]
        survivors.sort(key=lambda pair: (
            0 if pair[1].get("first_error") is None else 1,
            -first_error_line(pair[1]),
            float(pair[1].get("elapsed_seconds", 10**9)),
            pair[0].sha256,
        ))
        survivors = survivors[: args.full_limit]
        if not survivors:
            rounds_report.append({
                "round": round_index,
                "status": "no_local_survivor",
                "target": target.name,
                "candidate_count": len(candidates),
                "local_results": [copy_result_without_bulk(r) for _, r in local_results],
            })
            break

        full_results: list[tuple[Candidate, dict]] = []
        with ThreadPoolExecutor(max_workers=args.parallel_full) as executor:
            futures = {
                executor.submit(
                    compile_one,
                    candidate,
                    full_dir,
                    project_root,
                    10000,
                    7200,
                    int(current_result.get("error_headers", 10**9)),
                    "full",
                ): candidate
                for candidate, _ in survivors
            }
            for future in as_completed(futures):
                try:
                    full_results.append(future.result())
                except Exception as error:
                    candidate = futures[future]
                    full_results.append((candidate, {
                        "candidate_qym_sha256": candidate.sha256,
                        "panic_lines": 1,
                        "error_headers": 10**9,
                        "exception": repr(error),
                    }))

        progressing = [
            (candidate, result)
            for candidate, result in full_results
            if progress_over(result, current_result)
        ]
        progressing.sort(key=lambda pair: score(pair[1]))
        round_summary = {
            "round": round_index,
            "target": target.name,
            "candidate_count": len(candidates),
            "local_survivor_count": len(survivors),
            "full_result_count": len(full_results),
            "current_before": copy_result_without_bulk(current_result),
            "full_results": [copy_result_without_bulk(result) for _, result in full_results],
        }
        if not progressing:
            round_summary["status"] = "no_full_progress"
            rounds_report.append(round_summary)
            break

        winner, winner_result = progressing[0]
        winner_raw = winner.path.read_bytes()
        if winner.sha256 in visited_sources:
            round_summary["status"] = "cycle_detected"
            round_summary["winner"] = copy_result_without_bulk(winner_result)
            rounds_report.append(round_summary)
            break
        visited_sources.add(winner.sha256)
        current_path.write_bytes(winner_raw)
        current_result = copy_result_without_bulk(winner_result)
        current_result["frontier_progress"] = True
        current_result["round"] = round_index
        result_path.write_text(json.dumps(current_result, indent=2, sort_keys=True) + "\n")

        if score(current_result) < score(best_error_result):
            best_error_result = dict(current_result)
            best_error_source = winner_raw

        round_summary["status"] = "advanced"
        round_summary["winner"] = current_result
        rounds_report.append(round_summary)
        (round_dir / "ROUND_RESULT.json").write_text(
            json.dumps(round_summary, indent=2, sort_keys=True) + "\n"
        )
        if current_result.get("semantic_pass") or int(current_result.get("error_headers", 1)) == 0:
            break

    # Preserve the best error-count source, not merely a tie-progress working source.
    final_errors = int(current_result.get("error_headers", 10**9))
    best_errors = int(best_error_result.get("error_headers", 10**9))
    if best_errors < final_errors:
        current_path.write_bytes(best_error_source)
        current_result = dict(best_error_result)
        result_path.write_text(json.dumps(current_result, indent=2, sort_keys=True) + "\n")

    final_sha = sha256(current_path.read_bytes())
    final_report = {
        "schema": "qym-first-error-harvest-loop-v1",
        "starting_sha256": starting_sha,
        "starting_error_headers": int(starting_result.get("error_headers", 10**9)),
        "starting_first_error": starting_result.get("first_error"),
        "final_sha256": final_sha,
        "final_error_headers": int(current_result.get("error_headers", 10**9)),
        "final_first_error": current_result.get("first_error"),
        "semantic_pass": bool(current_result.get("semantic_pass")),
        "strict_error_improvement": (
            bool(current_result.get("semantic_pass")) or
            int(current_result.get("error_headers", 10**9)) <
                int(starting_result.get("error_headers", 10**9))
        ),
        "donor_count": len(donor_paths),
        "rounds": rounds_report,
    }
    (work / "HARVEST_RESULT.json").write_text(
        json.dumps(final_report, indent=2, sort_keys=True) + "\n"
    )
    (work / "FINAL_RESULT.json").write_text(
        json.dumps(current_result, indent=2, sort_keys=True) + "\n"
    )
    shutil.copy2(current_path, work / "QYM.HARVEST_BEST.lean")
    print(json.dumps(final_report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
