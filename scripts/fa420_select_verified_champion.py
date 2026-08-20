from __future__ import annotations

import hashlib
import json
import re
import subprocess
from dataclasses import asdict
from pathlib import Path
from typing import Any

import fa413_strict_transplant_tournament as core

ROOT = core.ROOT
TARGET = core.TARGET
OUT = ROOT / "build-logs" / "fa420-evidence-controller"
OUT.mkdir(parents=True, exist_ok=True)
IMMUTABLE_REF = "origin/champion/fa-pass376-31725-07f6efd-immutable"
IMMUTABLE_SHA = "07f6efd3309c3cc23b86adf5811918b752b72c33a3f7a76213ce9beb10796da4"
FLOOR_LINE = 31725
SOURCE_PATH = str(TARGET.relative_to(ROOT))

CANDIDATE_REFS = [
    IMMUTABLE_REF,
    "origin/fix/fa411-from-pass376-champion-20260809",
    "origin/fix/fa412-broad-from-pass376-20260809",
    "origin/fix/fa413-strict-transplant-from-31725-20260809",
    "origin/fix/fa414-full-script-tournament-from-31725-20260809",
    "origin/fix/fa415-fast-strict-tournament-20260809",
    "origin/fix/fa416-autonomous-strict-chain-20260809",
    "origin/fix/fa417-history-mining-chain-20260809",
    "origin/fix/fa418-lsp-strict-chain-20260809",
    "origin/fix/fa419-lsp-fixed-chain-20260809",
]

KNOWN_EVIDENCE_PATHS = [
    "build-logs/pass376-champion-restore/CURRENT.json",
    "build-logs/fa411-from-pass376/CURRENT.json",
    "build-logs/fa412-broad-from-pass376/CURRENT.json",
    "build-logs/fa413-strict-transplant/CURRENT.json",
    "build-logs/fa414-full-script-tournament/CURRENT.json",
    "build-logs/fa415-fast-strict/CURRENT.json",
    "build-logs/fa416-autonomous/CURRENT.json",
    "build-logs/fa417-history-mining/CURRENT.json",
    "build-logs/fa418-lsp-strict/CURRENT.json",
    "build-logs/fa419-lsp-fixed/CURRENT.json",
]


def run(args: list[str], timeout: int = 900) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        args,
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=timeout,
        check=False,
    )


def git_show(ref: str, path: str) -> str | None:
    proc = run(["git", "show", f"{ref}:{path}"], timeout=180)
    return proc.stdout if proc.returncode == 0 else None


def sha256(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def manifest(text: str) -> tuple[tuple[str, str | None, str], ...]:
    return tuple((d.kind, d.name, d.header) for d in core.declarations(text))


def extract_metric(status: dict[str, Any]) -> dict[str, Any] | None:
    metric = status.get("final_fa_metric")
    if not isinstance(metric, dict):
        metric = status.get("selected_metric")
    if not isinstance(metric, dict):
        results = status.get("results")
        if isinstance(results, dict):
            metric = results.get("Mock2_FunctionalAnalysis")
    if not isinstance(metric, dict):
        return None
    return metric


def metric_sha(metric: dict[str, Any]) -> str | None:
    for key in ("source_sha256", "sha256", "fa_source_sha256"):
        value = metric.get(key)
        if isinstance(value, str) and re.fullmatch(r"[0-9a-f]{64}", value):
            return value
    return None


def evidence_for(ref: str) -> tuple[str | None, dict[str, Any] | None]:
    for path in KNOWN_EVIDENCE_PATHS:
        text = git_show(ref, path)
        if text is None:
            continue
        try:
            status = json.loads(text)
        except json.JSONDecodeError:
            continue
        if extract_metric(status) is not None:
            return path, status
    return None, None


def candidate_row(
    ref: str,
    baseline_lines: int,
    baseline_imports: tuple[str, ...],
    baseline_manifest: tuple[tuple[str, str | None, str], ...],
) -> dict[str, Any] | None:
    source = git_show(ref, SOURCE_PATH)
    if source is None:
        return None
    source_sha = sha256(source)
    path, status = evidence_for(ref)
    if ref == IMMUTABLE_REF and status is None:
        status = {
            "complete": False,
            "final_fa_metric": {
                "exit_code": 1,
                "errors": 1,
                "first_line": FLOOR_LINE,
                "first_col": 2,
                "source_sha256": IMMUTABLE_SHA,
            },
        }
        path = "immutable-known-evidence"
    if status is None:
        return None
    metric = extract_metric(status)
    if metric is None:
        return None
    claimed_sha = metric_sha(metric)
    if claimed_sha is not None and claimed_sha != source_sha:
        return {
            "ref": ref,
            "rejected": "evidence/source SHA mismatch",
            "source_sha256": source_sha,
            "claimed_sha256": claimed_sha,
            "evidence_path": path,
        }
    if core.imports(source) != baseline_imports:
        return {"ref": ref, "rejected": "import manifest changed", "source_sha256": source_sha}
    if manifest(source) != baseline_manifest:
        return {"ref": ref, "rejected": "declaration header manifest changed", "source_sha256": source_sha}
    audit = core.forbidden_hits(source)
    if any(audit.values()):
        return {"ref": ref, "rejected": f"forbidden executable tokens: {audit}", "source_sha256": source_sha}

    complete = bool(status.get("complete", False))
    exit_code = int(metric.get("exit_code", 1))
    first_line_raw = metric.get("first_line")
    first_line = int(first_line_raw) if isinstance(first_line_raw, int) else None
    line_count = len(source.splitlines())
    delta = line_count - baseline_lines
    normalized = None if first_line is None else first_line - max(0, delta)
    if not complete and (first_line is None or first_line < FLOOR_LINE or normalized < FLOOR_LINE):
        return {
            "ref": ref,
            "rejected": "claimed frontier below immutable floor",
            "source_sha256": source_sha,
            "claimed_first_line": first_line,
            "claimed_normalized_first_line": normalized,
        }
    return {
        "ref": ref,
        "source": source,
        "source_sha256": source_sha,
        "evidence_path": path,
        "complete": complete,
        "claimed_exit_code": exit_code,
        "claimed_first_line": first_line,
        "claimed_normalized_first_line": normalized,
        "line_count": line_count,
        "line_delta": delta,
    }


def rank(row: dict[str, Any]) -> tuple[int, int, int]:
    complete = int(bool(row.get("complete")))
    passed = int(int(row.get("claimed_exit_code", 1)) == 0)
    frontier = int(row.get("claimed_normalized_first_line") or -1)
    return complete, passed, frontier


def direct_probe(label: str, source: str, baseline_lines: int) -> tuple[core.Metric, int | None]:
    TARGET.write_text(source, encoding="utf-8")
    metric = core.compile_fa(label, max_errors=1)
    delta = len(source.splitlines()) - baseline_lines
    normalized = None if metric.first_line is None else metric.first_line - max(0, delta)
    return metric, normalized


def main() -> int:
    fetch = run(["git", "fetch", "origin", "+refs/heads/*:refs/remotes/origin/*", "--prune"], timeout=1200)
    if fetch.returncode != 0:
        raise SystemExit(fetch.stdout[-6000:])

    baseline = git_show(IMMUTABLE_REF, SOURCE_PATH)
    if baseline is None or sha256(baseline) != IMMUTABLE_SHA:
        raise SystemExit("immutable PASS376 source unavailable or SHA mismatch")
    baseline_lines = len(baseline.splitlines())
    baseline_imports = core.imports(baseline)
    baseline_manifest = manifest(baseline)

    rejected: list[dict[str, Any]] = []
    eligible: list[dict[str, Any]] = []
    for ref in CANDIDATE_REFS:
        row = candidate_row(ref, baseline_lines, baseline_imports, baseline_manifest)
        if row is None:
            continue
        if "rejected" in row:
            rejected.append(row)
        else:
            eligible.append(row)
    eligible.sort(key=rank, reverse=True)

    prerequisite_rows = core.verify_prerequisites()
    selected: dict[str, Any] | None = None
    probe_rows: list[dict[str, Any]] = []
    for index, row in enumerate(eligible, 1):
        metric, normalized = direct_probe(f"selection-candidate-{index:02d}", row["source"], baseline_lines)
        actual = {
            "ref": row["ref"],
            "source_sha256": row["source_sha256"],
            "evidence_path": row["evidence_path"],
            "claimed": {k: v for k, v in row.items() if k not in ("source",)},
            "direct_metric": asdict(metric),
            "direct_normalized_first_line": normalized,
        }
        probe_rows.append(actual)
        valid = metric.passed or (
            metric.first_line is not None
            and normalized is not None
            and metric.first_line >= FLOOR_LINE
            and normalized >= FLOOR_LINE
        )
        claim_reproduced = (
            metric.passed
            if row["complete"] or row["claimed_exit_code"] == 0
            else normalized is not None
            and normalized >= int(row["claimed_normalized_first_line"] or FLOOR_LINE)
        )
        if valid and claim_reproduced:
            selected = {**row, "direct_metric": asdict(metric), "direct_normalized_first_line": normalized}
            break

    if selected is None:
        metric, normalized = direct_probe("immutable-fallback", baseline, baseline_lines)
        if metric.first_line != FLOOR_LINE or normalized != FLOOR_LINE:
            raise SystemExit(f"immutable fallback failed authoritative replay: {metric}, normalized={normalized}")
        selected = {
            "ref": IMMUTABLE_REF,
            "source": baseline,
            "source_sha256": IMMUTABLE_SHA,
            "evidence_path": "immutable-known-evidence",
            "complete": False,
            "claimed_exit_code": 1,
            "claimed_first_line": FLOOR_LINE,
            "claimed_normalized_first_line": FLOOR_LINE,
            "line_count": baseline_lines,
            "line_delta": 0,
            "direct_metric": asdict(metric),
            "direct_normalized_first_line": normalized,
        }

    TARGET.write_text(selected["source"], encoding="utf-8")
    selected_public = {k: v for k, v in selected.items() if k != "source"}
    status = {
        "immutable": {"ref": IMMUTABLE_REF, "sha256": IMMUTABLE_SHA, "first_error_line": FLOOR_LINE},
        "selection_policy": "evidence SHA must match checked-in source; imports and declaration headers unchanged; direct Lean replay required",
        "prerequisites": prerequisite_rows,
        "selected": selected_public,
        "eligible_claims": [{k: v for k, v in r.items() if k != "source"} for r in eligible],
        "direct_probes": probe_rows,
        "rejected": rejected,
    }
    (OUT / "SELECTED.json").write_text(json.dumps(status, indent=2), encoding="utf-8")
    (OUT / "SELECTED.txt").write_text(
        f"ref={selected['ref']}\n"
        f"sha256={selected['source_sha256']}\n"
        f"direct_exit={selected['direct_metric']['exit_code']}\n"
        f"direct_first={selected['direct_metric']['first_line']}:{selected['direct_metric']['first_col']}\n"
        f"direct_normalized_first={selected['direct_normalized_first_line']}\n",
        encoding="utf-8",
    )
    print(json.dumps(status, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
