from __future__ import annotations

import hashlib
import json
import os
import re
from dataclasses import asdict
from pathlib import Path
from typing import Any, Iterable

import fa419_lsp_fixed_tournament as fixed

base = fixed.base
core = base.core
ROOT = core.ROOT
TARGET = core.TARGET
OUT = ROOT / "build-logs" / "fa422-canonical-decl"
OUT.mkdir(parents=True, exist_ok=True)
FLOOR_LINE = 31725
MAX_FRONTIERS = int(os.environ.get("FA422_MAX_FRONTIERS", "80"))
MAX_CANDIDATES = int(os.environ.get("FA422_MAX_CANDIDATES", "500"))
DIRECT_FALLBACK = int(os.environ.get("FA422_DIRECT_FALLBACK", "20"))
PROOF_RE = re.compile(r":=\s*by\b")


def sha256(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def declarations(text: str) -> list[Any]:
    return core.declarations(text)


def manifest(text: str) -> tuple[tuple[str, str | None, str], ...]:
    return tuple((d.kind, d.name, d.header) for d in declarations(text))


def decl_index_at(text: str, line: int | None) -> int | None:
    if line is None:
        return None
    idx = max(0, line - 1)
    ds = declarations(text)
    for i, d in enumerate(ds):
        if d.start <= idx < d.end:
            return i
    prior = [i for i, d in enumerate(ds) if d.start <= idx]
    return prior[-1] if prior else None


def same_name_declarations(text: str, wanted: Any) -> Iterable[Any]:
    if wanted.name is None:
        return []
    return [d for d in declarations(text) if d.kind == wanted.kind and d.name == wanted.name]


def transplant_body(source: str, current: Any, donor: str, donor_decl: Any) -> str | None:
    source_lines = source.splitlines()
    donor_lines = donor.splitlines()
    current_block = "\n".join(source_lines[current.start : current.end])
    donor_block = "\n".join(donor_lines[donor_decl.start : donor_decl.end])
    cm = PROOF_RE.search(current_block)
    dm = PROOF_RE.search(donor_block)
    if cm is None or dm is None:
        return None
    block = current_block[: cm.end()] + donor_block[dm.end() :]
    rebuilt = source_lines[: current.start] + block.splitlines() + source_lines[current.end :]
    candidate = "\n".join(rebuilt) + ("\n" if source.endswith("\n") else "")
    # The theorem/definition statement sequence must remain exactly unchanged.
    if manifest(candidate) != manifest(source):
        return None
    return candidate


def collect_candidates(source: str, current: Any, branches: list[str]) -> list[tuple[str, str]]:
    expected_imports = core.imports(source)
    result: list[tuple[str, str]] = []
    seen = {sha256(source)}

    # First retain the original exact-header, same-height candidates and generic instance repairs.
    for label, candidate in base.collect_candidates(source, current, branches, MAX_CANDIDATES):
        digest = sha256(candidate)
        if digest in seen:
            continue
        if manifest(candidate) != manifest(source):
            continue
        seen.add(digest)
        result.append((f"fixed-height:{label}", candidate))
        if len(result) >= MAX_CANDIDATES:
            return result

    # Then allow longer/shorter proof scripts, while keeping the current declaration statement.
    for label, donor in core.donor_sources(branches):
        if len(result) >= MAX_CANDIDATES:
            break
        if not core.valid_donor(donor, expected_imports):
            continue
        for donor_decl in same_name_declarations(donor, current):
            candidate = transplant_body(source, current, donor, donor_decl)
            if candidate is None:
                continue
            digest = sha256(candidate)
            if digest in seen:
                continue
            if core.imports(candidate) != expected_imports:
                continue
            if any(core.forbidden_hits(candidate).values()):
                continue
            seen.add(digest)
            result.append((f"variable-height-body:{label}", candidate))
            if len(result) >= MAX_CANDIDATES:
                break
    return result


def cli_probe(label: str):
    return core.compile_fa(label, max_errors=1)


def full_cli(label: str):
    return base.history._original_compile_fa(label, max_errors=500)


def advances(
    metric: Any,
    candidate_source: str,
    champion_metric: Any,
    champion_source: str,
    champion_decl_index: int,
) -> tuple[bool, int | None]:
    if metric.passed:
        return True, None
    candidate_index = decl_index_at(candidate_source, metric.first_line)
    if metric.first_line is None or candidate_index is None or champion_metric.first_line is None:
        return False, candidate_index
    # Raw line must advance as the user requested.  In addition, variable-height candidates
    # must move the error to a genuinely later declaration, preventing blank-line inflation.
    if metric.first_line <= champion_metric.first_line:
        return False, candidate_index
    if candidate_index > champion_decl_index:
        return True, candidate_index
    # A later point inside the same declaration is accepted only when file height is unchanged.
    same_height = len(candidate_source.splitlines()) == len(champion_source.splitlines())
    return same_height and candidate_index == champion_decl_index, candidate_index


def lsp_summary(diags: list[dict[str, Any]], source: str) -> dict[str, Any]:
    first = base.first_lsp_error(diags)
    line = base.error_line(first) if first else None
    return {
        "error_count": sum(int(d.get("severity", 1)) == 1 for d in diags),
        "first_line": line,
        "first_col": base.error_col(first) if first else None,
        "first_message": str(first.get("message", "")) if first else "",
        "first_decl_index": decl_index_at(source, line),
    }


def main() -> int:
    source = TARGET.read_text(encoding="utf-8")
    starting_sha = sha256(source)
    if any(core.forbidden_hits(source).values()):
        raise SystemExit(f"forbidden token in starting source: {core.forbidden_hits(source)}")
    immutable_manifest = manifest(source)
    prerequisites = core.verify_prerequisites()
    branches = core.remote_branches()

    champion = cli_probe("fa422-baseline-first-error")
    if not champion.passed and (champion.first_line is None or champion.first_line < FLOOR_LINE):
        raise SystemExit(f"starting source below PASS376 floor: {champion}")
    champion_index = decl_index_at(source, champion.first_line)
    if not champion.passed and champion_index is None:
        raise SystemExit("could not map baseline error to a declaration")

    lsp = base.LeanLsp(ROOT, OUT / "lean-lsp.stderr.log")
    frontiers: list[dict[str, Any]] = []
    any_promotion = False
    try:
        lsp.initialize()
        diagnostics = lsp.open(source)
        for frontier in range(1, MAX_FRONTIERS + 1):
            if champion.passed:
                break
            assert champion.first_line is not None and champion_index is not None
            current_decls = declarations(source)
            if champion_index >= len(current_decls):
                break
            current = current_decls[champion_index]
            candidates = collect_candidates(source, current, branches)
            tested: list[dict[str, Any]] = []
            promoted = False
            fallback_used = 0

            for number, (label, candidate) in enumerate(candidates, 1):
                candidate_diags = lsp.change(candidate)
                summary = lsp_summary(candidate_diags, candidate)
                lsp_idx = summary["first_decl_index"]
                lsp_line = summary["first_line"]
                lsp_promising = lsp_line is None or (
                    isinstance(lsp_line, int)
                    and lsp_line > champion.first_line
                    and isinstance(lsp_idx, int)
                    and (
                        lsp_idx > champion_index
                        or (
                            lsp_idx == champion_index
                            and len(candidate.splitlines()) == len(source.splitlines())
                        )
                    )
                )
                # A small direct fallback prevents an imperfect LSP diagnostic from hiding all
                # candidates.  Direct CLI remains the sole authority in every case.
                should_compile = lsp_promising or fallback_used < DIRECT_FALLBACK
                row: dict[str, Any] = {
                    "number": number,
                    "label": label,
                    "sha256": sha256(candidate),
                    "line_count": len(candidate.splitlines()),
                    "lsp": summary,
                    "lsp_promising": lsp_promising,
                }
                if should_compile:
                    if not lsp_promising:
                        fallback_used += 1
                    TARGET.write_text(candidate, encoding="utf-8")
                    metric = cli_probe(f"frontier-{frontier:02d}-candidate-{number:03d}")
                    better, candidate_index = advances(
                        metric, candidate, champion, source, champion_index
                    )
                    row["direct_cli"] = asdict(metric)
                    row["direct_decl_index"] = candidate_index
                    row["direct_strictly_better"] = better
                    tested.append(row)
                    if better:
                        source = candidate
                        champion = metric
                        champion_index = candidate_index
                        diagnostics = candidate_diags
                        promoted = True
                        any_promotion = True
                        (OUT / f"frontier-{frontier:02d}-PROMOTED.txt").write_text(
                            f"label={label}\nsha256={metric.source_sha256}\n"
                            f"exit_code={metric.exit_code}\nfirst_error={metric.first_line}:{metric.first_col}\n"
                            f"declaration_index={candidate_index}\n",
                            encoding="utf-8",
                        )
                        break
                    TARGET.write_text(source, encoding="utf-8")
                    diagnostics = lsp.change(source)
                else:
                    tested.append(row)
                    diagnostics = lsp.change(source)

            frontiers.append(
                {
                    "frontier": frontier,
                    "current_declaration_index": champion_index,
                    "current_declaration": asdict(current),
                    "candidate_count": len(candidates),
                    "promoted": promoted,
                    "champion_after": asdict(champion),
                    "tested": tested,
                }
            )
            if not promoted:
                break
    finally:
        lsp.close()

    TARGET.write_text(source, encoding="utf-8")
    if manifest(source) != immutable_manifest:
        raise SystemExit("declaration statement manifest changed")
    authoritative = full_cli("fa422-final-authoritative")
    final_index = decl_index_at(source, authoritative.first_line)
    if not authoritative.passed and (
        authoritative.first_line is None
        or authoritative.first_line < FLOOR_LINE
        or final_index is None
    ):
        raise SystemExit(f"authoritative replay regressed: {authoritative}")

    complete = False
    two_pass: dict[str, list[dict[str, Any]]] = {}
    downstream_failure: str | None = None
    if authoritative.passed:
        try:
            two_pass = core.verify_all_twice()
            complete = True
            (OUT / "ALL_REQUIRED_TARGETS_2X_PASS").write_text(
                "\n".join(f"{name}=PASSx2" for name in two_pass) + "\n",
                encoding="utf-8",
            )
        except Exception as exc:
            downstream_failure = repr(exc)

    lines = source.splitlines()
    line = authoritative.first_line or 1
    start, end = max(1, line - 60), min(len(lines), line + 90)
    (OUT / "FIRST_ERROR_CONTEXT.txt").write_text(
        "\n".join(f"{i}: {lines[i - 1]}" for i in range(start, end + 1)),
        encoding="utf-8",
    )
    status = {
        "complete": complete,
        "stage": "ALL_REQUIRED_TARGETS_2X_PASS" if complete else "Mock2_FunctionalAnalysis",
        "starting_sha256": starting_sha,
        "final_sha256": authoritative.source_sha256,
        "immutable_floor_first_error": FLOOR_LINE,
        "statement_policy": "declaration header manifest unchanged; only proof bodies may vary",
        "promotion_policy": "direct CLI exit 0, or raw first error later and genuinely later declaration; same-declaration movement requires same file height",
        "lsp_policy": "screening only; never promotion authority",
        "prerequisites": prerequisites,
        "any_promotion": any_promotion,
        "final_fa_metric": asdict(authoritative),
        "final_error_decl_index": final_index,
        "frontiers": frontiers,
        "forbidden_token_audit": core.forbidden_hits(source),
        "two_pass": two_pass,
        "downstream_failure": downstream_failure,
    }
    (OUT / "CURRENT.json").write_text(json.dumps(status, indent=2), encoding="utf-8")
    (OUT / "CURRENT.txt").write_text(
        f"complete={complete}\nstage={status['stage']}\nany_promotion={any_promotion}\n"
        f"fa_exit={authoritative.exit_code}\nfa_errors={authoritative.errors}\n"
        f"fa_first={authoritative.first_line}:{authoritative.first_col}\n"
        f"fa_decl_index={final_index}\nfa_sha256={authoritative.source_sha256}\n"
        f"downstream_failure={downstream_failure}\n",
        encoding="utf-8",
    )
    print(json.dumps(status, indent=2))
    return 0 if complete else 2


if __name__ == "__main__":
    raise SystemExit(main())
