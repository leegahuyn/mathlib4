from __future__ import annotations

import re
from pathlib import Path
from typing import Iterable

import fa413_strict_transplant_tournament_v4 as v4

core = v4.core
_original_compile_fa = core.compile_fa


def compile_first_error(label: str, max_errors: int = 1):
    """Tournament candidates are ranked only by the first actual Lean error.

    Candidate/baseline probes therefore stop at one error.  The selected source is
    replayed with the full requested diagnostic budget before any promotion or 2x gate.
    """
    full = label == "final-fa-authoritative" or label.endswith("-authoritative")
    return _original_compile_fa(label, max_errors=500 if full else 1)


def _changed_script_donors(ref: str) -> Iterable[tuple[str, str]]:
    for item in core.scripted_donors(ref):
        yield item


def _branch_source(ref: str) -> tuple[str, str] | None:
    path = str(core.TARGET.relative_to(core.ROOT))
    text = core.git_show(ref, path)
    if text is None:
        return None
    return (ref, text)


def _history_commits(limit: int = 900) -> list[tuple[str, str]]:
    path = str(core.TARGET.relative_to(core.ROOT))
    proc = core.run(
        [
            "git",
            "log",
            "--all",
            f"--max-count={limit}",
            "--format=%H%x09%s",
            "--",
            path,
        ],
        timeout=300,
    )
    if proc.returncode != 0:
        return []
    rows: list[tuple[str, str]] = []
    seen: set[str] = set()
    for line in proc.stdout.splitlines():
        sha, _, subject = line.partition("\t")
        if not re.fullmatch(r"[0-9a-f]{40}", sha) or sha in seen:
            continue
        seen.add(sha)
        rows.append((sha, subject))

    def score(row: tuple[str, str]) -> tuple[int, int]:
        _, subject = row
        lower = subject.lower()
        nums = [int(x) for x in re.findall(r"(?:pass|fa)[ _-]?(\d+)", lower)]
        number = max(nums) if nums else -1
        relevance = sum(
            token in lower
            for token in (
                "functional",
                "frontier",
                "champion",
                "repair",
                "paired",
                "pass",
                "fa",
            )
        )
        return (relevance, number)

    # Git log is already newest first; stable sorting only lifts relevant repair commits.
    return sorted(rows, key=score, reverse=True)


def donor_sources(branches: list[str]) -> Iterable[tuple[str, str]]:
    yielded: set[str] = set()

    # First materialize the two deterministic post-PASS376 repair families.
    preferred = [b for b in branches if "fa411" in b or "fa412" in b]
    for ref in preferred:
        item = _branch_source(ref)
        if item is not None:
            label, text = item
            digest = core.hashlib.sha256(text.encode("utf-8")).hexdigest()
            if digest not in yielded:
                yielded.add(digest)
                yield label, text
        for label, text in _changed_script_donors(ref):
            digest = core.hashlib.sha256(text.encode("utf-8")).hexdigest()
            if digest not in yielded:
                yielded.add(digest)
                yield label, text

    # Then mine every reachable historical version of the FA file, not merely branch tips.
    path = str(core.TARGET.relative_to(core.ROOT))
    for commit, subject in _history_commits():
        text = core.git_show(commit, path)
        if text is None:
            continue
        digest = core.hashlib.sha256(text.encode("utf-8")).hexdigest()
        if digest in yielded:
            continue
        yielded.add(digest)
        yield f"history:{commit}:{subject}", text

    # Finally retain all other current branch heads as a fallback.
    for ref in branches:
        if ref in preferred:
            continue
        item = _branch_source(ref)
        if item is None:
            continue
        label, text = item
        digest = core.hashlib.sha256(text.encode("utf-8")).hexdigest()
        if digest in yielded:
            continue
        yielded.add(digest)
        yield label, text


core.compile_fa = compile_first_error
core.donor_sources = donor_sources

if __name__ == "__main__":
    raise SystemExit(core.main())
