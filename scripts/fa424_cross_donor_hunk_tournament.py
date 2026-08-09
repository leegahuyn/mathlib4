from __future__ import annotations

import difflib
import hashlib
import itertools
from dataclasses import dataclass
from typing import Any

import fa423_proof_hunk_tournament_v2 as prior

engine = prior.engine
core = prior.core
prior_collect = prior.collect_candidates


@dataclass(frozen=True)
class Edit:
    start: int
    end: int
    replacement: tuple[str, ...]
    label: str

    @property
    def key(self) -> tuple[int, int, tuple[str, ...]]:
        return self.start, self.end, self.replacement

    @property
    def weight(self) -> int:
        return (self.end - self.start) + len(self.replacement)


def sha256(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def proof_parts(source: str, declaration_index: int):
    ds = engine.declarations(source)
    if declaration_index >= len(ds):
        return None
    decl = ds[declaration_index]
    block = prior.mod.declaration_block(source, decl)
    parts = prior.mod.split_proof(block)
    if parts is None:
        return None
    return decl, parts[0], parts[1]


def declaration_index(source: str, current: Any) -> int:
    for i, decl in enumerate(engine.declarations(source)):
        if decl.start == current.start and decl.end == current.end and decl.header == current.header:
            return i
    raise ValueError("current declaration not found")


def edits_from_candidate(
    source: str,
    current_index: int,
    candidate: str,
    label: str,
) -> list[Edit]:
    source_parts = proof_parts(source, current_index)
    candidate_parts = proof_parts(candidate, current_index)
    if source_parts is None or candidate_parts is None:
        return []
    _, _, source_tail = source_parts
    _, _, candidate_tail = candidate_parts
    matcher = difflib.SequenceMatcher(a=source_tail, b=candidate_tail, autojunk=False)
    edits: list[Edit] = []
    for tag, i1, i2, j1, j2 in matcher.get_opcodes():
        if tag == "equal":
            continue
        edits.append(Edit(i1, i2, tuple(candidate_tail[j1:j2]), label))
    return edits


def nonoverlapping(edits: tuple[Edit, ...]) -> bool:
    intervals = sorted((e.start, e.end) for e in edits)
    for (_, end), (next_start, _) in zip(intervals, intervals[1:]):
        # Two insertions at the same position are considered overlapping because their
        # relative order is donor-dependent.
        if next_start < end or (end == next_start and end == intervals[0][0]):
            return False
    occupied_insertions = [e.start for e in edits if e.start == e.end]
    return len(occupied_insertions) == len(set(occupied_insertions))


def rebuild_from_edits(
    source: str,
    current_index: int,
    edits: tuple[Edit, ...],
) -> str | None:
    parts = proof_parts(source, current_index)
    if parts is None:
        return None
    current, prefix, tail = parts
    result = list(tail)
    for edit in sorted(edits, key=lambda e: (e.start, e.end), reverse=True):
        result[edit.start : edit.end] = list(edit.replacement)
    block = prefix + "\n".join(result)
    return prior.mod.rebuild_candidate(source, current, block)


def collect_candidates(source: str, current: Any, branches: list[str]):
    limit = engine.MAX_CANDIDATES
    current_index = declaration_index(source, current)
    seed_limit = min(max(250, limit // 4), 600)
    seeds = prior_collect(source, current, branches)[:seed_limit]

    atomic_by_key: dict[tuple[int, int, tuple[str, ...]], Edit] = {}
    for label, candidate in seeds:
        for edit in edits_from_candidate(source, current_index, candidate, label):
            old = atomic_by_key.get(edit.key)
            if old is None or edit.weight < old.weight:
                atomic_by_key[edit.key] = edit
    atomic = sorted(
        atomic_by_key.values(),
        key=lambda e: (e.weight, abs(e.start), e.label),
    )

    result: list[tuple[str, str]] = []
    seen = {sha256(source)}

    def add(label: str, candidate: str | None) -> bool:
        if candidate is None:
            return False
        digest = sha256(candidate)
        if digest in seen:
            return False
        if engine.manifest(candidate) != engine.manifest(source):
            return False
        if core.imports(candidate) != core.imports(source):
            return False
        if any(core.forbidden_hits(candidate).values()):
            return False
        seen.add(digest)
        result.append((label, candidate))
        return len(result) >= limit

    # Minimal atomic repairs first.
    for edit in atomic:
        if add(f"cross-atomic:{edit.label}", rebuild_from_edits(source, current_index, (edit,))):
            return result

    # Cross-donor pairs. Prefer small edits, but allow enough breadth to combine repairs
    # discovered in separate PASS lineages.
    pair_pool = atomic[: min(180, len(atomic))]
    for left_index, left in enumerate(pair_pool):
        for right in pair_pool[left_index + 1 :]:
            if left.label == right.label:
                continue
            edits = (left, right)
            if not nonoverlapping(edits):
                continue
            label = f"cross-pair:{left.label} + {right.label}"
            if add(label, rebuild_from_edits(source, current_index, edits)):
                return result

    # A narrow triple beam handles repairs with two prerequisites plus the failing line.
    triple_pool = atomic[: min(42, len(atomic))]
    for edits in itertools.combinations(triple_pool, 3):
        if len({e.label for e in edits}) < 2:
            continue
        if not nonoverlapping(edits):
            continue
        label = "cross-triple:" + " + ".join(e.label for e in edits)
        if add(label, rebuild_from_edits(source, current_index, edits)):
            return result

    # Retain the original donor/hunk candidates as the final part of the beam.
    for label, candidate in seeds:
        if add(f"seed:{label}", candidate):
            return result
    return result


engine.collect_candidates = collect_candidates

if __name__ == "__main__":
    raise SystemExit(engine.main())
