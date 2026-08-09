from __future__ import annotations

import difflib
import hashlib
import itertools
import re
from typing import Any, Iterable

import fa422_canonical_decl_tournament as engine

core = engine.core
_original_collect = engine.collect_candidates
PROOF_RE = re.compile(r":=\s*by\b")


def sha256(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def split_proof(block: str) -> tuple[str, list[str]] | None:
    match = PROOF_RE.search(block)
    if match is None:
        return None
    prefix = block[: match.end()]
    tail = block[match.end() :]
    return prefix, tail.splitlines()


def declaration_block(text: str, decl: Any) -> str:
    return "\n".join(text.splitlines()[decl.start : decl.end])


def rebuild_candidate(source: str, current: Any, block: str) -> str | None:
    lines = source.splitlines()
    rebuilt = lines[: current.start] + block.splitlines() + lines[current.end :]
    candidate = "\n".join(rebuilt) + ("\n" if source.endswith("\n") else "")
    if engine.manifest(candidate) != engine.manifest(source):
        return None
    if core.imports(candidate) != core.imports(source):
        return None
    if any(core.forbidden_hits(candidate).values()):
        return None
    return candidate


def apply_hunks(
    current_tail: list[str],
    donor_tail: list[str],
    opcodes: list[tuple[str, int, int, int, int]],
    chosen: tuple[int, ...],
) -> list[str]:
    result = list(current_tail)
    for opcode_index in sorted(chosen, reverse=True):
        tag, i1, i2, j1, j2 = opcodes[opcode_index]
        if tag == "equal":
            continue
        result[i1:i2] = donor_tail[j1:j2]
    return result


def donor_hunk_candidates(
    source: str,
    current: Any,
    donor: str,
    donor_decl: Any,
    label: str,
) -> Iterable[tuple[str, str]]:
    current_parts = split_proof(declaration_block(source, current))
    donor_parts = split_proof(declaration_block(donor, donor_decl))
    if current_parts is None or donor_parts is None:
        return []
    current_prefix, current_tail = current_parts
    _, donor_tail = donor_parts
    matcher = difflib.SequenceMatcher(a=current_tail, b=donor_tail, autojunk=False)
    edits = [op for op in matcher.get_opcodes() if op[0] != "equal"]
    if not edits:
        return []

    plans: list[tuple[int, ...]] = []
    # Individual edits expose the minimal historical API repair.
    plans.extend((i,) for i in range(len(edits)))
    # Adjacent pairs and triples combine repairs that were split across nearby lines.
    plans.extend(tuple(range(i, min(i + 2, len(edits)))) for i in range(len(edits) - 1))
    plans.extend(tuple(range(i, min(i + 3, len(edits)))) for i in range(len(edits) - 2))
    # Cumulative prefixes/suffixes and the whole donor capture dependent hunk sequences.
    plans.extend(tuple(range(0, i)) for i in range(2, len(edits) + 1))
    plans.extend(tuple(range(i, len(edits))) for i in range(0, max(0, len(edits) - 1)))
    plans.append(tuple(range(len(edits))))

    seen_plans: set[tuple[int, ...]] = set()
    result: list[tuple[str, str]] = []
    for plan in plans:
        plan = tuple(sorted(set(plan)))
        if not plan or plan in seen_plans:
            continue
        seen_plans.add(plan)
        tail = apply_hunks(current_tail, donor_tail, edits, plan)
        block = current_prefix + "\n".join(tail)
        candidate = rebuild_candidate(source, current, block)
        if candidate is None:
            continue
        result.append((f"history-hunks:{label}:plan={','.join(map(str, plan))}", candidate))
    return result


def local_instance_candidates(source: str, current: Any) -> Iterable[tuple[str, str]]:
    block = declaration_block(source, current)
    parts = split_proof(block)
    if parts is None:
        return []
    prefix, tail = parts
    variants: list[tuple[str, list[str]]] = []

    patterns = {
        "drop-complex-addcommgroup": re.compile(
            r"^\s*(?:letI|haveI)\s*:\s*AddCommGroup\s+ℂ\s*[:=]"
        ),
        "drop-complex-real-module": re.compile(
            r"^\s*(?:letI|haveI)\s*:\s*Module\s+ℝ\s+ℂ\s*[:=]"
        ),
        "drop-completion-normedspace": re.compile(
            r"^\s*(?:letI|haveI)\s*:\s*NormedSpace\s+ℂ\s+.*Completion"
        ),
    }
    for name, pattern in patterns.items():
        mutated = [line for line in tail if not pattern.search(line)]
        if mutated != tail:
            variants.append((name, mutated))

    replacements = {
        "replace-legacy-complex-addcommgroup": (
            "Complex.addCommGroup",
            "Complex.instNormedAddCommGroup.toAddCommGroup",
        ),
        "replace-inferred-complex-addcommgroup": (
            "(inferInstance : AddCommGroup ℂ)",
            "Complex.instNormedAddCommGroup.toAddCommGroup",
        ),
        "qualify-completion-normedspace": (
            "UniformSpace.Completion.instNormedSpace",
            "UniformSpace.Completion.instNormedSpace",
        ),
    }
    for name, (old, new) in replacements.items():
        mutated = [line.replace(old, new) for line in tail]
        if mutated != tail:
            variants.append((name, mutated))

    result: list[tuple[str, str]] = []
    for name, mutated in variants:
        candidate = rebuild_candidate(source, current, prefix + "\n".join(mutated))
        if candidate is not None:
            result.append((f"local-instance:{name}", candidate))
    return result


def collect_candidates(source: str, current: Any, branches: list[str]) -> list[tuple[str, str]]:
    result = _original_collect(source, current, branches)
    seen = {sha256(source)}
    seen.update(sha256(candidate) for _, candidate in result)
    limit = engine.MAX_CANDIDATES

    for label, candidate in local_instance_candidates(source, current):
        digest = sha256(candidate)
        if digest not in seen:
            seen.add(digest)
            result.append((label, candidate))
            if len(result) >= limit:
                return result

    expected_imports = core.imports(source)
    for donor_label, donor in core.donor_sources(branches):
        if len(result) >= limit:
            break
        if not core.valid_donor(donor, expected_imports):
            continue
        for donor_decl in engine.same_name_declarations(donor, current):
            for label, candidate in donor_hunk_candidates(
                source, current, donor, donor_decl, donor_label
            ):
                digest = sha256(candidate)
                if digest in seen:
                    continue
                seen.add(digest)
                result.append((label, candidate))
                if len(result) >= limit:
                    break
            if len(result) >= limit:
                break
    return result


engine.collect_candidates = collect_candidates

if __name__ == "__main__":
    raise SystemExit(engine.main())
