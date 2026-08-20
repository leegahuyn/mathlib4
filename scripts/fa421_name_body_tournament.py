from __future__ import annotations

import hashlib
import re
from typing import Iterable

import fa419_lsp_fixed_tournament as fixed

base = fixed.base
core = base.core
_original_collect = base.collect_candidates

PROOF_RE = re.compile(r":=\s*by\b")


def _same_name_declarations(text: str, wanted: object) -> Iterable[object]:
    name = getattr(wanted, "name", None)
    kind = getattr(wanted, "kind", None)
    if name is None:
        return []
    return [d for d in core.declarations(text) if d.name == name and d.kind == kind]


def _fit(lines: list[str], height: int) -> list[str] | None:
    result = list(lines)
    if len(result) > height:
        for predicate in (
            lambda line: not line.strip(),
            lambda line: line.lstrip().startswith("--")
            and not line.lstrip().startswith("--!"),
        ):
            removable = [i for i, line in enumerate(result) if predicate(line)]
            for i in reversed(removable):
                if len(result) <= height:
                    break
                del result[i]
    if len(result) > height:
        return None
    return result + [""] * (height - len(result))


def _transplant_body(
    current_source: str,
    current_decl: object,
    donor_source: str,
    donor_decl: object,
) -> str | None:
    current_lines = current_source.splitlines()
    donor_lines = donor_source.splitlines()
    current_block = "\n".join(current_lines[current_decl.start : current_decl.end])
    donor_block = "\n".join(donor_lines[donor_decl.start : donor_decl.end])
    current_match = PROOF_RE.search(current_block)
    donor_match = PROOF_RE.search(donor_block)
    if current_match is None or donor_match is None:
        return None

    # Keep the current theorem statement byte-for-byte through `:= by`; replace only
    # the proof script following it.  Thus signatures, assumptions and conclusions
    # cannot be weakened by a historical donor.
    replacement_block = (
        current_block[: current_match.end()]
        + donor_block[donor_match.end() :]
    )
    fitted = _fit(replacement_block.splitlines(), current_decl.lines)
    if fitted is None:
        return None
    if core.header_of(fitted) != current_decl.header:
        return None
    rebuilt = (
        current_lines[: current_decl.start]
        + fitted
        + current_lines[current_decl.end :]
    )
    result = "\n".join(rebuilt) + ("\n" if current_source.endswith("\n") else "")
    return result


def collect_candidates(
    source: str,
    declaration: object,
    branches: list[str],
    limit: int,
) -> list[tuple[str, str]]:
    candidates = _original_collect(source, declaration, branches, limit)
    seen = {hashlib.sha256(source.encode("utf-8")).hexdigest()}
    seen.update(hashlib.sha256(text.encode("utf-8")).hexdigest() for _, text in candidates)
    expected_imports = core.imports(source)

    for label, donor in core.donor_sources(branches):
        if len(candidates) >= limit:
            break
        if not core.valid_donor(donor, expected_imports):
            continue
        for donor_decl in _same_name_declarations(donor, declaration):
            candidate = _transplant_body(source, declaration, donor, donor_decl)
            if candidate is None:
                continue
            digest = hashlib.sha256(candidate.encode("utf-8")).hexdigest()
            if digest in seen:
                continue
            if core.imports(candidate) != expected_imports:
                continue
            if any(core.forbidden_hits(candidate).values()):
                continue
            # Recheck that the statement/header remains exactly the current one.
            enclosing = core.declaration_at(candidate, declaration.start + 1)
            if enclosing is None or enclosing.header != declaration.header:
                continue
            seen.add(digest)
            candidates.append((f"same-name-body:{label}", candidate))
            if len(candidates) >= limit:
                break
    return candidates


base.collect_candidates = collect_candidates

if __name__ == "__main__":
    raise SystemExit(base.main())
