from __future__ import annotations

import re
import sys
from dataclasses import dataclass
from pathlib import Path


TARGET_DECLARATIONS = (
    "Mock2Adv.Section7WorkaroundLedger.RequirementEvidence",
    "Mock2Adv.P0RepairLedger.RequirementEvidence",
)


@dataclass(frozen=True)
class UniverseReference:
    name: str
    arity: int


def split_level_arguments(raw: str) -> list[str]:
    """Split a Lean universe argument list on top-level commas."""
    args: list[str] = []
    start = 0
    paren = bracket = brace = 0
    for index, char in enumerate(raw):
        if char == "(":
            paren += 1
        elif char == ")":
            paren -= 1
        elif char == "[":
            bracket += 1
        elif char == "]":
            bracket -= 1
        elif char == "{":
            brace += 1
        elif char == "}":
            brace -= 1
        elif char == "," and paren == bracket == brace == 0:
            args.append(raw[start:index].strip())
            start = index + 1
    args.append(raw[start:].strip())
    return [arg for arg in args if arg]


def error_blocks(log_text: str) -> list[str]:
    starts: list[int] = []
    for declaration in TARGET_DECLARATIONS:
        marker = f"declaration `{declaration}` contains universe level metavariables"
        offset = 0
        while True:
            found = log_text.find(marker, offset)
            if found < 0:
                break
            starts.append(found)
            offset = found + len(marker)
    starts.sort()
    blocks: list[str] = []
    for index, start in enumerate(starts):
        finish = starts[index + 1] if index + 1 < len(starts) else len(log_text)
        blocks.append(log_text[start:finish])
    return blocks


def universe_references(log_text: str) -> list[UniverseReference]:
    references: dict[str, int] = {}
    # Lean pretty-prints universe applications as `Name.{u, ?u.123, ...}`.
    # Keep only applications whose level list still contains a metavariable.
    application = re.compile(
        r"(?<![A-Za-z0-9_'])"
        r"(@?[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)"
        r"\.\{([^}\n]+)\}"
    )
    for block in error_blocks(log_text):
        for match in application.finditer(block):
            raw_name = match.group(1).lstrip("@")
            levels = match.group(2)
            if "?" not in levels:
                continue
            arity = len(split_level_arguments(levels))
            if arity <= 0:
                continue
            previous = references.get(raw_name)
            if previous is not None and previous != arity:
                raise RuntimeError(
                    f"inconsistent universe arity for {raw_name}: {previous} and {arity}"
                )
            references[raw_name] = arity
    return [UniverseReference(name, arity) for name, arity in sorted(references.items())]


def namespace_span(source: str, namespace: str) -> tuple[int, int]:
    start_marker = f"namespace {namespace}"
    end_marker = f"end {namespace}"
    start = source.find(start_marker)
    if start < 0:
        raise RuntimeError(f"missing namespace marker: {start_marker}")
    end = source.find(end_marker, start)
    if end < 0:
        raise RuntimeError(f"missing namespace marker: {end_marker}")
    return start, end + len(end_marker)


def candidate_spellings(full_name: str) -> list[str]:
    parts = full_name.split(".")
    values: list[str] = []
    for width in range(len(parts), 0, -1):
        spelling = ".".join(parts[-width:])
        if spelling not in values:
            values.append(spelling)
    return values


def specialize_in_block(block: str, reference: UniverseReference) -> tuple[str, int, str | None]:
    replacement_levels = ", ".join("0" for _ in range(reference.arity))
    for spelling in candidate_spellings(reference.name):
        # Prefer explicit applications. This is the form used by the evidence ledger.
        explicit = re.compile(rf"@{re.escape(spelling)}(?!\.\{{)")
        matches = list(explicit.finditer(block))
        if matches:
            block = explicit.sub(f"@{spelling}.{{{replacement_levels}}}", block)
            return block, len(matches), spelling

        # Some type constructors and a few theorem aliases are written without `@`.
        # Restrict this fallback to tokens immediately used inside a KernelEvidence
        # expression or a proposition/type annotation in the two small ledger blocks.
        bare = re.compile(
            rf"(?<![A-Za-z0-9_'.]){re.escape(spelling)}(?![A-Za-z0-9_']|\.\{{)"
        )
        bare_matches = list(bare.finditer(block))
        if bare_matches:
            selected: list[tuple[int, int]] = []
            for match in bare_matches:
                lo = max(0, match.start() - 160)
                hi = min(len(block), match.end() + 160)
                context = block[lo:hi]
                if (
                    "KernelEvidence" in context
                    or "RequirementEvidence" in context
                    or spelling in {"PUnit", "ULift", "PLift"}
                ):
                    selected.append((match.start(), match.end()))
            if selected:
                pieces: list[str] = []
                cursor = 0
                for start, end in selected:
                    pieces.append(block[cursor:start])
                    pieces.append(f"{spelling}.{{{replacement_levels}}}")
                    cursor = end
                pieces.append(block[cursor:])
                return "".join(pieces), len(selected), spelling
    return block, 0, None


def main() -> int:
    if len(sys.argv) != 3:
        print("usage: adaptive_mock2_advanced_universe_repair.py SOURCE LOG", file=sys.stderr)
        return 64

    source_path = Path(sys.argv[1])
    log_path = Path(sys.argv[2])
    source = source_path.read_text(encoding="utf-8")
    log_text = log_path.read_text(encoding="utf-8", errors="replace")

    blocks = error_blocks(log_text)
    if not blocks:
        print("no target RequirementEvidence universe-metavariable error found", file=sys.stderr)
        return 2

    references = universe_references(log_text)
    if not references:
        print("target errors were present, but no universe-meta constant application was parsed", file=sys.stderr)
        for block in blocks:
            print(block[-5000:], file=sys.stderr)
        return 3

    spans = [
        namespace_span(source, "Section7WorkaroundLedger"),
        namespace_span(source, "P0RepairLedger"),
    ]
    # Work from the end so replacing one block does not invalidate the other span.
    patches = 0
    applied: list[str] = []
    for start, end in sorted(spans, reverse=True):
        block = source[start:end]
        for reference in references:
            block, count, spelling = specialize_in_block(block, reference)
            if count:
                patches += count
                applied.append(
                    f"{spelling}.{{{', '.join('0' for _ in range(reference.arity))}}}: {count}"
                )
        source = source[:start] + block + source[end:]

    if patches == 0:
        print("parsed universe references but found no unspecialized source occurrence", file=sys.stderr)
        print("references:", file=sys.stderr)
        for reference in references:
            print(f"  {reference.name}: {reference.arity}", file=sys.stderr)
        return 4

    source_path.write_text(source, encoding="utf-8")
    print(f"specialized {patches} universe-polymorphic occurrence(s)")
    for item in applied:
        print(f"  {item}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
