from __future__ import annotations

import re
import sys
from dataclasses import dataclass
from pathlib import Path


TARGET_DECLARATIONS = (
    "Mock2Adv.Section7WorkaroundLedger.RequirementEvidence",
    "Mock2Adv.P0RepairLedger.RequirementEvidence",
)
TARGET_NAMESPACES = (
    "Section7WorkaroundLedger",
    "P0RepairLedger",
)
SKIP_SUFFIXES = (
    "KernelEvidence",
    "RequirementEvidence",
    "Eq",
    "Iff",
    "Exists",
    "Nonempty",
)


@dataclass(frozen=True)
class UniverseReference:
    name: str
    arity: int


def split_level_arguments(raw: str) -> list[str]:
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
    return [
        log_text[start : starts[index + 1] if index + 1 < len(starts) else len(log_text)]
        for index, start in enumerate(starts)
    ]


def universe_references(log_text: str) -> list[UniverseReference]:
    references: dict[str, int] = {}
    application = re.compile(
        r"(?<![A-Za-z0-9_'])"
        r"@?([A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)"
        r"\.\{([^}\n]+)\}"
    )
    for block in error_blocks(log_text):
        for match in application.finditer(block):
            name = match.group(1)
            levels = match.group(2)
            if "?" not in levels or name.endswith(SKIP_SUFFIXES):
                continue
            arity = len(split_level_arguments(levels))
            if arity == 0:
                continue
            previous = references.get(name)
            if previous is not None and previous != arity:
                raise RuntimeError(f"inconsistent universe arity for {name}")
            references[name] = arity
    return [UniverseReference(name, arity) for name, arity in sorted(references.items())]


def namespace_span(source: str, namespace: str) -> tuple[int, int]:
    start_marker = f"namespace {namespace}"
    end_marker = f"end {namespace}"
    start = source.find(start_marker)
    if start < 0:
        raise RuntimeError(f"missing {start_marker}")
    end = source.find(end_marker, start)
    if end < 0:
        raise RuntimeError(f"missing {end_marker}")
    return start, end + len(end_marker)


def candidate_spellings(full_name: str) -> list[str]:
    parts = full_name.split(".")
    return [".".join(parts[-width:]) for width in range(len(parts), 0, -1)]


def specialize_explicit(block: str, reference: UniverseReference) -> tuple[str, int, str | None]:
    levels = ", ".join("0" for _ in range(reference.arity))
    for spelling in candidate_spellings(reference.name):
        pattern = re.compile(rf"@{re.escape(spelling)}(?!\.\{{)")
        count = len(pattern.findall(block))
        if count:
            return pattern.sub(f"@{spelling}.{{{levels}}}", block), count, spelling
    # Only these universe-carrying type constructors are safe as bare replacements.
    final = reference.name.rsplit(".", 1)[-1]
    if final in {"PUnit", "ULift", "PLift"}:
        pattern = re.compile(rf"(?<![A-Za-z0-9_'.]){final}(?![A-Za-z0-9_']|\.\{{)")
        count = len(pattern.findall(block))
        if count:
            return pattern.sub(f"{final}.{{{levels}}}", block), count, final
    return block, 0, None


def main() -> int:
    if len(sys.argv) != 3:
        print("usage: adaptive_mock2_advanced_universe_repair_v2.py SOURCE LOG", file=sys.stderr)
        return 64
    source_path = Path(sys.argv[1])
    log_path = Path(sys.argv[2])
    source = source_path.read_text(encoding="utf-8")
    log_text = log_path.read_text(encoding="utf-8", errors="replace")
    if not error_blocks(log_text):
        print("no target RequirementEvidence universe error", file=sys.stderr)
        return 2
    references = universe_references(log_text)
    if not references:
        print("no patchable universe-meta application found", file=sys.stderr)
        for block in error_blocks(log_text):
            print(block[-6000:], file=sys.stderr)
        return 3

    patches = 0
    applied: list[str] = []
    spans = [namespace_span(source, namespace) for namespace in TARGET_NAMESPACES]
    for start, end in sorted(spans, reverse=True):
        block = source[start:end]
        for reference in references:
            block, count, spelling = specialize_explicit(block, reference)
            if count:
                patches += count
                levels = ", ".join("0" for _ in range(reference.arity))
                applied.append(f"@{spelling}.{{{levels}}}: {count}")
        source = source[:start] + block + source[end:]

    if patches == 0:
        print("references parsed, but no unspecialized explicit source reference found", file=sys.stderr)
        for reference in references:
            print(f"  {reference.name}: {reference.arity}", file=sys.stderr)
        return 4
    source_path.write_text(source, encoding="utf-8")
    print(f"specialized {patches} explicit occurrence(s)")
    for item in applied:
        print(f"  {item}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
