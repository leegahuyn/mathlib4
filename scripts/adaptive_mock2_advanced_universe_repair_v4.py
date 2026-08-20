from __future__ import annotations

import re
import sys
from dataclasses import dataclass
from pathlib import Path


TARGETS = (
    ("Section7WorkaroundLedger", "Mock2Adv.Section7WorkaroundLedger.RequirementEvidence"),
    ("P0RepairLedger", "Mock2Adv.P0RepairLedger.RequirementEvidence"),
)
SKIP_FINAL_NAMES = {
    "KernelEvidence",
    "RequirementEvidence",
    "ClaimEvidence",
    "Eq",
    "Iff",
    "Exists",
    "Nonempty",
    "Sort",
    "Type",
    "Prop",
}
DECLARATION_KINDS = {
    "theorem",
    "lemma",
    "def",
    "abbrev",
    "opaque",
    "instance",
    "structure",
    "class",
    "inductive",
}
DECLARATION_PREFIXES = {"noncomputable", "private", "protected", "local"}


@dataclass(frozen=True)
class Reference:
    name: str
    arity: int


def split_levels(raw: str) -> list[str]:
    result: list[str] = []
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
            result.append(raw[start:index].strip())
            start = index + 1
    result.append(raw[start:].strip())
    return [item for item in result if item]


def error_blocks(log: str) -> list[str]:
    starts: list[int] = []
    for _, declaration in TARGETS:
        marker = f"declaration `{declaration}` contains universe level metavariables"
        cursor = 0
        while True:
            found = log.find(marker, cursor)
            if found < 0:
                break
            starts.append(found)
            cursor = found + len(marker)
    starts.sort()
    return [
        log[start : starts[index + 1] if index + 1 < len(starts) else len(log)]
        for index, start in enumerate(starts)
    ]


def references(log: str) -> list[Reference]:
    found: dict[str, int] = {}
    pattern = re.compile(
        r"(?<![A-Za-z0-9_'])"
        r"@?([A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)"
        r"\.\{([^}\n]+)\}"
    )
    for block in error_blocks(log):
        for match in pattern.finditer(block):
            name = match.group(1)
            raw_levels = match.group(2)
            if "?" not in raw_levels:
                continue
            if name.rsplit(".", 1)[-1] in SKIP_FINAL_NAMES:
                continue
            arity = len(split_levels(raw_levels))
            if arity <= 0:
                continue
            previous = found.get(name)
            if previous is not None and previous != arity:
                raise RuntimeError(
                    f"inconsistent universe arity for {name}: {previous}/{arity}"
                )
            found[name] = arity
    return [Reference(name, arity) for name, arity in sorted(found.items())]


def namespace_bounds(source: str, namespace: str) -> tuple[int, int]:
    start_marker = f"namespace {namespace}"
    end_marker = f"end {namespace}"
    start = source.find(start_marker)
    if start < 0:
        raise RuntimeError(f"missing {start_marker}")
    end = source.find(end_marker, start)
    if end < 0:
        raise RuntimeError(f"missing {end_marker}")
    return start, end


def starts_declaration(stripped: str) -> bool:
    if not stripped or stripped.startswith(("--", "/-", "@[")):
        return False
    first_line = stripped.splitlines()[0]
    tokens = first_line.replace("(", " ").replace(":", " ").split()
    index = 0
    while index < len(tokens) and tokens[index] in DECLARATION_PREFIXES:
        index += 1
    return index < len(tokens) and tokens[index] in DECLARATION_KINDS


def definition_bounds(source: str, namespace: str) -> tuple[int, int]:
    ns_start, ns_end = namespace_bounds(source, namespace)
    header = re.compile(
        r"(?m)^(?:(?:noncomputable|private|protected)\s+)*"
        r"(?:def|abbrev)\s+RequirementEvidence\b"
    )
    match = header.search(source, ns_start, ns_end)
    if not match:
        raise RuntimeError(f"missing {namespace}.RequirementEvidence definition")

    cursor = match.end()
    while cursor < ns_end:
        line_end = source.find("\n", cursor)
        if line_end < 0 or line_end > ns_end:
            line_end = ns_end
        line = source[cursor:line_end]
        stripped = line.strip()
        if stripped.startswith("end ") or starts_declaration(stripped):
            return match.start(), cursor
        cursor = line_end + 1
    return match.start(), ns_end


def spellings(full_name: str) -> list[str]:
    parts = full_name.split(".")
    return [".".join(parts[-width:]) for width in range(len(parts), 0, -1)]


def specialize(block: str, reference: Reference) -> tuple[str, int, str | None]:
    levels = ", ".join("0" for _ in range(reference.arity))
    for spelling in spellings(reference.name):
        explicit = re.compile(rf"@{re.escape(spelling)}(?!\.\{{)")
        count = len(explicit.findall(block))
        if count:
            return explicit.sub(f"@{spelling}.{{{levels}}}", block), count, f"@{spelling}"
    for spelling in spellings(reference.name):
        bare = re.compile(
            rf"(?<![A-Za-z0-9_'.]){re.escape(spelling)}"
            rf"(?![A-Za-z0-9_']|\.\{{)"
        )
        count = len(bare.findall(block))
        if count:
            return bare.sub(f"{spelling}.{{{levels}}}", block), count, spelling
    return block, 0, None


def main() -> int:
    if len(sys.argv) != 3:
        print(
            "usage: adaptive_mock2_advanced_universe_repair_v4.py SOURCE LOG",
            file=sys.stderr,
        )
        return 64
    source_path = Path(sys.argv[1])
    log_path = Path(sys.argv[2])
    source = source_path.read_text(encoding="utf-8")
    log = log_path.read_text(encoding="utf-8", errors="replace")
    blocks = error_blocks(log)
    if not blocks:
        print("no target RequirementEvidence universe error", file=sys.stderr)
        return 2
    refs = references(log)
    if not refs:
        print("no universe-meta reference parsed from target errors", file=sys.stderr)
        for block in blocks:
            print(block[-10000:], file=sys.stderr)
        return 3

    spans = [definition_bounds(source, namespace) for namespace, _ in TARGETS]
    patches = 0
    applied: list[str] = []
    for start, end in sorted(spans, reverse=True):
        block = source[start:end]
        for reference in refs:
            block, count, spelling = specialize(block, reference)
            if count:
                patches += count
                zeros = ", ".join("0" for _ in range(reference.arity))
                applied.append(f"{spelling}.{{{zeros}}}: {count}")
        source = source[:start] + block + source[end:]

    if patches == 0:
        print("parsed references but no body-scoped occurrence was patchable", file=sys.stderr)
        for reference in refs:
            print(f"  {reference.name}: {reference.arity}", file=sys.stderr)
        return 4
    source_path.write_text(source, encoding="utf-8")
    print(f"specialized {patches} body-scoped occurrence(s)")
    for item in applied:
        print(f"  {item}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
