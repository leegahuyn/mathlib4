from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path

TARGET_NAMESPACES = ("Section7WorkaroundLedger", "P0RepairLedger")
DECL_KINDS = {
    "theorem", "lemma", "def", "abbrev", "opaque", "instance",
    "structure", "class", "inductive",
}
DECL_PREFIXES = {"noncomputable", "private", "protected", "local"}
SKIP_NAMES = {
    "KernelEvidence", "RequirementEvidence", "Requirement", "Prop", "Sort", "Type",
    "Eq", "Iff", "Exists", "Nonempty",
}
QUALIFIED_NAME = r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*"


@dataclass(frozen=True)
class Candidate:
    ident: str
    namespace: str
    spelling: str
    explicit: bool


def starts_declaration(line: str) -> bool:
    stripped = line.strip()
    if not stripped or stripped.startswith(("--", "/-", "@[")):
        return False
    tokens = stripped.replace("(", " ").replace(":", " ").split()
    index = 0
    while index < len(tokens) and tokens[index] in DECL_PREFIXES:
        index += 1
    return index < len(tokens) and tokens[index] in DECL_KINDS


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


def definition_bounds(source: str, namespace: str) -> tuple[int, int]:
    ns_start, ns_end = namespace_bounds(source, namespace)
    header = re.compile(
        r"(?m)^(?:(?:noncomputable|private|protected)\s+)*"
        r"(?:def|abbrev)\s+RequirementEvidence\b"
    )
    match = header.search(source, ns_start, ns_end)
    if not match:
        raise RuntimeError(f"missing {namespace}.RequirementEvidence")
    cursor = source.find("\n", match.end())
    if cursor < 0:
        return match.start(), ns_end
    cursor += 1
    while cursor < ns_end:
        line_end = source.find("\n", cursor)
        if line_end < 0 or line_end > ns_end:
            line_end = ns_end
        line = source[cursor:line_end]
        if line.strip().startswith("end ") or starts_declaration(line):
            return match.start(), cursor
        cursor = line_end + 1
    return match.start(), ns_end


def collect_candidates(source: str, include_bare: bool) -> list[Candidate]:
    candidates: list[Candidate] = []
    seen: set[tuple[str, str, bool]] = set()
    explicit_pattern = re.compile(
        rf"@({QUALIFIED_NAME})(?![A-Za-z0-9_']|\.\{{)"
    )
    qualified_pattern = re.compile(
        r"(?<![A-Za-z0-9_'.])"
        r"([A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)+)"
        r"(?![A-Za-z0-9_']|\.\{)"
    )
    theorem_pattern = re.compile(
        r"(?<![A-Za-z0-9_'.])"
        r"([A-Za-z_][A-Za-z0-9_']*(?:_proved|_correctedAndProved|claimEvidence))"
        r"(?![A-Za-z0-9_']|\.\{)"
    )
    for namespace in TARGET_NAMESPACES:
        start, end = definition_bounds(source, namespace)
        block = source[start:end]
        for match in explicit_pattern.finditer(block):
            spelling = match.group(1)
            final = spelling.rsplit(".", 1)[-1]
            if final in SKIP_NAMES:
                continue
            key = (namespace, spelling, True)
            if key not in seen:
                seen.add(key)
                candidates.append(Candidate("", namespace, spelling, True))
        if not include_bare:
            continue
        for pattern in (qualified_pattern, theorem_pattern):
            for match in pattern.finditer(block):
                spelling = match.group(1)
                final = spelling.rsplit(".", 1)[-1]
                if final in SKIP_NAMES or spelling.startswith(("Requirement.", "KernelEvidence.")):
                    continue
                key = (namespace, spelling, False)
                if key not in seen:
                    seen.add(key)
                    candidates.append(Candidate("", namespace, spelling, False))
    return [
        Candidate(f"P{index:04d}", item.namespace, item.spelling, item.explicit)
        for index, item in enumerate(candidates)
    ]


def prepare(source_path: Path, probe_path: Path, map_path: Path, include_bare: bool) -> int:
    source = source_path.read_text(encoding="utf-8")
    candidates = collect_candidates(source, include_bare)
    if not candidates:
        print("no unspecialized probe candidates", file=sys.stderr)
        return 3
    insertions: list[tuple[int, str]] = []
    for namespace in TARGET_NAMESPACES:
        start, _ = definition_bounds(source, namespace)
        local = [item for item in candidates if item.namespace == namespace]
        if not local:
            continue
        lines = [""]
        for item in local:
            lines.append(f'#eval IO.println "UNIV_PROBE_BEGIN|{item.ident}"')
            lines.append(f"set_option pp.universes true in #check @{item.spelling}")
            lines.append(f'#eval IO.println "UNIV_PROBE_END|{item.ident}"')
        lines.append("")
        insertions.append((start, "\n".join(lines)))
    probe = source
    for offset, text in sorted(insertions, reverse=True):
        probe = probe[:offset] + text + probe[offset:]
    probe_path.write_text(probe, encoding="utf-8")
    map_path.write_text(
        json.dumps([item.__dict__ for item in candidates], ensure_ascii=False, indent=2),
        encoding="utf-8",
    )
    print(f"prepared {len(candidates)} universe probes")
    return 0


def split_levels(raw: str) -> list[str]:
    values: list[str] = []
    start = 0
    paren = bracket = brace = 0
    for index, char in enumerate(raw):
        if char == "(": paren += 1
        elif char == ")": paren -= 1
        elif char == "[": bracket += 1
        elif char == "]": bracket -= 1
        elif char == "{": brace += 1
        elif char == "}": brace -= 1
        elif char == "," and paren == bracket == brace == 0:
            values.append(raw[start:index].strip())
            start = index + 1
    values.append(raw[start:].strip())
    return [value for value in values if value]


def probe_arity(segment: str) -> int | None:
    match = re.search(
        rf"@?{QUALIFIED_NAME}\.\{{([^}}\n]+)\}}",
        segment,
    )
    if match:
        return len(split_levels(match.group(1)))
    if "error:" in segment.lower():
        return None
    return 0


def apply(source_path: Path, map_path: Path, log_path: Path) -> int:
    source = source_path.read_text(encoding="utf-8")
    log = log_path.read_text(encoding="utf-8", errors="replace")
    candidates = [Candidate(**item) for item in json.loads(map_path.read_text(encoding="utf-8"))]
    arities: dict[str, int] = {}
    for item in candidates:
        begin = f"UNIV_PROBE_BEGIN|{item.ident}"
        end = f"UNIV_PROBE_END|{item.ident}"
        begin_at = log.find(begin)
        end_at = log.find(end, begin_at + len(begin)) if begin_at >= 0 else -1
        if begin_at < 0 or end_at < 0:
            continue
        arity = probe_arity(log[begin_at + len(begin):end_at])
        if arity is not None and arity > 0:
            arities[item.ident] = arity
    if not arities:
        print("no positive universe arity was recovered from Lean probes", file=sys.stderr)
        return 4

    patches = 0
    applied: list[str] = []
    spans = {namespace: definition_bounds(source, namespace) for namespace in TARGET_NAMESPACES}
    for namespace, (start, end) in sorted(spans.items(), key=lambda pair: pair[1][0], reverse=True):
        block = source[start:end]
        for item in candidates:
            if item.namespace != namespace or item.ident not in arities:
                continue
            arity = arities[item.ident]
            levels = ", ".join("0" for _ in range(arity))
            if item.explicit:
                pattern = re.compile(
                    rf"@{re.escape(item.spelling)}(?![A-Za-z0-9_']|\.\{{)"
                )
                count = len(pattern.findall(block))
                if count:
                    block = pattern.sub(f"@{item.spelling}.{{{levels}}}", block)
            else:
                pattern = re.compile(
                    rf"(?<![A-Za-z0-9_'.]){re.escape(item.spelling)}"
                    rf"(?![A-Za-z0-9_']|\.\{{)"
                )
                count = len(pattern.findall(block))
                if count:
                    block = pattern.sub(f"{item.spelling}.{{{levels}}}", block)
            if count:
                patches += count
                applied.append(f"{namespace}: {item.spelling}.{{{levels}}} x{count}")
        source = source[:start] + block + source[end:]
    if not patches:
        print("Lean probes succeeded but no source occurrence was patchable", file=sys.stderr)
        return 5
    source_path.write_text(source, encoding="utf-8")
    print(f"applied {patches} Lean-probed universe specialization(s)")
    for line in applied:
        print(line)
    return 0


def main() -> int:
    parser = argparse.ArgumentParser()
    sub = parser.add_subparsers(dest="command", required=True)
    prep = sub.add_parser("prepare")
    prep.add_argument("source", type=Path)
    prep.add_argument("probe", type=Path)
    prep.add_argument("mapping", type=Path)
    prep.add_argument("--include-bare", action="store_true")
    app = sub.add_parser("apply")
    app.add_argument("source", type=Path)
    app.add_argument("mapping", type=Path)
    app.add_argument("log", type=Path)
    args = parser.parse_args()
    if args.command == "prepare":
        return prepare(args.source, args.probe, args.mapping, args.include_bare)
    return apply(args.source, args.mapping, args.log)


if __name__ == "__main__":
    raise SystemExit(main())
