from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "PrimalitySheafVerification" / "Spt5.lean"
OUTPUT = ROOT / ".lake" / "Spt5WholeFileAudit.lean"
MANIFEST = Path("/tmp/primality-final-local-gate/audit/Spt5-public-declarations.txt")


@dataclass
class Block:
    kind: str
    name: str | None
    namespace_parts: tuple[str, ...] = ()


def strip_prefix_comments(lines: list[str]) -> list[str]:
    result: list[str] = []
    depth = 0
    for raw in lines:
        index = 0
        out: list[str] = []
        in_string = False
        escaped = False
        while index < len(raw):
            if depth:
                if raw.startswith("/-", index):
                    depth += 1
                    index += 2
                elif raw.startswith("-/", index):
                    depth -= 1
                    index += 2
                else:
                    index += 1
            elif in_string:
                character = raw[index]
                if escaped:
                    escaped = False
                elif character == "\\":
                    escaped = True
                elif character == '"':
                    in_string = False
                out.append(" ")
                index += 1
            elif raw.startswith("/-", index):
                depth = 1
                index += 2
            elif raw.startswith("--", index):
                break
            elif raw[index] == '"':
                in_string = True
                out.append(" ")
                index += 1
            else:
                out.append(raw[index])
                index += 1
        result.append("".join(out))
    if depth:
        raise RuntimeError("unterminated nested comment in Spt5.lean")
    return result


def main() -> int:
    raw_lines = SOURCE.read_text(encoding="utf-8").splitlines()
    lines = strip_prefix_comments(raw_lines)
    blocks: list[Block] = []
    namespace: list[str] = []
    names: list[str] = []

    namespace_re = re.compile(r"^\s*namespace\s+([^\s]+)")
    section_re = re.compile(r"^\s*(?:noncomputable\s+)?section(?:\s+([^\s]+))?\s*$")
    end_re = re.compile(r"^\s*end(?:\s+([^\s]+))?\s*$")
    declaration_re = re.compile(
        r"^\s*(?:@\[[^\]]*\]\s*)*"
        r"(?P<mods>(?:(?:noncomputable|protected|nonrec|private|local)\s+)*)"
        r"(?P<kind>theorem|lemma|corollary|def|abbrev|opaque|instance)\s+"
        r"(?P<name>[^\s(:={]+)"
    )

    for line_number, line in enumerate(lines, 1):
        match = namespace_re.match(line)
        if match:
            label = match.group(1)
            parts = tuple(part for part in label.split(".") if part)
            namespace.extend(parts)
            blocks.append(Block("namespace", label, parts))
            continue

        match = section_re.match(line)
        if match:
            blocks.append(Block("section", match.group(1)))
            continue

        match = end_re.match(line)
        if match:
            explicit = match.group(1)
            if not blocks:
                continue
            if explicit is None:
                block = blocks.pop()
                if block.kind == "namespace" and block.namespace_parts:
                    del namespace[-len(block.namespace_parts):]
                continue
            # Close the most recent explicitly named block, including any
            # anonymous sections nested inside it.
            found = None
            for index in range(len(blocks) - 1, -1, -1):
                block = blocks[index]
                if block.name == explicit or (
                    block.kind == "namespace"
                    and block.namespace_parts
                    and block.namespace_parts[-1] == explicit
                ):
                    found = index
                    break
            if found is None:
                # Lean permits some end labels that are not section names.  Do
                # not guess by popping a namespace in that case.
                continue
            closing = blocks[found:]
            del blocks[found:]
            for block in reversed(closing):
                if block.kind == "namespace" and block.namespace_parts:
                    del namespace[-len(block.namespace_parts):]
            continue

        match = declaration_re.match(line)
        if not match:
            continue
        modifiers = set(match.group("mods").split())
        if "private" in modifiers or "local" in modifiers:
            continue
        name = match.group("name")
        if name == "_" or name.startswith("[") or name.startswith("("):
            continue
        # Named instances and declarations use Lean identifiers.  Anonymous
        # instances begin with a type expression and are intentionally skipped.
        if match.group("kind") == "instance" and any(symbol in name for symbol in ("→", "[", "]")):
            continue
        full_name = ".".join([*namespace, name]) if namespace else name
        if full_name not in names:
            names.append(full_name)

    if len(names) < 10:
        raise RuntimeError(f"suspiciously few Spt5 public declarations: {len(names)}")

    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_text(
        "import PrimalitySheafVerification.Spt5\n\n"
        + "\n".join(f"#print axioms {name}" for name in names)
        + "\n",
        encoding="utf-8",
    )
    MANIFEST.parent.mkdir(parents=True, exist_ok=True)
    MANIFEST.write_text("\n".join(names) + "\n", encoding="utf-8")
    print(f"Spt5 public declarations scheduled for audit: {len(names)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
