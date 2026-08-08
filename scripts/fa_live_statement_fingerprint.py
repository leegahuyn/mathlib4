from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path

DECL = re.compile(
    r"^(?P<indent>\s*)(?:(?P<mods>(?:(?:private|protected|noncomputable|local)\s+)*))"
    r"(?P<kind>theorem|lemma|corollary)\s+(?P<name>[^\s(:{]+)"
)


def strip_line_comment(line: str) -> str:
    return line.split("--", 1)[0]


def declarations(text: str) -> list[dict[str, str]]:
    lines = text.splitlines()
    starts = [i for i, line in enumerate(lines) if DECL.match(line)]
    result: list[dict[str, str]] = []
    for pos, start in enumerate(starts):
        match = DECL.match(lines[start])
        assert match is not None
        if "private" in (match.group("mods") or "").split():
            continue
        end = starts[pos + 1] if pos + 1 < len(starts) else len(lines)
        header_lines: list[str] = []
        found = False
        for i in range(start, end):
            line = lines[i]
            if ":= by" in line:
                header_lines.append(line.split(":= by", 1)[0].rstrip() + ":=")
                found = True
                break
            if re.search(r"\bwhere\s*$", strip_line_comment(line)):
                header_lines.append(line.rstrip())
                found = True
                break
            header_lines.append(line.rstrip())
        if not found:
            # Declarations without an explicit tactic proof are still fingerprinted up to the next declaration.
            header_lines = [line.rstrip() for line in lines[start:end]]
        normalized = "\n".join(header_lines).strip()
        result.append(
            {
                "kind": match.group("kind"),
                "name": match.group("name"),
                "header": normalized,
                "sha256": hashlib.sha256(normalized.encode("utf-8")).hexdigest(),
            }
        )
    return result


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("file", type=Path)
    parser.add_argument("--write", type=Path)
    parser.add_argument("--compare", type=Path)
    args = parser.parse_args()
    current = declarations(args.file.read_text(encoding="utf-8"))
    payload = {"file": str(args.file), "declarations": current}
    if args.write:
        args.write.parent.mkdir(parents=True, exist_ok=True)
        args.write.write_text(json.dumps(payload, indent=2, ensure_ascii=False), encoding="utf-8")
    if args.compare:
        expected = json.loads(args.compare.read_text(encoding="utf-8"))["declarations"]
        if current != expected:
            before = {entry["name"]: entry for entry in expected}
            after = {entry["name"]: entry for entry in current}
            missing = sorted(set(before) - set(after))
            added = sorted(set(after) - set(before))
            changed = sorted(
                name for name in set(before) & set(after)
                if before[name]["sha256"] != after[name]["sha256"]
            )
            print(json.dumps({"missing": missing, "added": added, "changed": changed}, indent=2))
            return 1
    print(json.dumps(payload, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
