from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path

DECL = re.compile(
    r"^(?P<indent>\s*)(?P<mods>(?:(?:private|protected|noncomputable|local|scoped)\s+)*)"
    r"(?P<kind>theorem|lemma|corollary|def|abbrev|instance|structure|class)\b"
    r"(?P<rest>.*)$"
)


def clean(line: str) -> str:
    return line.split("--", 1)[0].rstrip()


def collect(text: str) -> list[dict[str, str | int]]:
    lines = text.splitlines()
    starts = [i for i, line in enumerate(lines) if DECL.match(line)]
    result: list[dict[str, str | int]] = []
    anonymous = 0
    for position, start in enumerate(starts):
        match = DECL.match(lines[start])
        assert match is not None
        mods = (match.group("mods") or "").split()
        if "private" in mods or "local" in mods:
            continue
        end = starts[position + 1] if position + 1 < len(starts) else len(lines)
        signature: list[str] = []
        found = False
        depth = 0
        for index in range(start, end):
            raw = clean(lines[index])
            signature.append(raw)
            code = raw
            depth += code.count("(") + code.count("[") + code.count("{")
            depth -= code.count(")") + code.count("]") + code.count("}")
            if ":= by" in code:
                signature[-1] = code.split(":= by", 1)[0].rstrip() + " :="
                found = True
                break
            if re.search(r"\bwhere\s*$", code) and depth <= 0:
                signature[-1] = re.sub(r"\bwhere\s*$", "where", code)
                found = True
                break
            # Definitions with a term body on the same line.
            if ":=" in code and depth <= 0:
                signature[-1] = code.split(":=", 1)[0].rstrip() + " :="
                found = True
                break
        if not found:
            # Keep the complete declaration when no explicit body delimiter was recognized.
            signature = [clean(line) for line in lines[start:end]]
        normalized = "\n".join(signature).strip()
        rest = match.group("rest").strip()
        name_match = re.match(r"(?:_root_\.)?([A-Za-z0-9_'.]+)", rest)
        if name_match:
            name = name_match.group(1)
        else:
            anonymous += 1
            name = f"<anonymous-{match.group('kind')}-{anonymous}>"
        result.append(
            {
                "kind": match.group("kind"),
                "name": name,
                "line": start + 1,
                "signature": normalized,
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
    current = collect(args.file.read_text(encoding="utf-8"))
    payload = {"file": str(args.file), "declarations": current}
    if args.write:
        args.write.parent.mkdir(parents=True, exist_ok=True)
        args.write.write_text(json.dumps(payload, indent=2, ensure_ascii=False), encoding="utf-8")
    if args.compare:
        expected = json.loads(args.compare.read_text(encoding="utf-8"))["declarations"]
        before = {(entry["kind"], entry["name"]): entry for entry in expected}
        after = {(entry["kind"], entry["name"]): entry for entry in current}
        missing = sorted(set(before) - set(after))
        added = sorted(set(after) - set(before))
        changed = sorted(
            key for key in set(before) & set(after)
            if before[key]["sha256"] != after[key]["sha256"]
        )
        if missing or added or changed:
            print(json.dumps({"missing": missing, "added": added, "changed": changed}, indent=2))
            return 1
    print(json.dumps({"count": len(current)}, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
