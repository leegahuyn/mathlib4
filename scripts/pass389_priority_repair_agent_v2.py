from __future__ import annotations

import hashlib
import importlib.util
from pathlib import Path
import re

BASE = Path(__file__).with_name("pass389_priority_repair_agent.py")
spec = importlib.util.spec_from_file_location("pass389_priority_base", BASE)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load {BASE}")
agent = importlib.util.module_from_spec(spec)
spec.loader.exec_module(agent)


def stable_header_fingerprint(text: str) -> dict[str, str]:
    """Freeze public proof declarations without using mutable line numbers as keys."""
    lines = text.splitlines()
    starts = [i for i, line in enumerate(lines) if agent.PUBLIC_PROOF_DECL.match(line)]
    result: dict[str, str] = {}
    occurrences: dict[str, int] = {}
    for index, start in enumerate(starts):
        end = starts[index + 1] if index + 1 < len(starts) else len(lines)
        chunk = lines[start:end]
        header_lines: list[str] = []
        found = False
        for line in chunk[:160]:
            if ":=" in line:
                header_lines.append(line.split(":=", 1)[0].rstrip() + " :=")
                found = True
                break
            header_lines.append(line.rstrip())
            if re.search(r"\bwhere\s*$", line):
                found = True
                break
        if not found and len(header_lines) > 60:
            header_lines = header_lines[:60]
        first = lines[start]
        match = re.match(
            r"^(?:noncomputable\s+)?(?:theorem|lemma|corollary)\s+([^\s:{(]+)",
            first,
        )
        name = match.group(1) if match else "anonymous"
        occurrence = occurrences.get(name, 0)
        occurrences[name] = occurrence + 1
        normalized = "\n".join(part.strip() for part in header_lines if part.strip())
        result[f"{name}#{occurrence}"] = hashlib.sha256(normalized.encode()).hexdigest()
    return result


agent.header_fingerprint = stable_header_fingerprint
raise SystemExit(agent.main())
