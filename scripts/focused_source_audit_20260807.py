#!/usr/bin/env python3
"""Static trust and theorem-interface auditing for the focused Lean modules.

The scanner removes nested comments and strings before checking executable code.
The signature digest records theorem/lemma declarations only up to their proof
assignment, so proof repairs may change while public statements may not.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path

FORBIDDEN = {
    "sorry": r"\bsorry\b",
    "admit": r"\badmit\b",
    "global_axiom": r"(?m)^\s*axiom\b",
    "unsafe": r"\bunsafe\b",
    "native_decide": r"\bnative_decide\b",
    "Lean.ofReduceBool": r"\bLean\.ofReduceBool\b",
    "by_contra!": r"\bby_contra!\b",
}

DECL_START = re.compile(
    r"(?m)^\s*(?:(?:private|protected|nonrec)\s+)*(?:theorem|lemma)\s+([^\s:(]+)"
)
NEXT_DECL = re.compile(
    r"(?m)^\s*(?:(?:private|protected|nonrec)\s+)*"
    r"(?:theorem|lemma|def|abbrev|opaque|structure|class|instance|inductive)\s+"
)
PROOF_START = re.compile(r"(?m)\s+:=\s*by\b|(?m)\s+:=|(?m)^\s*where\s*$")


def strip_comments_and_strings(src: str) -> str:
    out: list[str] = []
    i = 0
    depth = 0
    in_string = False
    escaped = False
    while i < len(src):
        if depth:
            if src.startswith("/-", i):
                depth += 1
                out.extend("  ")
                i += 2
            elif src.startswith("-/", i):
                depth -= 1
                out.extend("  ")
                i += 2
            else:
                out.append("\n" if src[i] == "\n" else " ")
                i += 1
            continue
        if in_string:
            ch = src[i]
            out.append("\n" if ch == "\n" else " ")
            if escaped:
                escaped = False
            elif ch == "\\":
                escaped = True
            elif ch == '"':
                in_string = False
            i += 1
            continue
        if src.startswith("/-", i):
            depth = 1
            out.extend("  ")
            i += 2
        elif src.startswith("--", i):
            while i < len(src) and src[i] != "\n":
                out.append(" ")
                i += 1
        elif src[i] == '"':
            in_string = True
            out.append(" ")
            i += 1
        else:
            out.append(src[i])
            i += 1
    if depth or in_string:
        raise ValueError("unterminated nested comment or string")
    return "".join(out)


def declaration_signatures(code: str) -> list[str]:
    matches = list(DECL_START.finditer(code))
    signatures: list[str] = []
    for idx, match in enumerate(matches):
        start = match.start()
        end = len(code)
        if idx + 1 < len(matches):
            end = matches[idx + 1].start()
        next_other = NEXT_DECL.search(code, match.end(), end)
        if next_other:
            end = next_other.start()
        block = code[start:end]
        proof = PROOF_START.search(block)
        if proof:
            block = block[: proof.start()]
        signatures.append(" ".join(block.split()))
    return signatures


def inspect(path: Path) -> dict[str, object]:
    source = path.read_text(encoding="utf-8")
    code = strip_comments_and_strings(source)
    counts = {name: len(re.findall(pattern, code)) for name, pattern in FORBIDDEN.items()}
    signatures = declaration_signatures(code)
    return {
        "path": str(path),
        "source_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
        "source_lines": source.count("\n") + (0 if source.endswith("\n") else 1),
        "forbidden": counts,
        "theorem_lemma_count": len(signatures),
        "theorem_signature_sha256": hashlib.sha256(
            "\n".join(signatures).encode("utf-8")
        ).hexdigest(),
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    sub = parser.add_subparsers(dest="command", required=True)

    audit_parser = sub.add_parser("audit")
    audit_parser.add_argument("files", nargs="+")

    sig_parser = sub.add_parser("signature")
    sig_parser.add_argument("file")

    compare_parser = sub.add_parser("compare")
    compare_parser.add_argument("baseline")
    compare_parser.add_argument("candidate")

    args = parser.parse_args()

    if args.command == "audit":
        reports = [inspect(Path(raw)) for raw in args.files]
        print(json.dumps(reports, indent=2, ensure_ascii=False))
        if any(any(report["forbidden"].values()) for report in reports):
            return 1
        return 0

    if args.command == "signature":
        report = inspect(Path(args.file))
        print(report["theorem_signature_sha256"])
        return 0

    baseline = inspect(Path(args.baseline))
    candidate = inspect(Path(args.candidate))
    result = {
        "baseline": baseline,
        "candidate": candidate,
        "statements_equal": (
            baseline["theorem_signature_sha256"]
            == candidate["theorem_signature_sha256"]
        ),
    }
    print(json.dumps(result, indent=2, ensure_ascii=False))
    return 0 if result["statements_equal"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
