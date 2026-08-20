#!/usr/bin/env python3
"""Prepare source-only, header-preserving replacements for forbidden native_decide.

This draft is intentionally independent of a repository checkout.  It reads the
two authoritative source blobs recovered from artifact 8966752488, verifies
their SHA-256 identities, and can either report the replacement manifest or
materialize candidate copies in an explicitly supplied output directory.

It never invokes Lean, Lake, Git, or GitHub.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from dataclasses import asdict, dataclass
from pathlib import Path


EXPECTED = {
    "Spt1.lean": {
        "sha256": "0ef9289806dcb5b57d1d801526e45fe71bd2c85768b5b6f375fa9de005037e74",
        "standalone": 0,
        "fin_cases": 0,
        "inline": 1,
        "documentation": 1,
    },
    "Mock1_Advanced.lean": {
        "sha256": "69f0703cc03fd0efde38b9d7018424cc62b724e0afaab7b66e3ccafb4d9f0311",
        "standalone": 57,
        "fin_cases": 3,
        "inline": 0,
        "documentation": 0,
    },
}

DEFAULT_SOURCE_DIR = Path(
    "work/warnings-artifact-8966752488/build-logs/checked-in-sources"
)

STANDALONE_RE = re.compile(r"(?m)^(?P<indent>[ \t]*)native_decide[ \t]*$")
FIN_CASES_RE = re.compile(
    r"(?m)^(?P<prefix>[ \t]*fin_cases[ \t]+(?P<var>[A-Za-z_][A-Za-z0-9_]*)"
    r"[ \t]+<;>)[ \t]+native_decide[ \t]*$"
)
SPT1_INLINE_OLD = (
    "example : Fintype.card {x : ZMod 9 // (12 : ZMod 9) * x = 0} = 3 := "
    "by native_decide"
)
SPT1_DOCUMENTATION_OLD = (
    "without it the `native_decide` witnesses below failed to synthesize `Decidable`"
)
SPT1_DOCUMENTATION_NEW = (
    "without it the finite-decision witnesses below failed to synthesize `Decidable`"
)


@dataclass(frozen=True)
class ReplacementReport:
    file: str
    source_sha256: str
    candidate_sha256: str
    standalone: int
    fin_cases: int
    inline: int
    documentation: int
    total: int
    total_text_edits: int
    old_line_count: int
    new_line_count: int
    replacement: str
    forbidden_code_counts: dict[str, int]
    forbidden_raw_trust_counts: dict[str, int]


def sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def read_utf8(path: Path) -> str:
    # The artifact files are UTF-8 and use LF.  newline="" preserves identity.
    with path.open("r", encoding="utf-8", newline="") as handle:
        return handle.read()


def strip_lean_comments_and_strings(text: str) -> str:
    """Blank comments/strings while preserving newlines for token auditing.

    Lean block comments nest.  This scanner is deliberately conservative: all
    comment and string contents become spaces, so trust-token counts cannot be
    inflated by documentation or string literals.
    """

    out: list[str] = []
    i = 0
    block_depth = 0
    in_string = False
    escaped = False
    while i < len(text):
        ch = text[i]
        nxt = text[i + 1] if i + 1 < len(text) else ""
        if block_depth:
            if ch == "/" and nxt == "-":
                block_depth += 1
                out.extend("  ")
                i += 2
            elif ch == "-" and nxt == "/":
                block_depth -= 1
                out.extend("  ")
                i += 2
            else:
                out.append("\n" if ch == "\n" else " ")
                i += 1
            continue
        if in_string:
            if ch == "\n":
                out.append("\n")
            else:
                out.append(" ")
            if escaped:
                escaped = False
            elif ch == "\\":
                escaped = True
            elif ch == '"':
                in_string = False
            i += 1
            continue
        if ch == "/" and nxt == "-":
            block_depth = 1
            out.extend("  ")
            i += 2
        elif ch == "-" and nxt == "-":
            while i < len(text) and text[i] != "\n":
                out.append(" ")
                i += 1
        elif ch == '"':
            in_string = True
            out.append(" ")
            i += 1
        else:
            out.append(ch)
            i += 1
    if block_depth or in_string:
        raise ValueError("unterminated Lean block comment or string")
    return "".join(out)


def forbidden_counts(text: str) -> dict[str, int]:
    code = strip_lean_comments_and_strings(text)
    patterns = {
        "native_decide": r"\bnative_decide\b",
        "decide_plus_native": r"\bdecide\s+\+native\b",
        "Lean.ofReduceBool": r"\bLean\.ofReduceBool\b",
        "sorry": r"\bsorry\b",
        "admit": r"\badmit\b",
        "unsafe": r"\bunsafe\b",
    }
    return {name: len(re.findall(pattern, code)) for name, pattern in patterns.items()}


def forbidden_raw_trust_counts(text: str) -> dict[str, int]:
    """Count raw trust spellings, including comments, for an absolute-zero audit."""

    patterns = {
        "native_decide": r"\bnative_decide\b",
        "decide_plus_native": r"\bdecide\s+\+native\b",
        "Lean.ofReduceBool": r"\bLean\.ofReduceBool\b",
    }
    return {name: len(re.findall(pattern, text)) for name, pattern in patterns.items()}


def prepare_one(name: str, source: str, replacement: str) -> tuple[str, ReplacementReport]:
    expected = EXPECTED[name]
    actual_sha = sha256_text(source)
    if actual_sha != expected["sha256"]:
        raise ValueError(
            f"{name}: SHA-256 mismatch; expected {expected['sha256']}, got {actual_sha}"
        )

    standalone = len(STANDALONE_RE.findall(source))
    fin_cases = len(FIN_CASES_RE.findall(source))
    inline = source.count(SPT1_INLINE_OLD)
    documentation = source.count(SPT1_DOCUMENTATION_OLD)
    observed = {
        "standalone": standalone,
        "fin_cases": fin_cases,
        "inline": inline,
        "documentation": documentation,
    }
    wanted = {key: expected[key] for key in observed}
    if observed != wanted:
        raise ValueError(f"{name}: replacement shape mismatch: {observed} != {wanted}")

    candidate = FIN_CASES_RE.sub(
        lambda m: f"{m.group('prefix')} {replacement}", source
    )
    candidate = STANDALONE_RE.sub(
        lambda m: f"{m.group('indent')}{replacement}", candidate
    )
    if inline:
        candidate = candidate.replace(
            SPT1_INLINE_OLD, SPT1_INLINE_OLD.replace("native_decide", replacement)
        )
    if documentation:
        candidate = candidate.replace(
            SPT1_DOCUMENTATION_OLD, SPT1_DOCUMENTATION_NEW
        )

    total = standalone + fin_cases + inline
    if candidate == source or total == 0:
        raise ValueError(f"{name}: no candidate change was made")
    if candidate.count("\n") != source.count("\n"):
        raise ValueError(f"{name}: line count changed")

    counts = forbidden_counts(candidate)
    for token in ("native_decide", "decide_plus_native", "Lean.ofReduceBool"):
        if counts[token] != 0:
            raise ValueError(f"{name}: candidate still contains forbidden code token {token}")
    raw_trust_counts = forbidden_raw_trust_counts(candidate)
    if any(raw_trust_counts.values()):
        raise ValueError(
            f"{name}: candidate still contains a raw forbidden trust spelling: "
            f"{raw_trust_counts}"
        )

    report = ReplacementReport(
        file=name,
        source_sha256=actual_sha,
        candidate_sha256=sha256_text(candidate),
        standalone=standalone,
        fin_cases=fin_cases,
        inline=inline,
        documentation=documentation,
        total=total,
        total_text_edits=total + documentation,
        old_line_count=source.count("\n") + 1,
        new_line_count=candidate.count("\n") + 1,
        replacement=replacement,
        forbidden_code_counts=counts,
        forbidden_raw_trust_counts=raw_trust_counts,
    )
    return candidate, report


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source-dir", type=Path, default=DEFAULT_SOURCE_DIR)
    parser.add_argument("--output-dir", type=Path)
    parser.add_argument(
        "--variant",
        choices=("kernel", "elab"),
        default="kernel",
        help="kernel uses explicit `decide +kernel`; elab uses plain `decide`",
    )
    parser.add_argument(
        "--check-only",
        action="store_true",
        help="verify identities/counts and print JSON; do not write candidates",
    )
    args = parser.parse_args()
    if not args.check_only and args.output_dir is None:
        parser.error("--output-dir is required unless --check-only is used")

    replacement = "decide +kernel" if args.variant == "kernel" else "decide"
    candidates: dict[str, str] = {}
    reports: list[ReplacementReport] = []
    for name in EXPECTED:
        source = read_utf8(args.source_dir / name)
        candidate, report = prepare_one(name, source, replacement)
        candidates[name] = candidate
        reports.append(report)

    manifest = {
        "authority": "artifact 8966752488 checked-in source blobs",
        "variant": args.variant,
        "replacement": replacement,
        "lean_lake_git_github_invoked": False,
        "header_policy": (
            "proof-body token substitutions plus one documentation-only normalization; "
            "line count, declaration order, and every declaration header are preserved"
        ),
        "documentation_policy": (
            "one stale Spt1 comment spelling is normalized so raw trust-token counts are zero"
        ),
        "reports": [asdict(report) for report in reports],
        "total_replacements": sum(report.total for report in reports),
        "total_documentation_edits": sum(report.documentation for report in reports),
        "total_text_edits": sum(report.total_text_edits for report in reports),
    }
    if not args.check_only:
        assert args.output_dir is not None
        args.output_dir.mkdir(parents=True, exist_ok=False)
        for name, candidate in candidates.items():
            (args.output_dir / name).write_text(candidate, encoding="utf-8", newline="")
        (args.output_dir / "MANIFEST.json").write_text(
            json.dumps(manifest, ensure_ascii=False, indent=2) + "\n",
            encoding="utf-8",
            newline="",
        )
    print(json.dumps(manifest, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
