#!/usr/bin/env python3
from __future__ import annotations

import argparse
import difflib
import hashlib
import json
import re
import subprocess
from pathlib import Path
from typing import Any

SOURCE_PATH = "PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean"
DECL_RE = re.compile(r"^(?:theorem|lemma|def|noncomputable\s+def|abbrev|noncomputable\s+abbrev|instance|structure|class)\s+([^\s(:]+)")
TOP_RE = re.compile(r"^(?:/--|/-!|theorem\s|lemma\s|def\s|noncomputable\s+def\s|abbrev\s|noncomputable\s+abbrev\s|instance\s|structure\s|class\s|namespace\s|section\s|end\b)")
FORBIDDEN = {
    "sorry": re.compile(r"\bsorry\b"),
    "admit": re.compile(r"\badmit\b"),
    "global_axiom": re.compile(r"(?m)^\s*axiom\s+"),
    "unsafe": re.compile(r"(?m)^\s*(?:private\s+|protected\s+)?unsafe\b"),
    "native_decide": re.compile(r"\bnative_decide\b"),
    "Lean.ofReduceBool": re.compile(r"\bLean\.ofReduceBool\b"),
}


def sha(text: str) -> str:
    return hashlib.sha256(text.encode()).hexdigest()


def git_text(ref: str, path: str) -> str | None:
    proc = subprocess.run(
        ["git", "show", f"{ref}:{path}"],
        stdout=subprocess.PIPE,
        stderr=subprocess.DEVNULL,
        check=False,
    )
    return proc.stdout.decode("utf-8", errors="replace") if proc.returncode == 0 else None


def list_paths(ref: str) -> list[str]:
    proc = subprocess.run(
        ["git", "ls-tree", "-r", "--name-only", ref],
        stdout=subprocess.PIPE,
        stderr=subprocess.DEVNULL,
        text=True,
        check=False,
    )
    return [line.strip() for line in proc.stdout.splitlines() if line.strip()]


def declarations(lines: list[str]) -> list[dict[str, int | str]]:
    starts: list[tuple[int, str]] = []
    for index, line in enumerate(lines):
        match = DECL_RE.match(line)
        if match:
            starts.append((index, match.group(1)))
    result: list[dict[str, int | str]] = []
    for position, (start, name) in enumerate(starts):
        end = starts[position + 1][0] if position + 1 < len(starts) else len(lines)
        by_line = next((i for i in range(start, min(end, start + 160)) if ":= by" in lines[i]), None)
        header_end = by_line if by_line is not None else start
        result.append({"name": name, "start": start, "header_end": header_end, "end": end})
    return result


def declaration_at(decls: list[dict[str, int | str]], line_number: int) -> dict[str, int | str]:
    index = max(0, line_number - 1)
    eligible = [decl for decl in decls if int(decl["start"]) <= index < int(decl["end"])]
    if not eligible:
        raise RuntimeError(f"no declaration contains line {line_number}")
    return eligible[-1]


def intersects_header(i1: int, i2: int, decls: list[dict[str, int | str]]) -> bool:
    for decl in decls:
        start = int(decl["start"])
        end = int(decl["header_end"]) + 1
        if i1 < end and i2 > start:
            return True
    return False


def strip_comments_and_strings(text: str) -> str:
    output: list[str] = []
    index = 0
    block_depth = 0
    in_string = False
    while index < len(text):
        if block_depth:
            if text.startswith("/-", index):
                block_depth += 1; output.extend("  "); index += 2
            elif text.startswith("-/", index):
                block_depth -= 1; output.extend("  "); index += 2
            else:
                output.append("\n" if text[index] == "\n" else " "); index += 1
        elif in_string:
            if text[index] == "\\" and index + 1 < len(text):
                output.extend("  "); index += 2
            elif text[index] == '"':
                in_string = False; output.append(" "); index += 1
            else:
                output.append("\n" if text[index] == "\n" else " "); index += 1
        elif text.startswith("--", index):
            while index < len(text) and text[index] != "\n":
                output.append(" "); index += 1
        elif text.startswith("/-", index):
            block_depth = 1; output.extend("  "); index += 2
        elif text[index] == '"':
            in_string = True; output.append(" "); index += 1
        else:
            output.append(text[index]); index += 1
    return "".join(output)


def trust_clean(text: str) -> bool:
    cleaned = strip_comments_and_strings(text)
    return all(not pattern.search(cleaned) for pattern in FORBIDDEN.values())


def compact_or_pad(lines: list[str], target: int) -> list[str] | None:
    if len(lines) <= target:
        return lines + ["\n"] * (target - len(lines))
    remove = len(lines) - target
    removable = [i for i, line in enumerate(lines) if not line.strip() or line.lstrip().startswith("--")]
    if len(removable) < remove:
        return None
    removed = set(removable[-remove:])
    result = [line for i, line in enumerate(lines) if i not in removed]
    return result if len(result) == target else None


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--baseline", required=True)
    parser.add_argument("--output", required=True)
    parser.add_argument("--refs", required=True)
    parser.add_argument("--first-error-line", type=int, required=True)
    parser.add_argument("--limit", type=int, default=24)
    args = parser.parse_args()

    baseline_text = Path(args.baseline).read_text(encoding="utf-8")
    baseline_lines = baseline_text.splitlines(keepends=True)
    baseline_count = len(baseline_lines)
    baseline_decls = declarations(baseline_lines)
    current_decl = declaration_at(baseline_decls, args.first_error_line)
    current_name = str(current_decl["name"])
    current_start = int(current_decl["start"])
    current_header_end = int(current_decl["header_end"])
    current_end = int(current_decl["end"])
    current_header = tuple(baseline_lines[current_start : current_header_end + 1])

    refs = [line.strip() for line in Path(args.refs).read_text(encoding="utf-8").splitlines() if line.strip()]
    donor_sources: list[dict[str, Any]] = []
    seen_donor_sha: set[str] = set()
    for ref in refs:
        for path in list_paths(ref):
            filename = Path(path).name
            is_main = path == SOURCE_PATH
            is_evidence = (
                filename.endswith(".lean")
                and "Mock2_FunctionalAnalysis" in filename
                and ("candidate" in filename.lower() or "frontier" in filename.lower() or "source" in filename.lower())
            )
            if not is_main and not is_evidence:
                continue
            text = git_text(ref, path)
            if text is None:
                continue
            digest = sha(text)
            if digest in seen_donor_sha or digest == sha(baseline_text):
                continue
            lines = text.splitlines(keepends=True)
            if len(lines) != baseline_count or not trust_clean(text):
                continue
            seen_donor_sha.add(digest)
            donor_sources.append({"ref": ref, "path": path, "sha256": digest, "text": text, "lines": lines})

    candidates: dict[str, dict[str, Any]] = {}

    def add(name: str, lines: list[str], provenance: str, kind: str) -> None:
        if len(lines) != baseline_count:
            return
        text = "".join(lines)
        if not trust_clean(text):
            return
        output_decls = declarations(lines)
        try:
            output_decl = declaration_at(output_decls, args.first_error_line)
        except Exception:
            return
        if str(output_decl["name"]) != current_name or int(output_decl["start"]) != current_start:
            return
        output_header_end = int(output_decl["header_end"])
        if output_header_end != current_header_end:
            return
        if tuple(lines[current_start : current_header_end + 1]) != current_header:
            return
        digest = sha(text)
        if digest == sha(baseline_text) or digest in candidates:
            return
        candidates[digest] = {
            "name": name,
            "provenance": provenance,
            "kind": kind,
            "sha256": digest,
            "text": text,
        }

    window_lo = max(0, args.first_error_line - 1 - 120)
    window_hi = min(baseline_count, args.first_error_line - 1 + 3500)
    for donor_index, donor in enumerate(donor_sources):
        donor_lines = donor["lines"]
        donor_decls = declarations(donor_lines)
        provenance = f"{donor['ref']}:{donor['path']}:{donor['sha256']}"

        donor_current = [decl for decl in donor_decls if str(decl["name"]) == current_name]
        if len(donor_current) == 1:
            donor_decl = donor_current[0]
            donor_header_end = int(donor_decl["header_end"])
            donor_end = int(donor_decl["end"])
            donor_body = donor_lines[donor_header_end + 1 : donor_end]
            target_body_length = current_end - (current_header_end + 1)
            fixed_body = compact_or_pad(donor_body, target_body_length)
            if fixed_body is not None:
                output = baseline_lines[: current_header_end + 1] + fixed_body + baseline_lines[current_end:]
                add(
                    f"decl-body-{donor_index:03d}",
                    output,
                    provenance,
                    "evidence-declaration-body-transplant",
                )

        matcher = difflib.SequenceMatcher(a=baseline_lines, b=donor_lines, autojunk=False)
        safe_hunks: list[tuple[int, int, int, int]] = []
        for tag, i1, i2, j1, j2 in matcher.get_opcodes():
            if tag == "equal" or i2 <= window_lo or i1 >= window_hi:
                continue
            if (i2 - i1) != (j2 - j1):
                continue
            if intersects_header(i1, i2, baseline_decls) or intersects_header(j1, j2, donor_decls):
                continue
            safe_hunks.append((i1, i2, j1, j2))

        for hunk_index, (i1, i2, j1, j2) in enumerate(safe_hunks[:8]):
            output = list(baseline_lines)
            output[i1:i2] = donor_lines[j1:j2]
            add(
                f"evidence-hunk-{donor_index:03d}-{hunk_index:02d}",
                output,
                provenance,
                "single-equal-height-proof-hunk",
            )

        if safe_hunks:
            output = list(baseline_lines)
            for i1, i2, j1, j2 in reversed(safe_hunks[:20]):
                output[i1:i2] = donor_lines[j1:j2]
            add(
                f"evidence-hunks-combined-{donor_index:03d}",
                output,
                provenance,
                "combined-nonheader-equal-height-proof-hunks",
            )

    output_dir = Path(args.output)
    output_dir.mkdir(parents=True, exist_ok=True)
    ordered = list(candidates.values())[: args.limit]
    manifest_candidates = []
    for index, item in enumerate(ordered):
        filename = f"{index:03d}-{item['name']}.lean"
        (output_dir / filename).write_text(item.pop("text"), encoding="utf-8")
        manifest_candidates.append({**item, "file": filename})

    manifest = {
        "authority": "candidate generation only; direct Lean CLI remains promotion authority",
        "baseline_sha256": sha(baseline_text),
        "baseline_line_count": baseline_count,
        "first_error_line": args.first_error_line,
        "declaration": current_name,
        "declaration_start_line": current_start + 1,
        "declaration_header_sha256": sha("".join(current_header)),
        "window": [window_lo + 1, window_hi],
        "donor_source_count": len(donor_sources),
        "candidate_count": len(manifest_candidates),
        "candidates": manifest_candidates,
    }
    (output_dir / "MANIFEST.json").write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(manifest, indent=2))


if __name__ == "__main__":
    main()
