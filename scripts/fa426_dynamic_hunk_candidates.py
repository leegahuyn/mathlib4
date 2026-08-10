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
TOP_DECL = re.compile(r"^(?:theorem|lemma|def|noncomputable\s+def|abbrev|noncomputable\s+abbrev|instance|structure|class)\s+([^\s(:]+)")
ANY_TOP = re.compile(r"^(?:/--|/-!|theorem\s|lemma\s|def\s|noncomputable\s+def\s|abbrev\s|noncomputable\s+abbrev\s|instance\s|structure\s|class\s|namespace\s|section\s|end\b)")


def sha(text: str) -> str:
    return hashlib.sha256(text.encode()).hexdigest()


def source_from_ref(ref: str) -> str | None:
    p = subprocess.run(["git", "show", f"{ref}:{SOURCE_PATH}"], stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
    return p.stdout.decode("utf-8", errors="replace") if p.returncode == 0 and p.stdout else None


def decl_at(lines: list[str], line: int) -> tuple[str, int, int]:
    start = None; name = ""
    for i, text in enumerate(lines):
        m = TOP_DECL.match(text)
        if m and i + 1 <= line:
            start = i; name = m.group(1)
        if i + 1 > line:
            break
    if start is None:
        raise RuntimeError(f"no declaration at line {line}")
    end = next((i for i in range(start + 1, len(lines)) if lines[i] and not lines[i][0].isspace() and ANY_TOP.match(lines[i])), len(lines))
    return name, start, end


def by_line(lines: list[str], start: int, end: int) -> int | None:
    return next((i for i in range(start, min(end, start + 120)) if ":= by" in lines[i]), None)


def pad_or_compact(lines: list[str], target: int) -> list[str] | None:
    if len(lines) <= target:
        return lines + ["\n"] * (target - len(lines))
    remove = len(lines) - target
    removable = [i for i, s in enumerate(lines) if not s.strip() or s.lstrip().startswith("--")]
    if len(removable) < remove:
        return None
    gone = set(removable[-remove:])
    out = [s for i, s in enumerate(lines) if i not in gone]
    return out if len(out) == target else None


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--baseline", required=True)
    ap.add_argument("--output", required=True)
    ap.add_argument("--refs", required=True)
    ap.add_argument("--first-error-line", type=int, required=True)
    ap.add_argument("--limit", type=int, default=12)
    args = ap.parse_args()

    baseline_text = Path(args.baseline).read_text(encoding="utf-8")
    baseline_lines = baseline_text.splitlines(keepends=True)
    baseline_count = len(baseline_lines)
    decl_name, decl_start, decl_end = decl_at(baseline_lines, args.first_error_line)
    decl_by = by_line(baseline_lines, decl_start, decl_end)
    baseline_header = tuple(baseline_lines[decl_start : (decl_by + 1 if decl_by is not None else decl_start + 1)])

    refs = [r.strip() for r in Path(args.refs).read_text().splitlines() if r.strip()]
    candidates: dict[str, dict[str, Any]] = {}

    def add(name: str, lines: list[str], provenance: str, kind: str) -> None:
        if len(lines) != baseline_count:
            return
        try:
            out_name, out_start, out_end = decl_at(lines, args.first_error_line)
        except Exception:
            return
        if out_name != decl_name or out_start != decl_start:
            return
        out_by = by_line(lines, out_start, out_end)
        if decl_by is not None:
            if out_by != decl_by or tuple(lines[out_start : out_by + 1]) != baseline_header:
                return
        text = "".join(lines)
        d = sha(text)
        if d == sha(baseline_text) or d in candidates:
            return
        candidates[d] = {
            "name": name,
            "provenance": provenance,
            "kind": kind,
            "sha256": d,
            "text": text,
        }

    # Declaration-body transplants preserve the exact current statement/header.
    if decl_by is not None:
        target_body_len = decl_end - (decl_by + 1)
        for ref in refs:
            donor_text = source_from_ref(ref)
            if donor_text is None:
                continue
            donor_lines = donor_text.splitlines(keepends=True)
            donor_starts = [i for i, s in enumerate(donor_lines) if TOP_DECL.match(s) and TOP_DECL.match(s).group(1) == decl_name]
            if len(donor_starts) != 1:
                continue
            ds = donor_starts[0]
            de = next((i for i in range(ds + 1, len(donor_lines)) if donor_lines[i] and not donor_lines[i][0].isspace() and ANY_TOP.match(donor_lines[i])), len(donor_lines))
            db = by_line(donor_lines, ds, de)
            if db is None:
                continue
            donor_body = pad_or_compact(donor_lines[db + 1 : de], target_body_len)
            if donor_body is None:
                continue
            out = baseline_lines[: decl_by + 1] + donor_body + baseline_lines[decl_end:]
            safe = re.sub(r"[^A-Za-z0-9_.-]+", "-", ref)[-80:]
            add(f"decl-body-{safe}", out, ref, "declaration-body-transplant")

    # Equal-height local diff hunks around the actual frontier.
    window_lo = max(0, args.first_error_line - 1 - 80)
    window_hi = min(len(baseline_lines), args.first_error_line - 1 + 500)
    for ref in refs:
        donor_text = source_from_ref(ref)
        if donor_text is None:
            continue
        donor_lines = donor_text.splitlines(keepends=True)
        if len(donor_lines) != baseline_count:
            continue
        matcher = difflib.SequenceMatcher(a=baseline_lines, b=donor_lines, autojunk=False)
        local_hunks: list[tuple[int, int, int, int]] = []
        for tag, i1, i2, j1, j2 in matcher.get_opcodes():
            if tag == "equal" or i2 <= window_lo or i1 >= window_hi:
                continue
            if (i2 - i1) != (j2 - j1):
                continue
            local_hunks.append((i1, i2, j1, j2))
        safe = re.sub(r"[^A-Za-z0-9_.-]+", "-", ref)[-80:]
        for n, (i1, i2, j1, j2) in enumerate(local_hunks[:4]):
            out = list(baseline_lines)
            out[i1:i2] = donor_lines[j1:j2]
            add(f"hunk-{safe}-{n}", out, ref, "single-equal-height-hunk")
        if local_hunks:
            out = list(baseline_lines)
            for i1, i2, j1, j2 in reversed(local_hunks[:6]):
                out[i1:i2] = donor_lines[j1:j2]
            add(f"hunks-combined-{safe}", out, ref, "combined-equal-height-hunks")

    # Narrow syntax/API normalizations at the current declaration, with no line movement.
    block = "".join(baseline_lines[decl_start:decl_end])
    one_line_rules = [
        ("Complex.addCommGroup] using hcomp", "Complex.addCommGroup, Complex.instNormedAddCommGroup] using hcomp", "unfold-both-instances"),
        ("abs_add _ _", "abs_add_le _ _", "abs-add-rename"),
        ("hcompact.norm.mul hcompact.norm", "hcompact.norm.comp_left (g := fun x : ℝ => x ^ 2) (by norm_num)", "compact-support-square"),
        ("hcompact.deriv.norm.mul hcompact.deriv.norm", "hcompact.deriv.norm.comp_left (g := fun x : ℝ => x ^ 2) (by norm_num)", "compact-support-deriv-square"),
    ]
    for old, new, name in one_line_rules:
        if block.count(old) == 1:
            out = list(baseline_lines)
            changed = block.replace(old, new)
            changed_lines = changed.splitlines(keepends=True)
            fixed = pad_or_compact(changed_lines, decl_end - decl_start)
            if fixed is not None:
                out[decl_start:decl_end] = fixed
                add(f"local-{name}", out, f"local rule:{name}", "local-normalization")

    out_dir = Path(args.output)
    out_dir.mkdir(parents=True, exist_ok=True)
    manifest = []
    ordered = list(candidates.values())[: args.limit]
    for i, item in enumerate(ordered):
        fn = f"{i:02d}-{item['name']}.lean"
        (out_dir / fn).write_text(item.pop("text"), encoding="utf-8")
        manifest.append({**item, "file": fn})
    data = {
        "baseline_sha256": sha(baseline_text),
        "baseline_line_count": baseline_count,
        "first_error_line": args.first_error_line,
        "declaration": decl_name,
        "declaration_start_line": decl_start + 1,
        "declaration_end_line": decl_end,
        "declaration_header_sha256": sha("".join(baseline_header)),
        "window": [window_lo + 1, window_hi],
        "candidate_count": len(manifest),
        "candidates": manifest,
    }
    (out_dir / "MANIFEST.json").write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(data, indent=2))


if __name__ == "__main__":
    main()
