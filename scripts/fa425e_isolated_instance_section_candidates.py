#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path

THEOREM = "actualEdgeAmbientParam_hasDerivAt"
TOP_RE = re.compile(r"^(?:/--|/-!|theorem\s|lemma\s|def\s|noncomputable\s+def\s|abbrev\s|instance\s|structure\s|namespace\s|section\s|end\b)")


def sha(text: str) -> str:
    return hashlib.sha256(text.encode()).hexdigest()


def locate(lines: list[str]) -> tuple[int, int, int]:
    starts = [i for i, s in enumerate(lines) if s.startswith(f"theorem {THEOREM}")]
    if len(starts) != 1:
        raise RuntimeError(f"expected one blocker theorem, found {len(starts)}")
    start = starts[0]
    by_line = next(i for i in range(start, min(len(lines), start + 100)) if ":= by" in lines[i])
    end = next(i for i in range(by_line + 1, len(lines)) if lines[i] and not lines[i][0].isspace() and TOP_RE.match(lines[i]))
    return start, by_line, end


def doc_start(lines: list[str], theorem_start: int) -> int:
    i = theorem_start - 1
    while i >= 0 and not lines[i].strip():
        i -= 1
    if i >= 0 and lines[i].strip().endswith("-/"):
        j = i
        while j >= 0 and not lines[j].lstrip().startswith(("/--", "/-!")):
            j -= 1
        if j >= 0:
            return j
    return theorem_start


def safe_pre_slots(lines: list[str], before: int) -> list[int]:
    # Only replace top-level blank or ordinary line-comment slots.  Never consume
    # declaration/proof lines or the theorem docstring.
    lower = max(0, before - 80)
    slots = []
    for i in range(lower, before):
        s = lines[i]
        if s.strip() == "" or (not s[0].isspace() and s.startswith("--")):
            slots.append(i)
    return slots


def compact_or_pad(lines: list[str], target: int) -> list[str] | None:
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
    ap.add_argument("--refs", required=False)
    ap.add_argument("--limit", type=int, default=14)
    args = ap.parse_args()

    original = Path(args.baseline).read_text(encoding="utf-8")
    lines = original.splitlines(keepends=True)
    total = len(lines)
    start, by_line, next_top = locate(lines)
    header = tuple(lines[start : by_line + 1])
    dstart = doc_start(lines, start)
    pre_slots = safe_pre_slots(lines, dstart)
    body = lines[by_line + 1 : next_top]
    post_slots = [i for i in range(by_line + 1, next_top) if lines[i].strip() == ""]
    if not post_slots:
        raise RuntimeError("no blank top-level slot after blocker theorem for section end")
    post_slot = post_slots[-1]

    local_idx = next((i for i, s in enumerate(body) if "AddCommGroup Complex" in s and ("letI" in s or "let " in s)), None)
    hcomp_indices = [i for i, s in enumerate(body) if "hcomp" in s]
    closing_idx = hcomp_indices[-1] if hcomp_indices else None

    section_variants = {
        "disable-custom": [
            "section actualEdgeCanonicalInstanceScope\n",
            "attribute [-instance] Complex.addCommGroup\n",
        ],
        "canonical-local": [
            "section actualEdgeCanonicalInstanceScope\n",
            "local instance : AddCommGroup Complex := Complex.instNormedAddCommGroup.toAddCommGroup\n",
        ],
        "disable-and-canonical": [
            "section actualEdgeCanonicalInstanceScope\n",
            "attribute [-instance] Complex.addCommGroup\n",
            "local instance : AddCommGroup Complex := Complex.instNormedAddCommGroup.toAddCommGroup\n",
        ],
        "disable-and-normed": [
            "section actualEdgeCanonicalInstanceScope\n",
            "attribute [-instance] Complex.addCommGroup\n",
            "attribute [local instance] Complex.instNormedAddCommGroup\n",
        ],
        "canonical-priority": [
            "section actualEdgeCanonicalInstanceScope\n",
            "local instance (priority := 2000) : AddCommGroup Complex := Complex.instNormedAddCommGroup.toAddCommGroup\n",
        ],
    }
    closing_variants = {
        "keep-closing": None,
        "rebundle": "  exact hcomp.hasFDerivAt.hasDerivAt\n",
        "unfold-custom": "  simpa only [actualEdgeAmbientParam, actualEdgeNativeVelocity, Complex.addCommGroup] using hcomp\n",
        "unfold-both": "  simpa only [actualEdgeAmbientParam, actualEdgeNativeVelocity, Complex.addCommGroup, Complex.instNormedAddCommGroup] using hcomp\n",
        "convert-rfl": "  convert hcomp using 1 <;> rfl\n",
    }
    local_modes = {
        "remove-proof-local": "  -- canonical Complex additive structure is fixed by the surrounding section\n",
        "canonical-proof-local": "  letI : AddCommGroup Complex := Complex.instNormedAddCommGroup.toAddCommGroup\n",
    }

    candidates = []
    seen = set()

    def add(name: str, out: list[str], provenance: str) -> None:
        if len(out) != total:
            return
        try:
            s0, b0, _ = locate(out)
        except Exception:
            return
        if s0 != start or b0 != by_line or tuple(out[s0 : b0 + 1]) != header:
            return
        text = "".join(out)
        digest = sha(text)
        if digest == sha(original) or digest in seen:
            return
        seen.add(digest)
        candidates.append({"name": name, "provenance": provenance, "sha256": digest, "text": text})

    for sname, commands in section_variants.items():
        if len(pre_slots) < len(commands):
            continue
        selected_slots = pre_slots[-len(commands):]
        for lname, local_line in local_modes.items():
            for cname, closing in closing_variants.items():
                out = list(lines)
                for slot, command in zip(selected_slots, commands):
                    out[slot] = command
                out[post_slot] = "end actualEdgeCanonicalInstanceScope\n"
                new_body = list(body)
                if local_idx is not None:
                    new_body[local_idx] = local_line
                if closing is not None and closing_idx is not None:
                    # Replace only the final hcomp-bearing line.  One-line variants
                    # preserve the theorem proof height exactly.
                    new_body[closing_idx] = closing
                out[by_line + 1 : next_top] = new_body
                add(f"{sname}-{lname}-{cname}", out, f"hand:{sname}+{lname}+{cname}")

    out_dir = Path(args.output)
    out_dir.mkdir(parents=True, exist_ok=True)
    manifest = []
    for idx, item in enumerate(candidates[: args.limit]):
        fn = f"{idx:02d}-{item['name']}.lean"
        (out_dir / fn).write_text(item.pop("text"), encoding="utf-8")
        manifest.append({**item, "file": fn})
    data = {
        "theorem": THEOREM,
        "baseline_sha256": sha(original),
        "baseline_line_count": total,
        "theorem_start_line": start + 1,
        "theorem_header_sha256": sha("".join(header)),
        "docstring_start_line": dstart + 1,
        "pre_slots": [i + 1 for i in pre_slots[-6:]],
        "section_end_slot": post_slot + 1,
        "candidate_count": len(manifest),
        "candidates": manifest,
    }
    (out_dir / "MANIFEST.json").write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(data, indent=2))


if __name__ == "__main__":
    main()
