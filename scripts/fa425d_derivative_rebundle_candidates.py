#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path

THEOREM = "actualEdgeAmbientParam_hasDerivAt"
DECL_RE = re.compile(r"^(?:/--|/-!|theorem\s|lemma\s|def\s|noncomputable\s+def\s|abbrev\s|instance\s|structure\s|namespace\s|section\s|end\b)")


def sha(text: str) -> str:
    return hashlib.sha256(text.encode()).hexdigest()


def locate(lines: list[str]) -> tuple[int, int, int]:
    starts = [i for i, s in enumerate(lines) if s.startswith(f"theorem {THEOREM}")]
    if len(starts) != 1:
        raise RuntimeError(f"expected one blocker theorem, found {len(starts)}")
    start = starts[0]
    by_line = next(i for i in range(start, min(len(lines), start + 100)) if ":= by" in lines[i])
    end = next(i for i in range(by_line + 1, len(lines)) if lines[i] and not lines[i][0].isspace() and DECL_RE.match(lines[i]))
    return start, by_line, end


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
    count = len(lines)
    start, by_line, end = locate(lines)
    header = tuple(lines[start : by_line + 1])
    body = lines[by_line + 1 : end]

    hcomp_indices = [i for i, s in enumerate(body) if "hcomp" in s]
    if not hcomp_indices:
        raise RuntimeError("no hcomp use found in blocker theorem")
    closing_idx = hcomp_indices[-1]
    # Include preceding continuation lines from the current closing, but never the
    # have hcomp declaration itself.
    closing_start = closing_idx
    while closing_start > 0 and (
        body[closing_start - 1].lstrip().startswith(("simpa", "convert", "exact", "show", "change"))
        or body[closing_start - 1].rstrip().endswith(("using", "from"))
    ):
        closing_start -= 1
    closing_end = closing_idx + 1
    closing_height = closing_end - closing_start

    local_idx = next((i for i, s in enumerate(body) if "AddCommGroup Complex" in s and ("letI" in s or "let " in s)), None)
    blank_pre = [i for i in range(max(0, start - 30), start) if not lines[i].strip()]
    pre_slot = blank_pre[-1] if blank_pre else None

    candidates: list[dict[str, str]] = []
    seen: set[str] = set()

    def add(name: str, out_lines: list[str], provenance: str) -> None:
        if len(out_lines) != count:
            return
        s0, b0, _ = locate(out_lines)
        if s0 != start or b0 != by_line or tuple(out_lines[s0 : b0 + 1]) != header:
            return
        text = "".join(out_lines)
        digest = sha(text)
        if digest == sha(original) or digest in seen:
            return
        seen.add(digest)
        candidates.append({"name": name, "provenance": provenance, "sha256": digest, "text": text})

    closing_variants = {
        "rebundle-exact": ["  exact hcomp.hasFDerivAt.hasDerivAt\n"],
        "rebundle-simpa-defs": ["  simpa only [actualEdgeAmbientParam, actualEdgeNativeVelocity] using hcomp.hasFDerivAt.hasDerivAt\n"],
        "rebundle-simp-defs": ["  simpa [actualEdgeAmbientParam, actualEdgeNativeVelocity] using hcomp.hasFDerivAt.hasDerivAt\n"],
        "rebundle-convert-rfl": ["  convert hcomp.hasFDerivAt.hasDerivAt using 1 <;> rfl\n"],
        "rebundle-convert-simp": ["  convert hcomp.hasFDerivAt.hasDerivAt using 1 <;> simp [actualEdgeAmbientParam, actualEdgeNativeVelocity]\n"],
        "hasF-simpa": ["  simpa only [HasDerivAt, actualEdgeAmbientParam, actualEdgeNativeVelocity] using hcomp.hasFDerivAt\n"],
        "hasF-simp": ["  simpa [HasDerivAt, actualEdgeAmbientParam, actualEdgeNativeVelocity] using hcomp.hasFDerivAt\n"],
        "show-rebundle": ["  show HasDerivAt (actualEdgeAmbientParam e) (actualEdgeNativeVelocity e t) (t : Real)\n", "  exact hcomp.hasFDerivAt.hasDerivAt\n"],
    }
    local_modes = {
        "keep-local": None,
        "canonical-local": "  letI : AddCommGroup Complex := Complex.instNormedAddCommGroup.toAddCommGroup\n",
        "remove-local": "  -- use the canonical inferred Complex additive structure\n",
    }
    pre_modes = {
        "no-preheader": None,
        "preheader-canonical": "local instance : AddCommGroup Complex := Complex.instNormedAddCommGroup.toAddCommGroup\n",
        "preheader-normed": "local instance : NormedAddCommGroup Complex := Complex.instNormedAddCommGroup\n",
    }

    for pname, preline in pre_modes.items():
        if preline is not None and pre_slot is None:
            continue
        for lname, local_line in local_modes.items():
            for cname, replacement in closing_variants.items():
                out = list(lines)
                if preline is not None:
                    out[pre_slot] = preline
                theorem_body = list(body)
                if local_idx is not None and local_line is not None:
                    theorem_body[local_idx] = local_line
                fixed = compact_or_pad(replacement, closing_height)
                if fixed is None:
                    # Borrow blank/comment lines immediately before the closing
                    # without changing the theorem's overall body height.
                    need = len(replacement) - closing_height
                    borrow = [i for i in range(max(0, closing_start - 8), closing_start) if not theorem_body[i].strip() or theorem_body[i].lstrip().startswith("--")]
                    if len(borrow) < need:
                        continue
                    remove = set(borrow[-need:])
                    theorem_body = [s for i, s in enumerate(theorem_body) if i not in remove]
                    adjusted_start = closing_start - sum(1 for i in remove if i < closing_start)
                    adjusted_end = closing_end - sum(1 for i in remove if i < closing_end)
                    theorem_body[adjusted_start:adjusted_end] = replacement
                    theorem_body = compact_or_pad(theorem_body, len(body))
                    if theorem_body is None:
                        continue
                else:
                    theorem_body[closing_start:closing_end] = fixed
                out[by_line + 1 : end] = theorem_body
                add(f"{pname}-{lname}-{cname}", out, f"hand:{pname}+{lname}+{cname}")

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
        "baseline_line_count": count,
        "theorem_start_line": start + 1,
        "theorem_header_sha256": sha("".join(header)),
        "closing_start_line": by_line + 2 + closing_start,
        "closing_height": closing_height,
        "candidate_count": len(manifest),
        "candidates": manifest,
    }
    (out_dir / "MANIFEST.json").write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(data, indent=2))


if __name__ == "__main__":
    main()
