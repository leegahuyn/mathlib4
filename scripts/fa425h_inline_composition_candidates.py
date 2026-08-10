#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path

THEOREM = "actualEdgeAmbientParam_hasDerivAt"
TOP_RE = re.compile(r"^(?:/--|/-!|theorem\s|lemma\s|def\s|noncomputable\s+def\s|abbrev\s|instance\s|local\s+instance\s|attribute\s|structure\s|namespace\s|section\s|end\b)")
PROOF_COMMAND_RE = re.compile(r"^  (?:have|simpa|exact|convert|rw|show|change|refine|apply|constructor|calc|rfl|aesop|simp)\b")


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
    start, by_line, end = locate(lines)
    header = tuple(lines[start : by_line + 1])
    body = lines[by_line + 1 : end]

    hcomp_start = next((i for i, s in enumerate(body) if re.match(r"^  have hcomp\b", s)), None)
    if hcomp_start is None:
        raise RuntimeError("have hcomp declaration not found")
    hcomp_end = len(body)
    for i in range(hcomp_start + 1, len(body)):
        if PROOF_COMMAND_RE.match(body[i]):
            hcomp_end = i
            break
    if hcomp_end <= hcomp_start:
        raise RuntimeError("invalid hcomp block")

    closing_use = next((i for i in range(len(body) - 1, hcomp_end - 1, -1) if "hcomp" in body[i]), None)
    if closing_use is None:
        raise RuntimeError("final hcomp use not found")
    closing_start = closing_use
    while closing_start > hcomp_end and (
        body[closing_start - 1].rstrip().endswith(("using", "from"))
        or body[closing_start - 1].lstrip().startswith(("simpa", "convert", "exact", "show", "change"))
    ):
        closing_start -= 1
    closing_end = closing_use + 1

    hcomp_text = "".join(body[hcomp_start:hcomp_end])
    split = re.split(r":=\s*", hcomp_text, maxsplit=1)
    if len(split) != 2:
        raise RuntimeError("could not extract hcomp RHS")
    rhs = split[1].rstrip()
    # Normalize indentation only at the outermost level; internal proof lines stay intact.
    rhs_lines = rhs.splitlines()
    rhs_expr = "\n".join(rhs_lines)

    region_start = hcomp_start
    region_end = closing_end
    region_height = region_end - region_start
    local_idx = next((i for i, s in enumerate(body[:hcomp_start]) if "AddCommGroup Complex" in s and ("letI" in s or "let " in s)), None)

    templates = {
        "inline-simpa-only": [
            "  simpa only [actualEdgeAmbientParam, actualEdgeNativeVelocity] using\n",
            f"    ({rhs_expr})\n",
        ],
        "inline-simpa-full": [
            "  simpa [actualEdgeAmbientParam, actualEdgeNativeVelocity] using\n",
            f"    ({rhs_expr})\n",
        ],
        "inline-unfold-custom": [
            "  simpa only [actualEdgeAmbientParam, actualEdgeNativeVelocity, Complex.addCommGroup] using\n",
            f"    ({rhs_expr})\n",
        ],
        "inline-unfold-both": [
            "  simpa only [actualEdgeAmbientParam, actualEdgeNativeVelocity, Complex.addCommGroup, Complex.instNormedAddCommGroup] using\n",
            f"    ({rhs_expr})\n",
        ],
        "inline-convert-rfl": [
            f"  convert ({rhs_expr}) using 1 <;> rfl\n",
        ],
        "inline-rebundle": [
            "  simpa only [actualEdgeAmbientParam, actualEdgeNativeVelocity] using\n",
            f"    ({rhs_expr}).hasFDerivAt.hasDerivAt\n",
        ],
        "inline-typed-have": [
            "  have htarget : HasDerivAt (actualEdgeAmbientParam e) (actualEdgeNativeVelocity e t) (t : Real) := by\n",
            "    simpa only [actualEdgeAmbientParam, actualEdgeNativeVelocity] using\n",
            f"      ({rhs_expr})\n",
            "  exact htarget\n",
        ],
    }
    local_modes = {
        "keep-local": None,
        "canonical-local": "  letI : AddCommGroup Complex := Complex.instNormedAddCommGroup.toAddCommGroup\n",
        "remove-local": "  -- inline expression is elaborated under the theorem target instance\n",
    }

    candidates = []
    seen = set()

    def add(name: str, new_body: list[str], provenance: str) -> None:
        out = lines[: by_line + 1] + new_body + lines[end:]
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

    for lname, local_line in local_modes.items():
        for tname, replacement in templates.items():
            fixed = compact_or_pad(replacement, region_height)
            if fixed is None:
                continue
            b = list(body)
            if local_idx is not None and local_line is not None:
                b[local_idx] = local_line
            b[region_start:region_end] = fixed
            add(f"{lname}-{tname}", b, f"hand:{lname}+{tname}")

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
        "hcomp_region_start_line": by_line + 2 + region_start,
        "hcomp_region_end_line": by_line + 1 + region_end,
        "hcomp_region_height": region_height,
        "candidate_count": len(manifest),
        "candidates": manifest,
    }
    (out_dir / "MANIFEST.json").write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(data, indent=2))


if __name__ == "__main__":
    main()
