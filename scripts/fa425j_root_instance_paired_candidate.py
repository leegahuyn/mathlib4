#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path

THEOREM = "actualEdgeAmbientParam_hasDerivAt"
TOP_RE = re.compile(r"^(?:/--|/-!|theorem\s|lemma\s|def\s|noncomputable\s+def\s|abbrev\s|instance\s|local\s+instance\s|attribute\s|structure\s|namespace\s|section\s|end\b)")


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


def doc_start(lines: list[str], start: int) -> int:
    i = start - 1
    while i >= 0 and not lines[i].strip():
        i -= 1
    if i >= 0 and lines[i].strip().endswith("-/"):
        j = i
        while j >= 0 and not lines[j].lstrip().startswith(("/--", "/-!")):
            j -= 1
        if j >= 0:
            return j
    return start


def preserve_newlines(old: str, new: str) -> str:
    missing = old.count("\n") - new.count("\n")
    if missing < 0:
        raise RuntimeError("replacement increases line count")
    return new + ("\n" * missing)


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--baseline", required=True)
    ap.add_argument("--output", required=True)
    ap.add_argument("--refs", required=False)
    ap.add_argument("--limit", type=int, default=14)
    args = ap.parse_args()

    baseline_path = Path(args.baseline)
    original = baseline_path.read_text(encoding="utf-8")
    lines = original.splitlines(keepends=True)
    total = len(lines)
    if total != 60453:
        raise RuntimeError(f"baseline line count {total} != 60453")
    start, by_line, theorem_end = locate(lines)
    header = tuple(lines[start : by_line + 1])
    dstart = doc_start(lines, start)

    pre_slots = [
        i for i in range(max(0, dstart - 80), dstart)
        if lines[i].strip() == "" or (lines[i].startswith("--") and not lines[i].startswith("/--"))
    ]
    post_slots = [i for i in range(by_line + 1, theorem_end) if lines[i].strip() == ""]
    if not pre_slots or not post_slots:
        raise RuntimeError("fixed-height pre/post slots unavailable")
    pre_slot = pre_slots[-1]
    post_slot = post_slots[-1]
    lines[pre_slot] = "attribute [-instance] Complex.addCommGroup\n"
    lines[post_slot] = "attribute [instance] Complex.addCommGroup\n"

    local_indices = [
        i for i in range(by_line + 1, theorem_end)
        if "AddCommGroup Complex" in lines[i] and ("letI" in lines[i] or "let " in lines[i])
    ]
    if local_indices:
        lines[local_indices[0]] = "  -- theorem and proof use the canonical surrounding Complex additive instance\n"

    text = "".join(lines)
    paired_counts: dict[str, int] = {}
    for edge, expected in (
        ("circularArc", 5),
        ("leftVerticalSegment", 2),
        ("rightVerticalSegment", 2),
    ):
        pattern = re.compile(
            r"GammaTwoActualPolygonEdge\.paired\s*"
            r"\(\(q,\s*GammaTwoModularTileEdge\." + re.escape(edge) + r"\)\s*:\s*GammaTwoActualPolygonEdge\)"
        )
        matches = list(pattern.finditer(text))
        paired_counts[edge] = len(matches)
        if len(matches) not in (0, expected):
            raise RuntimeError(f"{edge}: expected zero or {expected} matches, found {len(matches)}")
        if matches:
            text = pattern.sub(
                lambda m, edge=edge: preserve_newlines(
                    m.group(0),
                    f"((q, GammaTwoModularTileEdge.{edge}) : GammaTwoActualPolygonEdge).paired",
                ),
                text,
            )

    out_lines = text.splitlines(keepends=True)
    ring_anchor = "  rw [nativeActualEdgeFluxIntegral_left_eq_selectedPiola hT]\n"
    anchor_indices = [i for i, s in enumerate(out_lines) if s == ring_anchor]
    ring_inserted = False
    if len(anchor_indices) == 1:
        idx = anchor_indices[0]
        if idx + 1 < len(out_lines) and out_lines[idx + 1].strip() == "":
            out_lines[idx + 1] = "  ring\n"
            ring_inserted = True
    elif len(anchor_indices) > 1:
        raise RuntimeError(f"ring anchor appears {len(anchor_indices)} times")

    if len(out_lines) != total:
        raise RuntimeError(f"candidate line count {len(out_lines)} != {total}")
    out_start, out_by, _ = locate(out_lines)
    if out_start != start or out_by != by_line or tuple(out_lines[out_start : out_by + 1]) != header:
        raise RuntimeError("theorem statement/header/start changed")
    candidate = "".join(out_lines)
    candidate_sha = sha(candidate)
    if candidate_sha == sha(original):
        raise RuntimeError("candidate is identical to baseline")

    out = Path(args.output)
    out.mkdir(parents=True, exist_ok=True)
    filename = "00-root-instance-paired.lean"
    (out / filename).write_text(candidate, encoding="utf-8")
    manifest = {
        "theorem": THEOREM,
        "strategy": "disable custom Complex.addCommGroup during theorem; remove proof-local instance; normalize paired calls",
        "baseline_sha256": sha(original),
        "baseline_line_count": total,
        "theorem_start_line": start + 1,
        "theorem_header_sha256": sha("".join(header)),
        "pre_disable_slot_line": pre_slot + 1,
        "post_reenable_slot_line": post_slot + 1,
        "paired_replacements": paired_counts,
        "ring_inserted": ring_inserted,
        "candidate_count": 1,
        "candidates": [{
            "name": "root-instance-paired",
            "provenance": "deterministic fixed-height root instance repair plus PASS413 paired-call normalization",
            "kind": "single-cumulative-candidate",
            "sha256": candidate_sha,
            "file": filename,
        }],
    }
    (out / "MANIFEST.json").write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(manifest, indent=2))


if __name__ == "__main__":
    main()
