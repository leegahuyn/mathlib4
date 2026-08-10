#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path

THEOREM = "actualEdgeAmbientParam_hasDerivAt"
DECL_RE = re.compile(r"^(?:/--|/-!|theorem\s|lemma\s|def\s|noncomputable\s+def\s|abbrev\s|instance\s|structure\s|namespace\s|section\s|end\b)")


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def locate(lines: list[str]) -> tuple[int, int, int]:
    starts = [i for i, s in enumerate(lines) if s.startswith(f"theorem {THEOREM}")]
    if len(starts) != 1:
        raise RuntimeError(f"expected one blocker theorem, found {len(starts)}")
    start = starts[0]
    by_line = next(i for i in range(start, start + 80) if ":= by" in lines[i])
    end = next(i for i in range(by_line + 1, len(lines)) if lines[i] and not lines[i][0].isspace() and DECL_RE.match(lines[i]))
    return start, by_line, end


def replace_exact(text: str, old: str, new: str, count: int) -> str | None:
    if text.count(old) != count:
        return None
    return text.replace(old, new)


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--baseline", required=True)
    ap.add_argument("--output", required=True)
    ap.add_argument("--refs", required=False)
    ap.add_argument("--limit", type=int, default=14)
    args = ap.parse_args()

    baseline = Path(args.baseline)
    original = baseline.read_text(encoding="utf-8")
    lines = original.splitlines(keepends=True)
    line_count = len(lines)
    start, by_line, end = locate(lines)
    header = "".join(lines[start : by_line + 1])
    header_sha = digest(header.encode())

    blank_candidates = [i for i in range(max(0, start - 30), start) if lines[i].strip() == ""]
    if not blank_candidates:
        raise RuntimeError("no blank line available before blocker theorem for fixed-height local instance")
    slot = blank_candidates[-1]

    local_old = "  letI : AddCommGroup Complex := Complex.addCommGroup\n"
    if original.count(local_old) != 1:
        # The 31726 source may already have changed the proof-local instance.
        local_old = next((s for s in lines[by_line + 1 : end] if "AddCommGroup Complex" in s and ("letI" in s or "let " in s)), "")

    candidates: list[tuple[str, str, str]] = []

    def add(name: str, text: str, provenance: str) -> None:
        out_lines = text.splitlines(keepends=True)
        out_start, out_by, _ = locate(out_lines)
        if len(out_lines) != line_count or out_start != start or out_by != by_line:
            raise RuntimeError(f"{name}: fixed-height/header-position violation")
        if "".join(out_lines[out_start : out_by + 1]) != header:
            raise RuntimeError(f"{name}: theorem statement/header changed")
        sha = digest(text.encode())
        if any(digest(t.encode()) == sha for _, t, _ in candidates):
            return
        candidates.append((name, text, provenance))

    def make(instance_line: str, proof_line: str | None, paired: bool = False, ring: bool = False) -> str | None:
        work = list(lines)
        work[slot] = instance_line + "\n"
        text = "".join(work)
        if local_old:
            repl = proof_line if proof_line is not None else "  -- proof uses the pre-header canonical Complex additive instance\n"
            if not repl.endswith("\n"):
                repl += "\n"
            if text.count(local_old) != 1:
                return None
            text = text.replace(local_old, repl)
        if paired:
            for edge, count in (("circularArc", 5), ("leftVerticalSegment", 2), ("rightVerticalSegment", 2)):
                old = f"GammaTwoActualPolygonEdge.paired ((q, GammaTwoModularTileEdge.{edge}) : GammaTwoActualPolygonEdge)"
                new = f"((q, GammaTwoModularTileEdge.{edge}) : GammaTwoActualPolygonEdge).paired"
                if text.count(old) == count:
                    text = text.replace(old, new)
                else:
                    old2 = f"GammaTwoActualPolygonEdge.paired\n        ((q, GammaTwoModularTileEdge.{edge}) : GammaTwoActualPolygonEdge)"
                    new2 = f"((q, GammaTwoModularTileEdge.{edge}) : GammaTwoActualPolygonEdge).paired"
                    if text.count(old2) not in (0, count):
                        return None
                    text = text.replace(old2, new2)
        if ring:
            anchor = "  rw [nativeActualEdgeFluxIntegral_left_eq_selectedPiola hT]\n\n"
            if text.count(anchor) == 1:
                text = text.replace(anchor, "  rw [nativeActualEdgeFluxIntegral_left_eq_selectedPiola hT]\n  ring\n")
            else:
                return None
        return text

    variants = [
        ("preheader-add-remove-local", "local instance : AddCommGroup Complex := Complex.instNormedAddCommGroup.toAddCommGroup", None),
        ("preheader-add-local-canonical", "local instance : AddCommGroup Complex := Complex.instNormedAddCommGroup.toAddCommGroup", "  letI : AddCommGroup Complex := Complex.instNormedAddCommGroup.toAddCommGroup"),
        ("preheader-normed-remove-local", "local instance : NormedAddCommGroup Complex := Complex.instNormedAddCommGroup", None),
        ("preheader-add-named-remove-local", "local instance actualEdgeCanonicalComplexAddCommGroup : AddCommGroup Complex := Complex.instNormedAddCommGroup.toAddCommGroup", None),
        ("preheader-add-priority-remove-local", "local instance (priority := 2000) : AddCommGroup Complex := Complex.instNormedAddCommGroup.toAddCommGroup", None),
    ]
    for name, inst, proof in variants:
        text = make(inst, proof)
        if text is not None:
            add(name, text, f"hand:{name}")
        text = make(inst, proof, paired=True)
        if text is not None:
            add(name + "-paired", text, f"hand:{name}+paired")
        text = make(inst, proof, paired=True, ring=True)
        if text is not None:
            add(name + "-paired-ring", text, f"hand:{name}+paired+ring")

    # Also test the verified baseline unchanged as a control.
    add("baseline-control", original, "verified baseline control")

    out = Path(args.output)
    out.mkdir(parents=True, exist_ok=True)
    manifest = []
    for idx, (name, text, provenance) in enumerate(candidates[: args.limit]):
        file = f"{idx:02d}-{name}.lean"
        (out / file).write_text(text, encoding="utf-8")
        manifest.append({"name": name, "provenance": provenance, "sha256": digest(text.encode()), "file": file})
    data = {
        "theorem": THEOREM,
        "baseline_sha256": digest(original.encode()),
        "baseline_line_count": line_count,
        "theorem_start_line": start + 1,
        "theorem_header_sha256": header_sha,
        "preheader_slot_line": slot + 1,
        "candidate_count": len(manifest),
        "candidates": manifest,
    }
    (out / "MANIFEST.json").write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(data, indent=2))


if __name__ == "__main__":
    main()
