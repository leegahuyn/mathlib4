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
    local_idx = next((i for i, s in enumerate(body) if "AddCommGroup Complex" in s and ("letI" in s or "let " in s)), None)
    if local_idx is None:
        # PASS423 may have replaced the line by a comment.  Reuse the earliest
        # blank/comment proof slot before hcomp is constructed.
        hcomp_decl = next((i for i, s in enumerate(body) if "have hcomp" in s), len(body))
        local_idx = next((i for i in range(hcomp_decl) if not body[i].strip() or body[i].lstrip().startswith("--")), None)
    if local_idx is None:
        raise RuntimeError("no fixed-height slot for instance equality proof")

    hcomp_uses = [i for i, s in enumerate(body) if "hcomp" in s]
    if not hcomp_uses:
        raise RuntimeError("no hcomp use in blocker theorem")
    closing_idx = hcomp_uses[-1]

    equality_variants = {
        "forward-rfl": "  have hinst : Complex.addCommGroup = Complex.instNormedAddCommGroup.toAddCommGroup := by rfl\n",
        "forward-ext": "  have hinst : Complex.addCommGroup = Complex.instNormedAddCommGroup.toAddCommGroup := by ext <;> rfl\n",
        "forward-structure-ext": "  have hinst : Complex.addCommGroup = Complex.instNormedAddCommGroup.toAddCommGroup := by apply AddCommGroup.ext <;> rfl\n",
        "reverse-rfl": "  have hinst : Complex.instNormedAddCommGroup.toAddCommGroup = Complex.addCommGroup := by rfl\n",
        "reverse-ext": "  have hinst : Complex.instNormedAddCommGroup.toAddCommGroup = Complex.addCommGroup := by ext <;> rfl\n",
    }
    forward_closings = {
        "simpa-only": "  simpa only [actualEdgeAmbientParam, actualEdgeNativeVelocity, hinst] using hcomp\n",
        "simpa-full": "  simpa [actualEdgeAmbientParam, actualEdgeNativeVelocity, hinst] using hcomp\n",
        "rw-goal": "  rw [hinst]; simpa only [actualEdgeAmbientParam, actualEdgeNativeVelocity] using hcomp\n",
        "cases": "  cases hinst; simpa only [actualEdgeAmbientParam, actualEdgeNativeVelocity] using hcomp\n",
        "rw-all": "  rw [hinst] at *; simpa only [actualEdgeAmbientParam, actualEdgeNativeVelocity] using hcomp\n",
    }
    reverse_closings = {
        "simpa-only-rev": "  simpa only [actualEdgeAmbientParam, actualEdgeNativeVelocity, hinst] using hcomp\n",
        "rw-hcomp": "  rw [hinst] at hcomp; simpa only [actualEdgeAmbientParam, actualEdgeNativeVelocity] using hcomp\n",
        "cases-rev": "  cases hinst; simpa only [actualEdgeAmbientParam, actualEdgeNativeVelocity] using hcomp\n",
        "rw-goal-rev": "  rw [← hinst]; simpa only [actualEdgeAmbientParam, actualEdgeNativeVelocity] using hcomp\n",
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

    for ename, equality in equality_variants.items():
        closings = reverse_closings if ename.startswith("reverse") else forward_closings
        for cname, closing in closings.items():
            b = list(body)
            b[local_idx] = equality
            b[closing_idx] = closing
            add(f"{ename}-{cname}", b, f"hand:{ename}+{cname}")

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
        "instance_equality_slot_line": by_line + 2 + local_idx,
        "closing_slot_line": by_line + 2 + closing_idx,
        "candidate_count": len(manifest),
        "candidates": manifest,
    }
    (out_dir / "MANIFEST.json").write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(data, indent=2))


if __name__ == "__main__":
    main()
