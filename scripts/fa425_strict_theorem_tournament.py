#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
from dataclasses import dataclass
from pathlib import Path

THEOREM = "actualEdgeAmbientParam_hasDerivAt"
SOURCE_PATH = "PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean"
DECL_RE = re.compile(
    r"^(?:/--|/-!|theorem\s|lemma\s|def\s|noncomputable\s+def\s|abbrev\s|"
    r"noncomputable\s+abbrev\s|instance\s|structure\s|class\s|namespace\s|section\s|end\b)"
)


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


@dataclass(frozen=True)
class Slice:
    start: int
    by_line: int
    end: int
    header: tuple[str, ...]
    body: tuple[str, ...]


def theorem_slice(lines: list[str]) -> Slice:
    starts = [i for i, line in enumerate(lines) if line.startswith(f"theorem {THEOREM}")]
    if len(starts) != 1:
        raise RuntimeError(f"expected one {THEOREM}, found {len(starts)}")
    start = starts[0]
    by_line = next((i for i in range(start, min(len(lines), start + 80)) if ":= by" in lines[i]), None)
    if by_line is None:
        raise RuntimeError("could not find := by in blocker theorem header")
    end = None
    for i in range(by_line + 1, len(lines)):
        if lines[i] and not lines[i][0].isspace() and DECL_RE.match(lines[i]):
            end = i
            break
    if end is None:
        raise RuntimeError("could not find declaration after blocker theorem")
    return Slice(
        start=start,
        by_line=by_line,
        end=end,
        header=tuple(lines[start : by_line + 1]),
        body=tuple(lines[by_line + 1 : end]),
    )


def compact_body(body: list[str], target: int) -> list[str] | None:
    if len(body) <= target:
        return body + ["\n"] * (target - len(body))
    removable = [i for i, line in enumerate(body) if not line.strip() or line.lstrip().startswith("--")]
    remove_count = len(body) - target
    if len(removable) < remove_count:
        return None
    remove = set(removable[-remove_count:])
    compacted = [line for i, line in enumerate(body) if i not in remove]
    return compacted if len(compacted) == target else None


def source_from_ref(ref: str) -> bytes | None:
    proc = subprocess.run(
        ["git", "show", f"{ref}:{SOURCE_PATH}"],
        stdout=subprocess.PIPE,
        stderr=subprocess.DEVNULL,
        check=False,
    )
    return proc.stdout if proc.returncode == 0 and proc.stdout else None


def add_candidate(
    candidates: dict[str, dict[str, object]],
    baseline_lines: list[str],
    sl: Slice,
    name: str,
    body: list[str],
    provenance: str,
    expected_line_count: int,
) -> None:
    fixed = compact_body(body, len(sl.body))
    if fixed is None:
        return
    out = baseline_lines[: sl.by_line + 1] + fixed + baseline_lines[sl.end :]
    if len(out) != expected_line_count:
        raise RuntimeError(f"{name}: fixed-height violation {len(out)} != {expected_line_count}")
    out_sl = theorem_slice(out)
    if out_sl.header != sl.header:
        raise RuntimeError(f"{name}: theorem statement/header changed")
    data = "".join(out).encode("utf-8")
    digest = sha256_bytes(data)
    if digest in candidates:
        return
    candidates[digest] = {
        "name": name,
        "provenance": provenance,
        "sha256": digest,
        "bytes": data,
    }


def transformed(body: tuple[str, ...], old: str, new: str) -> list[str] | None:
    text = "".join(body)
    if text.count(old) != 1:
        return None
    return text.replace(old, new).splitlines(keepends=True)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--baseline", required=True)
    parser.add_argument("--output", required=True)
    parser.add_argument("--refs", required=True, help="newline-separated fetched donor refs")
    parser.add_argument("--limit", type=int, default=14)
    args = parser.parse_args()

    baseline_path = Path(args.baseline)
    baseline_data = baseline_path.read_bytes()
    baseline_lines = baseline_data.decode("utf-8").splitlines(keepends=True)
    baseline_count = len(baseline_lines)
    sl = theorem_slice(baseline_lines)
    header_sha = sha256_bytes("".join(sl.header).encode("utf-8"))

    candidates: dict[str, dict[str, object]] = {}
    add_candidate(candidates, baseline_lines, sl, "baseline", list(sl.body), "verified baseline", baseline_count)

    refs = [line.strip() for line in Path(args.refs).read_text(encoding="utf-8").splitlines() if line.strip()]
    for ref in refs:
        data = source_from_ref(ref)
        if data is None:
            continue
        try:
            donor_lines = data.decode("utf-8").splitlines(keepends=True)
            donor_sl = theorem_slice(donor_lines)
        except Exception:
            continue
        add_candidate(
            candidates,
            baseline_lines,
            sl,
            f"donor-{re.sub(r'[^A-Za-z0-9_.-]+', '-', ref)[-90:]}",
            list(donor_sl.body),
            ref,
            baseline_count,
        )

    local_old = "  letI : AddCommGroup Complex := Complex.addCommGroup\n"
    local_variants = {
        "canonical-explicit": "  letI : AddCommGroup Complex := Complex.instNormedAddCommGroup.toAddCommGroup\n",
        "canonical-infer": "  letI : AddCommGroup Complex := inferInstance\n",
        "canonical-default": "  -- use the canonical inferred Complex additive structure\n",
        "canonical-noninstance-let": "  let _ : AddCommGroup Complex := Complex.instNormedAddCommGroup.toAddCommGroup\n",
    }
    for name, replacement in local_variants.items():
        body = transformed(sl.body, local_old, replacement)
        if body is not None:
            add_candidate(candidates, baseline_lines, sl, name, body, f"hand:{name}", baseline_count)

    # If a canonical-instance donor still fails at the final coercion/simplification,
    # test narrowly stronger proof closings without touching the theorem header.
    snapshot = list(candidates.values())
    closing_patterns = [
        (
            "  simpa only [actualEdgeAmbientParam, actualEdgeNativeVelocity] using hcomp\n",
            "  simpa [actualEdgeAmbientParam, actualEdgeNativeVelocity] using hcomp\n",
            "simpa-full",
        ),
        (
            "  simpa only [actualEdgeAmbientParam, actualEdgeNativeVelocity] using hcomp\n",
            "  change HasDerivAt (fun x : ℝ => selectedCosetAmbientMap e.1\n"
            "    (modularTileEdgeAmbientParam e.2 x)) (actualEdgeNativeVelocity e t) (t : ℝ)\n"
            "  simpa only [actualEdgeNativeVelocity] using hcomp\n",
            "change-domain-then-exact",
        ),
        (
            "  simpa only [actualEdgeAmbientParam, actualEdgeNativeVelocity] using hcomp\n",
            "  change HasDerivAt (fun x : Real => selectedCosetAmbientMap e.1\n"
            "    (modularTileEdgeAmbientParam e.2 x)) _ _\n"
            "  simpa only [actualEdgeNativeVelocity] using hcomp\n",
            "change-underscores",
        ),
    ]
    for item in snapshot:
        src_lines = item["bytes"].decode("utf-8").splitlines(keepends=True)  # type: ignore[index]
        item_sl = theorem_slice(src_lines)
        for old, new, suffix in closing_patterns:
            body = transformed(item_sl.body, old, new)
            if body is None:
                continue
            add_candidate(
                candidates,
                baseline_lines,
                sl,
                f"{item['name']}-{suffix}",
                body,
                f"{item['provenance']}+hand:{suffix}",
                baseline_count,
            )

    out_dir = Path(args.output)
    out_dir.mkdir(parents=True, exist_ok=True)
    manifest: list[dict[str, object]] = []
    ordered = list(candidates.values())[: args.limit]
    for idx, item in enumerate(ordered):
        filename = f"{idx:02d}-{item['name']}.lean"
        path = out_dir / filename
        path.write_bytes(item.pop("bytes"))  # type: ignore[arg-type]
        manifest.append({**item, "file": filename})

    metadata = {
        "theorem": THEOREM,
        "baseline_sha256": sha256_bytes(baseline_data),
        "baseline_line_count": baseline_count,
        "theorem_start_line": sl.start + 1,
        "theorem_end_line": sl.end,
        "theorem_header_sha256": header_sha,
        "theorem_body_line_count": len(sl.body),
        "candidate_count": len(manifest),
        "candidates": manifest,
    }
    (out_dir / "MANIFEST.json").write_text(json.dumps(metadata, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(metadata, indent=2))


if __name__ == "__main__":
    main()
