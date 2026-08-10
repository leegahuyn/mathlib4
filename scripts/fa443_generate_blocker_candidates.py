from __future__ import annotations

import hashlib
import json
import os
import re
import shutil
from pathlib import Path
from typing import Any, Iterable

from fa442_pipeline_common import (
    BLOCKER,
    FA_PATH,
    REPO,
    audit_clean,
    declaration_sequence_sha,
    extract_blocker_header,
    line_count_bytes,
    sha256_bytes,
    slugify,
    source_metadata,
    write_json,
)

OUT = REPO / "build-logs/fa443-blocker-tournament/generated"
DONOR_ROOT = Path(os.environ.get(
    "FA443_DONOR_ROOT",
    REPO / "build-logs/fa442-pipeline-repair/prep/candidate-bundle",
))
CURRENT_BASELINE_SHA = os.environ.get("CURRENT_BASELINE_SHA", "")

TOP_LEVEL = re.compile(
    rb"^(?:@\[[^\n]*\]\s*)?(?:noncomputable\s+)?"
    rb"(?:private\s+|protected\s+)?"
    rb"(?:theorem|lemma|def|abbrev|instance|structure|class|inductive)\b",
)


def blocker_region(data: bytes) -> tuple[int, int, int, bytes, bytes]:
    marker = f"theorem {BLOCKER}".encode()
    start = data.find(marker)
    if start < 0:
        raise RuntimeError(f"missing theorem {BLOCKER}")
    header_end = data.find(b":= by", start)
    if header_end < 0:
        raise RuntimeError(f"missing ':= by' for {BLOCKER}")
    header_end += len(b":= by")
    line_end = data.find(b"\n", header_end)
    body_start = len(data) if line_end < 0 else line_end + 1
    cursor = body_start
    body_end = len(data)
    while cursor < len(data):
        next_nl = data.find(b"\n", cursor)
        if next_nl < 0:
            next_nl = len(data)
        raw = data[cursor:next_nl]
        if raw and raw[:1] not in b" \t" and (
            raw.startswith((b"/-", b"--", b"section", b"namespace", b"end ")) or
            TOP_LEVEL.match(raw)
        ):
            body_end = cursor
            break
        cursor = next_nl + 1
    return start, header_end, body_start, data[body_start:body_end], data[body_end:]


def normalize_body_height(body: bytes, target_newlines: int) -> bytes | None:
    lines = body.splitlines(keepends=True)
    while sum(x.count(b"\n") for x in lines) > target_newlines:
        removed = False
        for i in range(len(lines) - 1, -1, -1):
            if lines[i].strip() == b"":
                del lines[i]
                removed = True
                break
        if not removed:
            return None
    current = sum(x.count(b"\n") for x in lines)
    if current < target_newlines:
        lines.extend([b"\n"] * (target_newlines - current))
    return b"".join(lines)


def transplant(base: bytes, donor: bytes) -> bytes | None:
    b_start, b_header_end, b_body_start, b_body, b_suffix = blocker_region(base)
    d_start, d_header_end, d_body_start, d_body, _ = blocker_region(donor)
    if base[b_start:b_header_end] != donor[d_start:d_header_end]:
        return None
    target_height = b_body.count(b"\n")
    body = normalize_body_height(d_body, target_height)
    if body is None:
        return None
    candidate = base[:b_body_start] + body + b_suffix
    if line_count_bytes(candidate) != line_count_bytes(base):
        return None
    return candidate


def theorem_body_text(data: bytes) -> tuple[str, tuple[int, int, int, bytes, bytes]]:
    region = blocker_region(data)
    return region[3].decode("utf-8"), region


def replace_body(base: bytes, new_body: str) -> bytes | None:
    start, header_end, body_start, old_body, suffix = blocker_region(base)
    target = old_body.count(b"\n")
    normalized = normalize_body_height(new_body.encode(), target)
    if normalized is None:
        return None
    candidate = base[:body_start] + normalized + suffix
    if line_count_bytes(candidate) != line_count_bytes(base):
        return None
    return candidate


def line_transform(body: str, predicate, replacement) -> str | None:
    lines = body.splitlines(keepends=True)
    hits = [i for i, line in enumerate(lines) if predicate(line)]
    if not hits:
        return None
    for i in hits:
        ending = "\n" if lines[i].endswith("\n") else ""
        lines[i] = replacement(lines[i].rstrip("\n")) + ending
    return "".join(lines)


def candidate_valid(base_meta: dict[str, Any], data: bytes) -> tuple[bool, dict[str, Any]]:
    try:
        meta = source_metadata(data)
    except Exception as exc:
        return False, {"error": repr(exc)}
    checks = {
        "same_height": meta["line_count"] == base_meta["line_count"],
        "header_unchanged": (
            meta["blocker_header_sha256"] == base_meta["blocker_header_sha256"] and
            meta["blocker_header"] == base_meta["blocker_header"]
        ),
        "declaration_sequence_unchanged": (
            meta["declaration_sequence_sha256"] == base_meta["declaration_sequence_sha256"]
        ),
        "trust_audit_clean": audit_clean(meta["trust_audit"]),
    }
    return all(checks.values()), {**meta, **checks}


def donor_sources() -> Iterable[tuple[str, bytes]]:
    if not DONOR_ROOT.exists():
        return []
    out: list[tuple[str, bytes]] = []
    for path in sorted(DONOR_ROOT.rglob("source.lean")):
        try:
            data = path.read_bytes()
            if f"theorem {BLOCKER}".encode() in data:
                out.append((f"donor-{path.parent.name}", data))
        except Exception:
            continue
    return out


def main() -> None:
    if OUT.exists():
        shutil.rmtree(OUT)
    (OUT / "candidate-bundle").mkdir(parents=True)
    base = FA_PATH.read_bytes()
    base_sha = sha256_bytes(base)
    if CURRENT_BASELINE_SHA and base_sha != CURRENT_BASELINE_SHA:
        raise RuntimeError(
            f"current selected baseline SHA mismatch: expected {CURRENT_BASELINE_SHA}, got {base_sha}"
        )
    base_meta = source_metadata(base)
    base_body, _ = theorem_body_text(base)
    variants: dict[str, tuple[str, bytes, list[str]]] = {}

    def add(name: str, data: bytes | None, origins: list[str]) -> None:
        if data is None or data == base:
            return
        ok, meta = candidate_valid(base_meta, data)
        if not ok:
            return
        sha = meta["sha256"]
        if sha not in variants:
            variants[sha] = (name, data, origins)
        else:
            variants[sha][2].extend(origins)

    # Historical proof-body donors: header and file height remain fixed.
    for name, donor in donor_sources():
        add(name, transplant(base, donor), [name])

    # Instance-normalization variants. Every edit stays inside the proof body.
    instance_lines = [
        "",
        "  letI : AddCommGroup Complex := Complex.instNormedAddCommGroup.toAddCommGroup",
        "  letI : AddCommGroup Complex := inferInstance",
        "  letI : AddCommGroup ℂ := Complex.instNormedAddCommGroup.toAddCommGroup",
        "  letI : AddCommGroup ℂ := inferInstance",
        "  letI := Complex.instNormedAddCommGroup.toAddCommGroup",
    ]
    instance_bodies: list[tuple[str, str]] = [("identity", base_body)]
    for index, replacement in enumerate(instance_lines):
        transformed = line_transform(
            base_body,
            lambda line: "letI" in line and "AddCommGroup" in line and "Complex" in line,
            lambda old, replacement=replacement: replacement,
        )
        if transformed is not None:
            instance_bodies.append((f"instance-{index}", transformed))

    global_substitutions = [
        (
            "legacy-to-normed-parent",
            "Complex.addCommGroup",
            "Complex.instNormedAddCommGroup.toAddCommGroup",
        ),
        (
            "normed-parent-to-legacy",
            "Complex.instNormedAddCommGroup.toAddCommGroup",
            "Complex.addCommGroup",
        ),
    ]
    for name, old, new in global_substitutions:
        if old in base_body:
            instance_bodies.append((name, base_body.replace(old, new)))

    tail_replacements = [
        ("tail-exact-hcomp", re.compile(r"(?m)^([ \t]*)simpa[^\n]*using\s+hcomp\s*$"), r"\1exact hcomp"),
        ("tail-convert-rfl", re.compile(r"(?m)^([ \t]*)simpa[^\n]*using\s+hcomp\s*$"), r"\1convert hcomp using 1 <;> rfl"),
        ("tail-convert-simp", re.compile(r"(?m)^([ \t]*)simpa[^\n]*using\s+hcomp\s*$"), r"\1convert hcomp using 1 <;> simp"),
        ("tail-simpa-only", re.compile(r"(?m)^([ \t]*)simpa\s+\[([^\]]*)\]\s+using\s+hcomp\s*$"), r"\1simpa only [\2] using hcomp"),
    ]

    for iname, body in instance_bodies:
        add(iname, replace_body(base, body), [iname])
        for tname, pattern, repl in tail_replacements:
            if pattern.search(body):
                add(f"{iname}__{tname}", replace_body(base, pattern.sub(repl, body)), [iname, tname])

    # Direct local expression normalizations around hbase/hcomp/final goal.
    local_edits = [
        (
            "simpa-at-hbase",
            re.compile(r"(?m)^([ \t]*)have\s+hbase\s*:=([^\n]*)$"),
            r"\1have hbase :=\2\n\1simp only at hbase",
        ),
        (
            "change-at-hcomp",
            re.compile(r"(?m)^([ \t]*)simpa([^\n]*)using\s+hcomp\s*$"),
            r"\1change _\n\1simpa\2using hcomp",
        ),
        (
            "convert-hcomp-simp-all",
            re.compile(r"(?m)^([ \t]*)simpa[^\n]*using\s+hcomp\s*$"),
            r"\1convert hcomp using 1 <;> simp_all",
        ),
    ]
    for name, pattern, repl in local_edits:
        if pattern.search(base_body):
            add(name, replace_body(base, pattern.sub(repl, base_body)), [name])

    used: set[str] = set()
    matrix: list[dict[str, Any]] = []

    # Current-run baseline is one explicit tournament entry.
    baseline_slug = "baseline-current"
    baseline_dir = OUT / "candidate-bundle" / baseline_slug
    baseline_dir.mkdir(parents=True)
    (baseline_dir / "source.lean").write_bytes(base)
    base_record = {
        **base_meta,
        "variant": "baseline-current",
        "slug": baseline_slug,
        "is_baseline": True,
        "origins": ["checked-in selected source before FA443 tournament"],
    }
    write_json(baseline_dir / "metadata.json", base_record)
    matrix.append({
        "variant": "baseline-current",
        "slug": baseline_slug,
        "sha256": base_sha,
        "is_baseline": True,
    })
    used.add(baseline_slug)

    for sha, (name, data, origins) in sorted(variants.items()):
        slug = slugify(name)
        serial = 2
        while slug in used:
            slug = f"{slugify(name)}-{serial}"
            serial += 1
        used.add(slug)
        target = OUT / "candidate-bundle" / slug
        target.mkdir(parents=True)
        (target / "source.lean").write_bytes(data)
        meta = source_metadata(data)
        meta.update({
            "variant": name,
            "slug": slug,
            "is_baseline": False,
            "origins": sorted(set(origins)),
        })
        write_json(target / "metadata.json", meta)
        matrix.append({
            "variant": name,
            "slug": slug,
            "sha256": sha,
            "is_baseline": False,
        })

    if len(matrix) < 2:
        raise RuntimeError("no valid proof-body candidate was generated")
    write_json(OUT / "baseline-meta.json", base_record)
    write_json(OUT / "matrix.json", {"include": matrix})
    write_json(OUT / "inventory.json", {
        "current_baseline_sha256": base_sha,
        "line_count": base_meta["line_count"],
        "blocker": BLOCKER,
        "candidate_count_including_baseline": len(matrix),
        "candidates": matrix,
    })
    print(json.dumps({
        "baseline_sha256": base_sha,
        "candidate_count_including_baseline": len(matrix),
    }, indent=2))


if __name__ == "__main__":
    main()
