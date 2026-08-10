#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import re
import sys
from pathlib import Path

ROOT = Path.cwd()
SOURCE = ROOT / "PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean"
HELPER_PATH = ROOT / "scripts/fa427_prepare_actualedge_candidate.py"
TARGET = "actualEdgeAmbientParam_hasDerivAt"
EXPECTED_LINES = 60453
DECL_RE = re.compile(
    r"^(?:protected\s+|private\s+|noncomputable\s+)?"
    r"(?:theorem|lemma|def|abbrev|instance|structure|class)\s+([^\s(:]+)"
)

VARIANTS = {
    "baseline",
    "scoped-normed-remove",
    "scoped-normed-normed",
    "scoped-normed-alias",
    "scoped-normed-remove-exact",
    "scoped-normed-remove-simpa",
    "scoped-normed-remove-convert",
    "scoped-normed-remove-change",
    "scoped-complex-remove",
    "scoped-complex-complex",
}


def load_helper():
    spec = importlib.util.spec_from_file_location("fa427_scoped_helper", HELPER_PATH)
    if spec is None or spec.loader is None:
        raise RuntimeError("unable to load FA427 source recovery helper")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def digest(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def line_count(text: str) -> int:
    return text.count("\n") + (0 if text.endswith("\n") else 1)


def declaration_span(text: str) -> tuple[int, int, int, str]:
    lines = text.splitlines(keepends=True)
    start = None
    for i, line in enumerate(lines):
        match = DECL_RE.match(line)
        if match and match.group(1) == TARGET:
            start = i
            break
    if start is None:
        raise RuntimeError(f"target declaration {TARGET} not found")
    end = len(lines)
    for i in range(start + 1, len(lines)):
        if DECL_RE.match(lines[i]):
            end = i
            break
    block = "".join(lines[start:end])
    marker = block.find(":= by")
    marker_len = len(":= by")
    if marker < 0:
        marker = block.find(":=")
        marker_len = len(":=")
    if marker < 0:
        raise RuntimeError("target theorem body marker not found")
    header = block[: marker + marker_len]
    body_start = start + header.count("\n")
    return start, body_start, end, header


def find_scope_slots(lines: list[str], start: int, end: int) -> tuple[list[int], int]:
    # We need two command slots before the theorem and one after it.  Reuse only
    # blank lines or an existing local AddCommGroup instance line; no theorem text moves.
    before: list[int] = []
    for i in range(max(0, start - 24), start):
        stripped = lines[i].strip()
        if stripped == "":
            before.append(i)
        elif (
            "AddCommGroup" in stripped
            and ("Complex" in stripped or "ℂ" in stripped)
            and stripped.startswith(("local instance", "instance"))
        ):
            before.append(i)
    before = sorted(set(before))
    if len(before) < 2:
        raise RuntimeError(f"only {len(before)} same-height pre-theorem command slots found")
    # Prefer the nearest two lines while preserving order: section then instance.
    before = before[-2:]

    after = None
    for i in range(end, min(len(lines), end + 24)):
        if lines[i].strip() == "":
            after = i
            break
    if after is None:
        # The final blank line inside the theorem body can host `end` only if it
        # is after the finishing command.  Search backwards conservatively.
        for i in range(end - 1, max(start, end - 8), -1):
            if lines[i].strip() == "":
                after = i
                break
    if after is None:
        raise RuntimeError("no same-height post-theorem scope-closing slot found")
    return before, after


def body_instance_line(lines: list[str], body_start: int, end: int) -> int | None:
    for i in range(body_start, min(end, body_start + 36)):
        if re.search(r"\bletI\s*:\s*AddCommGroup\s+(?:Complex|ℂ)", lines[i]):
            return i
    return None


def finish_span(lines: list[str], body_start: int, end: int) -> tuple[int, int] | None:
    hits = [i for i in range(body_start, end) if "hcomp" in lines[i]]
    if not hits:
        return None
    last = hits[-1]
    start = last
    while start > body_start:
        stripped = lines[start].lstrip()
        if stripped.startswith(("simpa", "exact", "convert", "refine", "show", "change")):
            break
        start -= 1
    if not lines[start].lstrip().startswith(("simpa", "exact", "convert", "refine", "show", "change")):
        return None
    return start, last + 1


def replace_same_height(lines: list[str], start: int, end: int, replacement: list[str]) -> None:
    height = end - start
    normalized = [line if line.endswith("\n") else line + "\n" for line in replacement]
    if len(normalized) > height:
        raise RuntimeError(f"replacement height {len(normalized)} exceeds source height {height}")
    normalized.extend(["\n"] * (height - len(normalized)))
    lines[start:end] = normalized


def prepare(baseline: str, variant: str) -> tuple[str, dict]:
    if variant == "baseline":
        start, body_start, end, header = declaration_span(baseline)
        return baseline, {
            "variant": variant,
            "baseline_sha256": digest(baseline),
            "candidate_sha256": digest(baseline),
            "line_count": line_count(baseline),
            "target_header_sha256": digest(header),
            "target_declaration": TARGET,
            "theorem_start_line": start + 1,
            "body_start_line": body_start + 1,
        }

    lines = baseline.splitlines(keepends=True)
    start, body_start, end, header = declaration_span(baseline)
    pre_slots, post_slot = find_scope_slots(lines, start, end)
    section_slot, instance_slot = pre_slots
    instance_kind = "normed" if variant.startswith("scoped-normed") else "complex"
    body_kind = "remove"
    if variant.endswith("-normed"):
        body_kind = "normed"
    elif variant.endswith("-alias"):
        body_kind = "alias"
    elif variant.endswith("-complex"):
        body_kind = "complex"
    finish_kind = "unchanged"
    for suffix in ("exact", "simpa", "convert", "change"):
        if variant.endswith("-" + suffix):
            finish_kind = suffix
            break

    lines[section_slot] = "section actualEdgeAmbientParamCanonicalInstanceSection\n"
    if instance_kind == "normed":
        lines[instance_slot] = (
            "local instance actualEdgeAmbientParamComplexAddCommGroup : AddCommGroup Complex := "
            "Complex.instNormedAddCommGroup.toAddCommGroup\n"
        )
    else:
        lines[instance_slot] = (
            "local instance actualEdgeAmbientParamComplexAddCommGroup : AddCommGroup Complex := "
            "Complex.addCommGroup\n"
        )
    lines[post_slot] = "end actualEdgeAmbientParamCanonicalInstanceSection\n"

    local_line = body_instance_line(lines, body_start, end)
    if local_line is not None:
        if body_kind == "remove":
            lines[local_line] = "\n"
        elif body_kind == "normed":
            lines[local_line] = (
                "  letI : AddCommGroup Complex := "
                "Complex.instNormedAddCommGroup.toAddCommGroup\n"
            )
        elif body_kind == "complex":
            lines[local_line] = "  letI : AddCommGroup Complex := Complex.addCommGroup\n"
        elif body_kind == "alias":
            lines[local_line] = (
                "  letI : AddCommGroup Complex := "
                "actualEdgeAmbientParamComplexAddCommGroup\n"
            )
    elif body_kind != "remove":
        blank = next(
            (i for i in range(body_start, min(end, body_start + 14)) if lines[i].strip() == ""),
            None,
        )
        if blank is None:
            raise RuntimeError("no proof-local instance or blank line available")
        if body_kind == "normed":
            lines[blank] = (
                "  letI : AddCommGroup Complex := "
                "Complex.instNormedAddCommGroup.toAddCommGroup\n"
            )
        elif body_kind == "complex":
            lines[blank] = "  letI : AddCommGroup Complex := Complex.addCommGroup\n"
        else:
            lines[blank] = (
                "  letI : AddCommGroup Complex := "
                "actualEdgeAmbientParamComplexAddCommGroup\n"
            )
        local_line = blank

    if finish_kind != "unchanged":
        span = finish_span(lines, body_start, end)
        if span is None:
            raise RuntimeError("hcomp finishing command not found")
        f_start, f_end = span
        replacements = {
            "exact": ["  exact hcomp\n"],
            "simpa": [
                "  simpa only [actualEdgeAmbientParam, actualEdgeNativeVelocity] using hcomp\n"
            ],
            "convert": ["  convert hcomp using 1 <;> rfl\n"],
            "change": [
                "  change HasDerivAt\n",
                "    (fun x => selectedCosetAmbientMap e.1\n",
                "      (modularTileEdgeAmbientParam e.2 x))\n",
                "    ((UpperHalfPlane.smulFDeriv (selectedCosetGL e.1)\n",
                "      ↑(modularTileEdgeParam e.2 t))\n",
                "      (modularTileEdgeVelocity e.2 t)) (t : Real)\n",
                "  exact hcomp\n",
            ],
        }
        replace_same_height(lines, f_start, f_end, replacements[finish_kind])

    candidate = "".join(lines)
    c_start, c_body_start, c_end, candidate_header = declaration_span(candidate)
    if candidate_header != header:
        raise RuntimeError("target theorem statement/header text changed")
    if line_count(candidate) != EXPECTED_LINES:
        raise RuntimeError(
            f"candidate height {line_count(candidate)} != {EXPECTED_LINES}"
        )
    metadata = {
        "variant": variant,
        "baseline_sha256": digest(baseline),
        "candidate_sha256": digest(candidate),
        "line_count": line_count(candidate),
        "target_header_sha256": digest(header),
        "target_declaration": TARGET,
        "theorem_start_line": start + 1,
        "body_start_line": body_start + 1,
        "section_slot_line": section_slot + 1,
        "instance_slot_line": instance_slot + 1,
        "end_slot_line": post_slot + 1,
        "proof_local_instance_line": None if local_line is None else local_line + 1,
        "instance_kind": instance_kind,
        "body_kind": body_kind,
        "finish_kind": finish_kind,
    }
    return candidate, metadata


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--variant", required=True, choices=sorted(VARIANTS))
    parser.add_argument("--output-dir", required=True)
    args = parser.parse_args()
    output = Path(args.output_dir)
    output.mkdir(parents=True, exist_ok=True)
    helper = load_helper()
    artifact_dir = output / "artifact-downloads"
    artifact_dir.mkdir(parents=True, exist_ok=True)
    baseline_data, provenance = helper.recover_exact_source(artifact_dir)
    baseline = baseline_data.decode("utf-8")
    candidate, metadata = prepare(baseline, args.variant)
    SOURCE.write_text(candidate, encoding="utf-8")
    (output / "Mock2_FunctionalAnalysis-baseline.lean").write_bytes(baseline_data)
    (output / "Mock2_FunctionalAnalysis-candidate.lean").write_text(
        candidate, encoding="utf-8"
    )
    (output / "PROVENANCE.json").write_text(
        json.dumps(provenance, indent=2) + "\n", encoding="utf-8"
    )
    (output / "CANDIDATE.json").write_text(
        json.dumps(metadata, indent=2) + "\n", encoding="utf-8"
    )
    print(json.dumps({**metadata, "provenance": provenance}, indent=2))


if __name__ == "__main__":
    main()
