#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import zipfile
from pathlib import Path

ROOT = Path.cwd()
SOURCE = ROOT / "PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean"
TARGET = "actualEdgeAmbientParam_hasDerivAt"
EXPECTED_SHA = "71dc36f16ebea92d537aa40a5d420443e4bcb93ccb76fea31efb40a6cb5c3aa0"
RUN_ID = 31317392557
EXPECTED_LINES = 60453
REPO = os.environ.get("GITHUB_REPOSITORY", "leegahuyn/mathlib4")
DECL_RE = re.compile(
    r"^(?:protected\s+|private\s+|noncomputable\s+)?"
    r"(?:theorem|lemma|def|abbrev|instance|structure|class)\s+([^\s(:]+)"
)

VARIANTS = {
    "baseline",
    "body-remove",
    "body-normed",
    "body-complex",
    "pre-normed-body-remove",
    "pre-normed-body-normed",
    "pre-normed-body-alias",
    "pre-complex-body-remove",
    "pre-normed-remove-exact",
    "pre-normed-remove-simpa",
    "pre-normed-remove-convert",
    "no-pre-remove-simpa",
}


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def lines(data: bytes) -> int:
    return data.count(b"\n") + (0 if data.endswith(b"\n") else 1)


def run(args: list[str], *, text: bool = True, stdout=None, stderr=None):
    return subprocess.run(
        args, cwd=ROOT, text=text, stdout=stdout, stderr=stderr, check=False
    )


def artifacts() -> list[dict]:
    p = run(
        ["gh", "api", "--paginate", f"/repos/{REPO}/actions/runs/{RUN_ID}/artifacts?per_page=100"],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if p.returncode != 0:
        return []
    raw = p.stdout.strip()
    if not raw:
        return []
    pages: list[object] = []
    try:
        pages = [json.loads(raw)]
    except json.JSONDecodeError:
        dec = json.JSONDecoder()
        i = 0
        while i < len(raw):
            while i < len(raw) and raw[i].isspace():
                i += 1
            if i >= len(raw):
                break
            obj, i = dec.raw_decode(raw, i)
            pages.append(obj)
    result: list[dict] = []
    for page in pages:
        if isinstance(page, dict):
            result.extend(page.get("artifacts", []))
        elif isinstance(page, list):
            result.extend(x for x in page if isinstance(x, dict))
    return result


def recover_exact_source(tmp: Path) -> tuple[bytes, dict]:
    if SOURCE.exists():
        current = SOURCE.read_bytes()
        if sha(current) == EXPECTED_SHA and lines(current) == EXPECTED_LINES:
            return current, {"source": "checked-in exact SHA"}

    hits: list[tuple[Path, bytes, int, str]] = []
    checks: list[dict] = []
    for art in artifacts():
        if art.get("expired"):
            continue
        aid = int(art["id"])
        name = str(art.get("name", ""))
        z = tmp / f"{aid}.zip"
        u = tmp / str(aid)
        u.mkdir(parents=True, exist_ok=True)
        with z.open("wb") as h:
            p = run(
                ["gh", "api", f"/repos/{REPO}/actions/artifacts/{aid}/zip"],
                text=False,
                stdout=h,
                stderr=subprocess.PIPE,
            )
        row = {"artifact_id": aid, "name": name, "download_exit": p.returncode}
        checks.append(row)
        if p.returncode != 0:
            continue
        try:
            with zipfile.ZipFile(z) as ar:
                ar.extractall(u)
        except zipfile.BadZipFile:
            row["bad_zip"] = True
            continue
        local_hits = 0
        for f in u.rglob("*"):
            if not f.is_file():
                continue
            data = f.read_bytes()
            if sha(data) == EXPECTED_SHA:
                local_hits += 1
                hits.append((f, data, aid, name))
        row["exact_sha_hits"] = local_hits
    if not hits:
        raise RuntimeError("PASS423 exact SHA source not found in checked source or artifacts")
    hits.sort(
        key=lambda item: (
            not item[0].name.endswith(".lean"),
            "source" not in str(item[0]).lower(),
            len(str(item[0])),
        )
    )
    f, data, aid, name = hits[0]
    if lines(data) != EXPECTED_LINES:
        raise RuntimeError(f"exact SHA candidate has line count {lines(data)}")
    return data, {
        "source": "PASS423 artifact exact SHA",
        "run_id": RUN_ID,
        "all_exact_hits": len(hits),
        "selected_artifact_id": aid,
        "selected_artifact_name": name,
        "selected_member": str(f.relative_to(tmp / str(aid))),
        "artifact_checks": checks,
    }


def declaration_span(text: str) -> tuple[int, int, int, str]:
    ls = text.splitlines(keepends=True)
    start = None
    for i, line in enumerate(ls):
        m = DECL_RE.match(line)
        if m and m.group(1) == TARGET:
            start = i
            break
    if start is None:
        raise RuntimeError(f"target declaration {TARGET} not found")
    end = len(ls)
    for i in range(start + 1, len(ls)):
        if DECL_RE.match(ls[i]):
            end = i
            break
    block = "".join(ls[start:end])
    marker = block.find(":= by")
    marker_len = len(":= by")
    if marker < 0:
        marker = block.find(":=")
        marker_len = len(":=")
    if marker < 0:
        raise RuntimeError("target theorem body marker not found")
    prefix = block[: marker + marker_len]
    body_start = start + prefix.count("\n")
    return start, body_start, end, prefix


def same_height_replace(ls: list[str], start: int, end: int, replacement: list[str]) -> None:
    height = end - start
    normalized = [x if x.endswith("\n") else x + "\n" for x in replacement]
    if len(normalized) > height:
        raise RuntimeError("replacement exceeds available line height")
    normalized.extend(["\n"] * (height - len(normalized)))
    ls[start:end] = normalized


def locate_pre_slot(ls: list[str], theorem_start: int) -> tuple[int | None, int | None]:
    instance_line = None
    blank_line = None
    for i in range(max(0, theorem_start - 14), theorem_start):
        stripped = ls[i].strip()
        if (
            "AddCommGroup" in stripped
            and ("Complex" in stripped or "ℂ" in stripped)
            and (stripped.startswith("local instance") or stripped.startswith("instance"))
        ):
            instance_line = i
        elif stripped == "":
            blank_line = i
    return instance_line, blank_line


def locate_body_instance(ls: list[str], body_start: int, end: int) -> int | None:
    for i in range(body_start, min(end, body_start + 35)):
        if re.search(r"\bletI\s*:\s*AddCommGroup\s+(?:Complex|ℂ)", ls[i]):
            return i
    return None


def locate_hcomp_finish(ls: list[str], body_start: int, end: int) -> tuple[int, int] | None:
    positions = [i for i in range(body_start, end) if "hcomp" in ls[i]]
    if not positions:
        return None
    last = positions[-1]
    start = last
    while start > body_start:
        stripped = ls[start].lstrip()
        if stripped.startswith(("simpa", "exact", "convert", "refine", "show")):
            break
        start -= 1
    if not ls[start].lstrip().startswith(("simpa", "exact", "convert", "refine", "show")):
        return None
    return start, last + 1


def prepare_variant(baseline: str, variant: str) -> tuple[str, dict]:
    if variant not in VARIANTS:
        raise RuntimeError(f"unknown variant: {variant}")
    ls = baseline.splitlines(keepends=True)
    theorem_start, body_start, end, header = declaration_span(baseline)
    pre_instance, pre_blank = locate_pre_slot(ls, theorem_start)
    body_instance = locate_body_instance(ls, body_start, end)
    finish = locate_hcomp_finish(ls, body_start, end)

    pre_mode = "unchanged"
    body_mode = "unchanged"
    finish_mode = "unchanged"
    if variant.startswith("pre-normed"):
        pre_mode = "normed"
    elif variant.startswith("pre-complex"):
        pre_mode = "complex"
    elif variant.startswith("no-pre"):
        pre_mode = "none"

    if "body-remove" in variant or "-remove-" in variant or variant.startswith("no-pre-remove"):
        body_mode = "remove"
    elif "body-normed" in variant:
        body_mode = "normed"
    elif "body-complex" in variant:
        body_mode = "complex"
    elif "body-alias" in variant:
        body_mode = "alias"

    if variant.endswith("-exact"):
        finish_mode = "exact"
    elif variant.endswith("-simpa"):
        finish_mode = "simpa"
    elif variant.endswith("-convert"):
        finish_mode = "convert"

    if variant == "body-remove":
        body_mode = "remove"
    elif variant == "body-normed":
        body_mode = "normed"
    elif variant == "body-complex":
        body_mode = "complex"

    slot = pre_instance if pre_instance is not None else pre_blank
    if pre_mode != "unchanged":
        if slot is None:
            raise RuntimeError("no same-height pre-theorem slot available")
        if pre_mode == "normed":
            ls[slot] = (
                "local instance actualEdgeCanonicalComplexAddCommGroup : AddCommGroup Complex := "
                "Complex.instNormedAddCommGroup.toAddCommGroup\n"
            )
        elif pre_mode == "complex":
            ls[slot] = (
                "local instance actualEdgeCanonicalComplexAddCommGroup : AddCommGroup Complex := "
                "Complex.addCommGroup\n"
            )
        else:
            ls[slot] = "\n"

    if body_mode != "unchanged":
        if body_instance is None:
            # Use a blank proof-body line only when no proof-local instance exists.
            body_instance = next(
                (i for i in range(body_start, min(end, body_start + 12)) if ls[i].strip() == ""),
                None,
            )
        if body_instance is None:
            raise RuntimeError("no proof-body instance/blank slot available")
        if body_mode == "remove":
            ls[body_instance] = "\n"
        elif body_mode == "normed":
            ls[body_instance] = (
                "  letI : AddCommGroup Complex := "
                "Complex.instNormedAddCommGroup.toAddCommGroup\n"
            )
        elif body_mode == "complex":
            ls[body_instance] = "  letI : AddCommGroup Complex := Complex.addCommGroup\n"
        elif body_mode == "alias":
            if pre_mode == "unchanged" and pre_instance is None:
                raise RuntimeError("alias body requires a pre-theorem instance")
            ls[body_instance] = (
                "  letI : AddCommGroup Complex := actualEdgeCanonicalComplexAddCommGroup\n"
            )

    if finish_mode != "unchanged":
        if finish is None:
            raise RuntimeError("hcomp finishing command not found")
        f_start, f_end = finish
        if finish_mode == "exact":
            repl = ["  exact hcomp\n"]
        elif finish_mode == "simpa":
            repl = [
                "  simpa only [actualEdgeAmbientParam, actualEdgeNativeVelocity] using hcomp\n"
            ]
        else:
            repl = ["  convert hcomp using 1 <;> rfl\n"]
        same_height_replace(ls, f_start, f_end, repl)

    candidate = "".join(ls)
    c_start, c_body, c_end, c_header = declaration_span(candidate)
    if c_header != header:
        raise RuntimeError("theorem statement/header changed")
    if lines(candidate.encode()) != EXPECTED_LINES:
        raise RuntimeError("file height changed")
    metadata = {
        "variant": variant,
        "baseline_sha256": sha(baseline.encode()),
        "candidate_sha256": sha(candidate.encode()),
        "line_count": lines(candidate.encode()),
        "target_declaration": TARGET,
        "target_header_sha256": sha(header.encode()),
        "theorem_start_line": theorem_start + 1,
        "body_start_line": body_start + 1,
        "pre_mode": pre_mode,
        "body_mode": body_mode,
        "finish_mode": finish_mode,
        "pre_instance_line": None if pre_instance is None else pre_instance + 1,
        "pre_blank_line": None if pre_blank is None else pre_blank + 1,
        "body_instance_line": None if body_instance is None else body_instance + 1,
    }
    return candidate, metadata


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--variant", required=True, choices=sorted(VARIANTS))
    parser.add_argument("--output-dir", required=True)
    args = parser.parse_args()

    output = Path(args.output_dir)
    output.mkdir(parents=True, exist_ok=True)
    tmp = output / "artifact-downloads"
    tmp.mkdir(parents=True, exist_ok=True)
    baseline_data, provenance = recover_exact_source(tmp)
    baseline = baseline_data.decode("utf-8")
    candidate, metadata = prepare_variant(baseline, args.variant)
    SOURCE.write_text(candidate, encoding="utf-8")
    (output / "Mock2_FunctionalAnalysis-candidate.lean").write_text(
        candidate, encoding="utf-8"
    )
    (output / "Mock2_FunctionalAnalysis-baseline.lean").write_bytes(baseline_data)
    (output / "PROVENANCE.json").write_text(
        json.dumps(provenance, indent=2) + "\n", encoding="utf-8"
    )
    (output / "CANDIDATE.json").write_text(
        json.dumps(metadata, indent=2) + "\n", encoding="utf-8"
    )
    print(json.dumps({**metadata, "provenance": provenance}, indent=2))


if __name__ == "__main__":
    main()
