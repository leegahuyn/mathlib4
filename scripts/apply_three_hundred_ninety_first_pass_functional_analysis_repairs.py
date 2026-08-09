from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
import difflib
import hashlib
import json
import os
import re

ROOT = Path(__file__).resolve().parents[1]
BASE_PATH = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
DONOR_PATH = Path(os.environ["PASS376_DONOR"])
PATCH_PATH = Path(os.environ.get("PASS391_PATCH_OUT", "/tmp/pass391.patch"))
META_PATH = Path(os.environ.get("PASS391_META_OUT", "/tmp/pass391-meta.json"))
START = "private theorem denseRange_energyCompletionMap_of_denseRange"
END = "/-- The Mobius-composed actual edge has the declared native tangent. -/"
EXPECTED_BASE_SHA256 = "10c95422f6e57fb0ec21f8307f5ca97636997bb111e9347beb7ac5fb58b2d196"
EXPECTED_DONOR_SHA256 = "07f6efd3309c3cc23b86adf5811918b752b72c33a3f7a76213ce9beb10796da4"
EXPECTED_OUTPUT_SHA256 = "58e503b0d8bc304fda07fc9b4fe3056bf43cd6df089bc8a27ab34712696e64e0"


@dataclass
class Decl:
    kind: str
    name: str
    ns: tuple[str, ...]
    start: int
    header_end: int
    end: int
    text: str
    header: str
    body: str

    @property
    def key(self) -> tuple[tuple[str, ...], str, str]:
        return self.ns, self.kind, self.name


DECL_PATTERN = (
    r"(?P<lead>(?:(?:private|noncomputable|protected)\s+)*)"
    r"(?P<kind>instance|def|abbrev|theorem|lemma|opaque)\s+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_'\.]*)"
    r"(?=\s*(?:\(|\{|\[|:|:=))"
)
EVENT_RE = re.compile(
    r"(?m)^(?:"
    r"(?P<namespace>namespace)\s+(?P<nsname>[A-Za-z_][A-Za-z0-9_'\.]*)|"
    r"(?P<section>section)(?:\s+(?P<secname>[A-Za-z_][A-Za-z0-9_']*))?|"
    r"(?P<end>end)(?:\s+[A-Za-z_][A-Za-z0-9_'\.]*)?|"
    + DECL_PATTERN
    + r")"
)
BOUNDARY_RE = re.compile(
    r"(?m)^(?=(?:(?:private|noncomputable|protected)\s+)*"
    r"(?:instance|def|abbrev|theorem|lemma|opaque)\s+[A-Za-z_]|"
    r"namespace\b|section\b|end\b|variable\b|include\b|omit\b|open\b|"
    r"attribute\b|local\b|scoped\b|#(?:check|synth|print|eval)\b|/--|/-!)"
)


def mask_comments_strings(src: str) -> str:
    out = list(src)
    i = 0
    depth = 0
    string = False
    esc = False
    line = False
    while i < len(src):
        if line:
            if src[i] == "\n":
                line = False
            else:
                out[i] = " "
            i += 1
        elif depth:
            if src.startswith("/-", i):
                out[i] = out[i + 1] = " "
                depth += 1
                i += 2
            elif src.startswith("-/", i):
                out[i] = out[i + 1] = " "
                depth -= 1
                i += 2
            else:
                if src[i] != "\n":
                    out[i] = " "
                i += 1
        elif string:
            c = src[i]
            if c != "\n":
                out[i] = " "
            if esc:
                esc = False
            elif c == "\\":
                esc = True
            elif c == '"':
                string = False
            i += 1
        elif src.startswith("/-", i):
            out[i] = out[i + 1] = " "
            depth = 1
            i += 2
        elif src.startswith("--", i):
            out[i] = out[i + 1] = " "
            line = True
            i += 2
        elif src[i] == '"':
            out[i] = " "
            string = True
            i += 1
        else:
            i += 1
    if depth or string:
        raise RuntimeError("unterminated comment or string")
    return "".join(out)


def body_marker(block: str) -> int:
    masked = mask_comments_strings(block)
    candidates: list[int] = []
    z = masked.find(":=")
    if z >= 0:
        candidates.append(z)
    for pat in (
        r"(?m)^where\b",
        r"(?m)^by\s*$",
        r"(?m)^\s*where\b",
        r"(?m)^\s*by\s*$",
        r"(?m)^\s*\|",
    ):
        match = re.search(pat, masked)
        if match:
            candidates.append(match.start())
    if not candidates:
        raise RuntimeError("no body marker for " + block[:160].replace("\n", " "))
    return min(candidates)


def parse_region(text: str) -> list[Decl]:
    masked = mask_comments_strings(text)
    frames: list[tuple[str, str | None]] = []
    ns_at: dict[int, tuple[str, ...]] = {}
    decl_matches = []
    for match in EVENT_RE.finditer(masked):
        if match.group("namespace"):
            frames.append(("namespace", match.group("nsname")))
        elif match.group("section"):
            frames.append(("section", match.group("secname")))
        elif match.group("end"):
            if frames:
                frames.pop()
        elif match.group("kind"):
            ns_at[match.start()] = tuple(
                name for typ, name in frames if typ == "namespace" and name
            )
            decl_matches.append(match)
    out: list[Decl] = []
    starts = [match.start() for match in decl_matches]
    for i, match in enumerate(decl_matches):
        next_decl = starts[i + 1] if i + 1 < len(starts) else len(text)
        boundary = BOUNDARY_RE.search(masked, match.end(), next_decl)
        end = boundary.start() if boundary else next_decl
        block = text[match.start() : end]
        header_len = body_marker(block)
        out.append(
            Decl(
                match.group("kind"),
                match.group("name"),
                ns_at[match.start()],
                match.start(),
                match.start() + header_len,
                end,
                block,
                block[:header_len],
                block[header_len:],
            )
        )
    return out


def norm_header(header: str) -> str:
    return " ".join(header.split())


def main() -> int:
    base = BASE_PATH.read_text(encoding="utf-8")
    donor = DONOR_PATH.read_text(encoding="utf-8")
    base_hash = hashlib.sha256(base.encode()).hexdigest()
    donor_hash = hashlib.sha256(donor.encode()).hexdigest()
    print(f"input_sha256={base_hash}")
    print(f"donor_sha256={donor_hash}")
    if base_hash == EXPECTED_OUTPUT_SHA256:
        print("[pass391] already applied")
        return 0
    if base_hash != EXPECTED_BASE_SHA256:
        raise RuntimeError(f"unexpected PASS391 input: {base_hash}")
    if donor_hash != EXPECTED_DONOR_SHA256:
        raise RuntimeError(f"unexpected PASS376 donor: {donor_hash}")

    base_start = base.index(START)
    base_end = base.index(END, base_start)
    donor_start = donor.index(START)
    donor_end = donor.index(END, donor_start)
    base_region = base[base_start:base_end]
    donor_region = donor[donor_start:donor_end]
    base_decls = parse_region(base_region)
    donor_decls = parse_region(donor_region)
    base_keys = [decl.key for decl in base_decls]
    donor_keys = [decl.key for decl in donor_decls]

    matcher = difflib.SequenceMatcher(a=base_keys, b=donor_keys, autojunk=False)
    matched: dict[int, int] = {}
    base_only: list[int] = []
    donor_only: list[int] = []
    for tag, i1, i2, j1, j2 in matcher.get_opcodes():
        if tag == "equal":
            for base_i, donor_i in zip(range(i1, i2), range(j1, j2)):
                matched[donor_i] = base_i
        elif tag in ("delete", "replace"):
            base_only.extend(range(i1, i2))
        if tag in ("insert", "replace"):
            donor_only.extend(range(j1, j2))

    merged = donor_region
    for donor_i, base_i in sorted(
        matched.items(), key=lambda item: donor_decls[item[0]].start, reverse=True
    ):
        donor_decl = donor_decls[donor_i]
        base_decl = base_decls[base_i]
        merged = (
            merged[: donor_decl.start]
            + base_decl.header
            + merged[donor_decl.header_end :]
        )

    for base_i in sorted(base_only, reverse=True):
        base_decl = base_decls[base_i]
        next_key = None
        for k in range(base_i + 1, len(base_decls)):
            if base_decls[k].key in donor_keys:
                next_key = base_decls[k].key
                break
        block = "\n" + base_decl.text.rstrip() + "\n\n"
        current = parse_region(merged)
        if next_key is None:
            merged += block
        else:
            matches = [decl for decl in current if decl.key == next_key]
            if len(matches) != 1:
                raise RuntimeError(
                    f"cannot place {base_decl.key}; next {next_key} count={len(matches)}"
                )
            pos = matches[0].start
            merged = merged[:pos] + block + merged[pos:]

    candidate = base[:base_start] + merged + base[base_end:]
    patch = "".join(
        difflib.unified_diff(
            base.splitlines(True),
            candidate.splitlines(True),
            fromfile="a/PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean",
            tofile="b/PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean",
        )
    )
    new_decls = parse_region(candidate[base_start : candidate.index(END, base_start)])
    new_i = 0
    changed = []
    missing = []
    for base_decl in base_decls:
        while new_i < len(new_decls) and new_decls[new_i].key != base_decl.key:
            new_i += 1
        if new_i == len(new_decls):
            missing.append(base_decl.key)
            continue
        if norm_header(new_decls[new_i].header) != norm_header(base_decl.header):
            changed.append(
                (base_decl.key, norm_header(base_decl.header), norm_header(new_decls[new_i].header))
            )
        new_i += 1

    output_hash = hashlib.sha256(candidate.encode()).hexdigest()
    if output_hash != EXPECTED_OUTPUT_SHA256:
        raise RuntimeError(f"unexpected PASS391 output: {output_hash}")
    meta = {
        "base_sha256": base_hash,
        "donor_sha256": donor_hash,
        "output_sha256": output_hash,
        "base_decls": len(base_decls),
        "donor_decls": len(donor_decls),
        "merged_decls": len(new_decls),
        "base_only": [base_decls[i].key for i in base_only],
        "donor_only": [donor_decls[i].key for i in donor_only],
        "missing": missing,
        "changed_header_count": len(changed),
        "patch_bytes": len(patch.encode()),
    }
    print(json.dumps(meta, indent=2, default=list))
    if missing or changed:
        raise RuntimeError(f"header preservation failed: missing={missing}, changed={changed[:20]}")
    PATCH_PATH.write_text(patch, encoding="utf-8")
    META_PATH.write_text(json.dumps(meta, indent=2, default=list) + "\n", encoding="utf-8")
    BASE_PATH.write_text(candidate, encoding="utf-8")
    print("[pass391] header-preserving donor merge applied")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
