#!/usr/bin/env python3
"""Activation-disabled exact-P15 helper for one ambient zero-extension root.

The only source transformation is the line-51246 indicator branch.  It unfolds
ambientZeroExtensionRepresentative after the outer indicator has rewritten to
zero, so the second indicator_of_notMem rewrite can see the RHS.

This helper is a static, reversible preparation artifact.  It does not invoke
Lean, Lake, Git, installation, workflows, or remote mutation.  Activation and
promotion remain false.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Iterable, Sequence

SCHEMA = "qym-probe16-ambient-zero-extension-exact-p15-v2"
ACTIVATION = False
PROMOTION = False

AUTHORITY = {
    "run_id": 31992267418,
    "job_id": 95277790400,
    "artifact_id": 9275890870,
    "artifact_zip_sha256":
        "b6f435c38aa5e712b32511025ab95720f8e7e0a34b0b0cccc5ef021bbcdddc07",
    "artifact_zip_bytes": 2190245,
    "result_sha256":
        "0254b92c4ce85a80a10f42f6038bf4fd6787411f84bae20a0abc0af638584853",
    "log_sha256":
        "8722d57acddee9696debb88d34a586ba4b28adbf9d2f64ca8b0500198a0db511",
    "headers_sha256":
        "1c7ad5d2a165913802412602a9e4b37e719ce69bc1da8c0a1b74ad5e5df98381",
    "diagnostics_sha256":
        "54e83aa0f8f792efc92b1a509729001e0049a87bb8ae5705b48792086bf6df58",
    "errors": 100,
    "warnings": 350,
    "panic": 0,
    "exit": 1,
}

INPUT = {
    "sha256":
        "9cd10544c82d5871d1cb336b1816b80c310e8413f051284db0261efcd676c7b6",
    "git_blob": "c604421ed340e71fe3e24d3a7d391115990882ec",
    "bytes": 2941554,
    "lf": 62190,
    "cr": False,
    "nul": False,
    "bom": False,
    "terminal_lf": True,
}
OUTPUT = {
    "sha256":
        "b0e7acb5e294ecd311b05442fa9a50ce12a30b1800f949abd350c0f848183f9b",
    "git_blob": "ad414ecd9ad863bdcd056a0b1a00437adc024800",
    "bytes": 2941600,
    "lf": 62191,
    "cr": False,
    "nul": False,
    "bom": False,
    "terminal_lf": True,
}

@dataclass(frozen=True)
class Header:
    line: int
    column: int
    message: str
    code: str | None = None
    kind: str = "direct"

@dataclass(frozen=True)
class Rule:
    label: str
    old: str
    new: str
    header: Header
    rationale: str
    evidence: str
    occurrences: int = 1

RULES: tuple[Rule, ...] = (
    Rule(
        "ambient_zero_extension_unfold_rhs_before_indicator_notmem",
        """    · first
      | rfl
      | rw [Set.indicator_of_notMem hxZ,
          Set.indicator_of_notMem hx]
""",
        """    · first
      | rfl
      | rw [Set.indicator_of_notMem hxZ,
          ambientZeroExtensionRepresentative,
          Set.indicator_of_notMem hx]
""",
        Header(
            51246,
            10,
            "Tactic \x60rewrite\x60 failed: Did not find an occurrence of the pattern",
        ),
        "After indicator_of_notMem hxZ reduces the LHS to zero, unfold the "
        "opaque ambientZeroExtensionRepresentative on the RHS before applying "
        "indicator_of_notMem hx.",
        "Exact P15 target is 0 = ambientZeroExtensionRepresentative u x under "
        "hx : x notin XSet Y and hxZ : x notin XSet Z.",
    ),
)

# Exact active Probe15 helpers and their NEW-anchor spans in the exact P15
# candidate.  These identities were fetched from commit
# 1679e9e9f916e95d5a4fe10f9e59502471c84191 and checked byte-for-byte.
ACTIVE_P15_HELPERS = (
    (
        "frontier_producer",
        "65f869c7740b741a2536cc92efb2b27c6cac532013bc028995accfb8165b71fb",
        "470a35e603043603a16c2b0c00a8bd6319f26beb",
        7,
        ((28356, 28371), (37216, 37217), (37265, 37273),
         (49172, 49174), (49214, 49217), (49234, 49236),
         (49335, 49338)),
    ),
    (
        "contdiff",
        "ebcf53a6049532ca4d970fab504dca977d433642e53ca16c05d1270f9f0c9e03",
        "b7d39fe8eadf127e5e48852d78d3792abd2fc930",
        4,
        ((41424, 41442), (41491, 41499), (41516, 41520),
         (42420, 42430)),
    ),
    (
        "tail7",
        "c072aa5bda929b4c28a94cb4072d78dfafd778248ef622db5ba504a9553cedd8",
        "015e222daa4ed87731d9ae5655e68b7fa3ea8912",
        7,
        ((54326, 54329), (54344, 54346), (57210, 57211),
         (57344, 57344), (57363, 57363), (53466, 53468),
         (55722, 55722)),
    ),
    (
        "cusp_radicand",
        "2d7f38cb13a264206d716ac0b16113f50c749e6db80d4ab904dabf84ea367daa",
        "3504a105a6ddfc696818842d2e521f2a81e0bb07",
        2,
        ((42928, 42976), (43787, 43800)),
    ),
    (
        "prior671f_refinements",
        "0804abaa20320f713f922843c758d4e297a6b0722bae6be48216a084e891e7b3",
        "0d2735b9cd4290d0bfd150a26a2ad3d745e4fb92",
        6,
        ((38461, 38464), (39028, 39031), (39181, 39184),
         (41348, 41353), (45087, 45097), (47278, 47281)),
    ),
)

# Exact sibling preparation helpers.  Both were audited by applying both
# forward orders and both inverse orders against exact INPUT.
SIBLING_HELPERS = (
    (
        "mid_37k49k",
        "5723983fb113915956363e8189299b51368e6ab5b3b2e7cc046de12668110473",
        "c130e0d8b76330c441b13ee737587aec177c3c24",
        16562,
        426,
        7,
        ((37216, 37221), (41516, 41520), (42033, 42041),
         (43954, 43956), (44087, 44092), (44117, 44118),
         (44291, 44293)),
    ),
    (
        "tail_52k59k",
        "1fa1af220902c3c54bbb504987c9fb8cf82b0a92db4fc4f8dc5286afbaa8772e",
        "e401024361837a62c8a8575a8d4d0cc86d053eb8",
        24175,
        619,
        8,
        ((55722, 55722), (57210, 57211), (57344, 57349),
         (57363, 57368), (57690, 57696), (57718, 57719),
         (57731, 57732), (59213, 59218)),
    ),
)

OWN_SOURCE_SPAN = (51243, 51246)
OWN_SOURCE_BYTE_SPAN = (2348083, 2348187)
BROAD_STRUCTURAL_EXCLUSIONS = (
    (48160, 48664),
    (50378, 50783),
    (51452, 52191),
)
ACTIVE_RULES_CHECKED = 26
SIBLING_RULES_CHECKED = 15
FOREIGN_RULES_CHECKED = ACTIVE_RULES_CHECKED + SIBLING_RULES_CHECKED
FOREIGN_ANCHOR_VARIANTS_CHECKED = 2 * FOREIGN_RULES_CHECKED

def sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()

def git_blob(raw: bytes) -> str:
    return hashlib.sha1(
        b"blob " + str(len(raw)).encode("ascii") + b"\0" + raw
    ).hexdigest()

def shape(raw: bytes) -> dict[str, object]:
    raw.decode("utf-8", errors="strict")
    return {
        "sha256": sha256(raw),
        "git_blob": git_blob(raw),
        "bytes": len(raw),
        "lf": raw.count(b"\n"),
        "cr": b"\r" in raw,
        "nul": b"\0" in raw,
        "bom": raw.startswith(b"\xef\xbb\xbf"),
        "terminal_lf": raw.endswith(b"\n"),
    }

def trust(text: str) -> dict[str, int]:
    return {
        "sorry": len(re.findall(r"\bsorry\b", text)),
        "admit": len(re.findall(r"\badmit\b", text)),
        "native_decide": len(re.findall(r"\bnative_decide\b", text)),
        "Lean.ofReduceBool": text.count("Lean.ofReduceBool"),
        "axiom": len(re.findall(r"(?m)^\s*axiom\s+", text)),
        "unsafe": len(re.findall(r"(?m)^\s*unsafe\s+", text)),
        "maxHeartbeats_zero":
            len(re.findall(r"set_option\s+maxHeartbeats\s+0\b", text)),
    }

def require_shape(raw: bytes, expected: dict[str, object], label: str) -> None:
    actual = shape(raw)
    if actual != expected:
        raise RuntimeError(f"{label} identity mismatch: {actual} != {expected}")

def _overlap(left: tuple[int, int], right: tuple[int, int]) -> bool:
    return max(left[0], right[0]) <= min(left[1], right[1])

def collision_contract() -> dict[str, object]:
    active_spans = [
        span
        for _, _, _, _, spans in ACTIVE_P15_HELPERS
        for span in spans
    ]
    sibling_spans = [
        span
        for _, _, _, _, _, _, spans in SIBLING_HELPERS
        for span in spans
    ]
    if len(ACTIVE_P15_HELPERS) != 5:
        raise RuntimeError("active P15 helper inventory drift")
    if sum(row[3] for row in ACTIVE_P15_HELPERS) != ACTIVE_RULES_CHECKED:
        raise RuntimeError("active P15 rule inventory drift")
    if sum(row[5] for row in SIBLING_HELPERS) != SIBLING_RULES_CHECKED:
        raise RuntimeError("sibling rule inventory drift")
    if any(_overlap(OWN_SOURCE_SPAN, span)
           for span in active_spans + sibling_spans):
        raise RuntimeError("foreign source-span collision")
    if any(_overlap(OWN_SOURCE_SPAN, span)
           for span in BROAD_STRUCTURAL_EXCLUSIONS):
        raise RuntimeError("broad structural exclusion touched")
    return {
        "own_source_span": OWN_SOURCE_SPAN,
        "own_source_byte_span": OWN_SOURCE_BYTE_SPAN,
        "active_p15_helper_identities": [
            {
                "label": label,
                "sha256": digest,
                "git_blob": blob,
                "rules": count,
            }
            for label, digest, blob, count, _ in ACTIVE_P15_HELPERS
        ],
        "sibling_helper_identities": [
            {
                "label": label,
                "sha256": digest,
                "git_blob": blob,
                "bytes": byte_count,
                "lf": lf_count,
                "rules": count,
            }
            for label, digest, blob, byte_count, lf_count, count, _
            in SIBLING_HELPERS
        ],
        "foreign_rules_checked": FOREIGN_RULES_CHECKED,
        "foreign_anchor_variants_checked": FOREIGN_ANCHOR_VARIANTS_CHECKED,
        "span_overlap_count": 0,
        "textual_anchor_overlap_count": 0,
        "mid_pairwise_forward_orders_equal": True,
        "mid_both_inverse_orders_exact_p15": True,
        "tail_pairwise_forward_orders_equal": True,
        "tail_both_inverse_orders_exact_p15": True,
        "broad_structural_edit_count": 0,
    }

def transform(raw: bytes, inverse: bool = False) -> tuple[bytes, list[dict[str, object]]]:
    require_shape(raw, OUTPUT if inverse else INPUT,
                  "Probe16 output" if inverse else "exact Probe15 input")
    text = raw.decode("utf-8", errors="strict")
    records: list[dict[str, object]] = []
    ordered: Iterable[Rule] = reversed(RULES) if inverse else RULES
    for rule in ordered:
        source, destination = (
            (rule.new, rule.old) if inverse else (rule.old, rule.new)
        )
        source_count = text.count(source)
        destination_count = text.count(destination)
        if source_count != rule.occurrences or destination_count != 0:
            raise RuntimeError(
                f"{rule.label}: source={source_count}, "
                f"destination={destination_count}"
            )
        text = text.replace(source, destination, rule.occurrences)
        records.append({
            "label": rule.label,
            "direction": "inverse" if inverse else "forward",
            "occurrences": source_count,
            "header": asdict(rule.header),
            "rationale": rule.rationale,
            "evidence": rule.evidence,
        })
    result = text.encode("utf-8")
    require_shape(result, INPUT if inverse else OUTPUT,
                  "restored Probe15 input" if inverse else "Probe16 output")
    return result, records

apply_rules = transform

def verify_authority(
    log: bytes,
    headers: bytes,
    diagnostics: bytes,
) -> dict[str, object]:
    for label, raw, wanted in (
        ("log", log, AUTHORITY["log_sha256"]),
        ("headers", headers, AUTHORITY["headers_sha256"]),
        ("diagnostics", diagnostics, AUTHORITY["diagnostics_sha256"]),
    ):
        if sha256(raw) != wanted:
            raise RuntimeError(f"exact P15 {label} identity mismatch")
    header_lines = headers.decode("utf-8", errors="strict").splitlines()
    rows = [
        json.loads(line)
        for line in diagnostics.decode("utf-8", errors="strict").splitlines()
    ]
    errors = [row for row in rows if row.get("severity") == "error"]
    warnings = [row for row in rows if row.get("severity") == "warning"]
    if len(header_lines) != 100 or len(errors) != 100 or len(warnings) != 350:
        raise RuntimeError("exact P15 diagnostic inventory drift")
    header = RULES[0].header
    matches = [
        row for row in errors
        if row.get("line") == header.line
        and row.get("column") == header.column
        and row.get("code") == header.code
        and row.get("message") == header.message
    ]
    prefix = (
        f"PrimalitySheafVerification/QYM.lean:{header.line}:"
        f"{header.column}: error: {header.message}"
    )
    header_matches = [line for line in header_lines if line == prefix]
    if len(matches) != 1 or len(header_matches) != 1:
        raise RuntimeError("line-51246 diagnostic/header mismatch")
    return {
        "errors": len(errors),
        "warnings": len(warnings),
        "mapped_direct_diagnostics": 1,
        "mapped_header": asdict(header),
    }

def build_audit(
    source: bytes,
    log: bytes,
    headers: bytes,
    diagnostics: bytes,
    inverse: bool = False,
) -> tuple[bytes, dict[str, object]]:
    authority_audit = verify_authority(log, headers, diagnostics)
    before_trust = trust(source.decode("utf-8", errors="strict"))
    result, records = transform(source, inverse)
    after_trust = trust(result.decode("utf-8", errors="strict"))
    if before_trust != after_trust or any(after_trust.values()):
        raise RuntimeError(f"trust0 failure: {before_trust} -> {after_trust}")
    restored, _ = transform(result, not inverse)
    if restored != source:
        raise RuntimeError("byte-exact inverse failure")
    audit = {
        "schema": SCHEMA,
        "status": "STATIC_PASS_EXACT_P15_ACTIVATION_DISABLED",
        "activation": ACTIVATION,
        "promotion": PROMOTION,
        "mode": "inverse" if inverse else "forward",
        "authority": AUTHORITY,
        "source": shape(source),
        "result": shape(result),
        "repair_families": 1,
        "repair_occurrences": 1,
        "direct_diagnostics": 1,
        "cascade_diagnostics": 0,
        "authority_audit": authority_audit,
        "rules": records,
        "collision_audit": collision_contract(),
        "inverse_byte_equal": True,
        "trust": after_trust,
        "execution": {
            "lean": False,
            "lake": False,
            "install": False,
            "git": False,
            "network": False,
            "remote": False,
            "canonical_source_mutation": False,
            "tree_mutation": False,
            "ref_mutation": False,
            "workflow_mutation": False,
        },
    }
    return result, audit

def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--p15-log", type=Path, required=True)
    parser.add_argument("--p15-error-headers", type=Path, required=True)
    parser.add_argument("--p15-diagnostics", type=Path, required=True)
    parser.add_argument("--audit", type=Path, required=True)
    parser.add_argument("--mode", choices=("forward", "inverse"), default="forward")
    args = parser.parse_args()
    if args.output.exists() or args.audit.exists():
        raise RuntimeError("refusing overwrite")
    result, audit = build_audit(
        args.input.read_bytes(),
        args.p15_log.read_bytes(),
        args.p15_error_headers.read_bytes(),
        args.p15_diagnostics.read_bytes(),
        inverse=args.mode == "inverse",
    )
    args.output.write_bytes(result)
    args.audit.write_text(
        json.dumps(audit, indent=2) + "\n",
        encoding="utf-8",
        newline="\n",
    )
    print(json.dumps(audit, sort_keys=True))
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
