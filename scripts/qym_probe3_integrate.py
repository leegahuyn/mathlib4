#!/usr/bin/env python3
"""Compose the exact, reversible QYM probe-3 repair package.

The order is deliberate: the position-sensitive late pass runs first, followed
by one weighted-Hermitian proof repair, the early text pass, the mid P0 pass,
the run-2-confirmed P1/additional hunks, and finally the 47 pure forwarding
aliases.  The aliases use ``abbrev`` because rc1 resolves theorem header holes
before seeing a proof RHS and therefore rejects the previously proposed ``: _``.
No Lean, Lake, Git, or network process is invoked.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import re
import sys
from pathlib import Path
from types import ModuleType
from typing import Iterable


SCHEMA = "qym-probe3-integrated-transform-v1"
EXPECTED_INPUT_SHA256 = (
    "64f045b04dc39e157ba609047e6ac9a0851962b7c74024af9987dbcbd46f19d1"
)
EXPECTED_INPUT_GIT_BLOB = "5031023859a5cac44aaaf1760564c1e560ede13b"
EXPECTED_INPUT_BYTES = 2_906_438
EXPECTED_INPUT_LF = 61_580

# Filled only after the composed transform has been independently materialized.
EXPECTED_OUTPUT_SHA256 = (
    "9e82073bdaf6339feb1ca09d70ab371947c6e07294ae01895a33c75f978bd780"
)
EXPECTED_OUTPUT_GIT_BLOB = "652a6b11899db967ec19c2f32ca7aa1ad2044c7a"
EXPECTED_OUTPUT_BYTES = 2_906_639
EXPECTED_OUTPUT_LF = 61_479

HELPER_SHA256 = {
    "late": "381b0442490c98ce3c03fa618ea84b4954d1e655aba981d13b674c0bd7be30fe",
    "early": "a0c39dc2c26ee7f40faf7b7c93f99e18f6284cdc21e462483171d66b215b060a",
    "mid_p0": "85be64d86f0f1526e79c10cc3e6179b4352c3e5335f69be13a62beafbdb83862",
    "mid_confirmed_patch": "624b537b94536936f981e6eb09cc56f101c14a6a15f44830805c02cb0059140b",
    "forwarder_inventory": "3d39b45d2d5908ab1f3d7b8e041ef0f11f3dc1b9e1780996b737d73b55bcf6e5",
}

# These five patch hunks are already owned by the earlier exact-five pass.
# Skipping them here is what makes the composition collision-free while still
# activating every run-2-confirmed conceptual repair in the patch.
DELEGATED_PATCH_HUNKS = frozenset({11612, 11636, 11794, 11810, 11978})
PATCH_ATOMIC_OCCURRENCES = {
    11612: 1, 11636: 1, 11794: 1, 11810: 1, 11978: 1,
    12265: 1, 12275: 1, 14757: 1, 15104: 1, 15600: 1,
    17640: 2, 17729: 1, 17851: 1, 19138: 1, 19321: 2,
    19332: 1, 19672: 1, 19987: 2, 20020: 1, 20030: 1, 20046: 1,
}

RUN2_MID_HEADER_LINES = (
    11618, 11639, 11797, 11813, 11982, 12269, 12279, 14761,
    15107, 15603, 17643, 17650, 17733, 17855, 19141, 19324,
    19327, 19335, 19675, 19990, 20024, 20033, 20047,
)

WEIGHTED_OLD = (
    "theorem weightedHermitianPairing_conj_symm (X Y : Mat2) :\n"
    "    weightedHermitianPairing X Y = star (weightedHermitianPairing Y X) := by\n"
    "  rw [weightedHermitianPairing_formula, weightedHermitianPairing_formula]\n"
    "  simp only [star_add, star_mul, map_ofNat, star_star]\n"
    "  ring\n"
)
WEIGHTED_NEW = (
    "theorem weightedHermitianPairing_conj_symm (X Y : Mat2) :\n"
    "    weightedHermitianPairing X Y = star (weightedHermitianPairing Y X) := by\n"
    "  have hstar_two : star (2 : ℂ) = 2 := by\n"
    "    norm_num [Complex.star_def]\n"
    "  rw [weightedHermitianPairing_formula, weightedHermitianPairing_formula]\n"
    "  simp only [star_add, star_mul, hstar_two, star_star]\n"
    "  ring\n"
)

TRUST_PATTERNS = {
    "sorry": re.compile(r"(?<![\w.])sorry(?![\w])"),
    "admit": re.compile(r"(?<![\w.])admit(?![\w])"),
    "native_decide": re.compile(r"(?<![\w.])native_decide(?![\w])"),
    "Lean.ofReduceBool": re.compile(r"(?<![\w.])Lean\.ofReduceBool(?![\w])"),
    "axiom_declaration": re.compile(r"^[ \t]*axiom\b", re.MULTILINE),
    "maxHeartbeats_zero": re.compile(
        r"^[ \t]*set_option[ \t]+maxHeartbeats[ \t]+0\b", re.MULTILINE
    ),
}


def sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def git_blob(raw: bytes) -> str:
    return hashlib.sha1(f"blob {len(raw)}\0".encode("ascii") + raw).hexdigest()


def hygiene(raw: bytes, label: str) -> dict[str, object]:
    if raw.startswith(b"\xef\xbb\xbf"):
        raise AssertionError(f"{label}: UTF-8 BOM forbidden")
    if b"\r" in raw or b"\x00" in raw:
        raise AssertionError(f"{label}: CR/NUL forbidden")
    if not raw.endswith(b"\n"):
        raise AssertionError(f"{label}: terminal LF required")
    raw.decode("utf-8", errors="strict")
    return {
        "sha256": sha256(raw), "git_blob": git_blob(raw),
        "bytes": len(raw), "lf": raw.count(b"\n"),
        "utf8": True, "bom": False, "cr": False, "nul": False,
        "terminal_lf": True,
    }


def trust_counts(text: str) -> dict[str, int]:
    return {name: len(pattern.findall(text)) for name, pattern in TRUST_PATTERNS.items()}


def load_exact_module(path: Path, expected_sha: str, name: str) -> ModuleType:
    raw = path.read_bytes()
    if sha256(raw) != expected_sha:
        raise AssertionError(f"{name}: helper SHA-256 mismatch")
    spec = importlib.util.spec_from_file_location(f"qym_probe3_{name}", path)
    if spec is None or spec.loader is None:
        raise AssertionError(f"{name}: cannot create import spec")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def exact_replace(text: str, old: str, new: str, label: str) -> str:
    if text.count(old) != 1 or text.count(new) != 0:
        raise AssertionError(
            f"{label}: expected one old and zero new; found "
            f"{text.count(old)} old/{text.count(new)} new"
        )
    return text.replace(old, new)


def parse_confirmed_patch(raw: bytes) -> list[dict[str, object]]:
    text = raw.decode("utf-8", errors="strict")
    lines = text.splitlines(keepends=True)
    hunks: list[dict[str, object]] = []
    i = 0
    header_re = re.compile(r"^@@ -(\d+),")
    while i < len(lines):
        match = header_re.match(lines[i])
        if match is None:
            i += 1
            continue
        source_line = int(match.group(1))
        i += 1
        old: list[str] = []
        new: list[str] = []
        while i < len(lines) and not lines[i].startswith("@@ "):
            line = lines[i]
            if line.startswith(" "):
                old.append(line[1:])
                new.append(line[1:])
            elif line.startswith("-") and not line.startswith("---"):
                old.append(line[1:])
            elif line.startswith("+") and not line.startswith("+++"):
                new.append(line[1:])
            i += 1
        hunks.append({"source_line": source_line, "old": "".join(old), "new": "".join(new)})
    if tuple(int(h["source_line"]) for h in hunks) != tuple(PATCH_ATOMIC_OCCURRENCES):
        raise AssertionError("confirmed patch hunk inventory/order drift")
    return hunks


def apply_confirmed_patch(
    text: str, hunks: Iterable[dict[str, object]], *, inverse: bool
) -> tuple[str, list[dict[str, object]]]:
    rows = list(hunks)
    if inverse:
        rows.reverse()
    audit: list[dict[str, object]] = []
    for hunk in rows:
        line = int(hunk["source_line"])
        if line in DELEGATED_PATCH_HUNKS:
            continue
        old = str(hunk["new"] if inverse else hunk["old"])
        new = str(hunk["old"] if inverse else hunk["new"])
        direction = "inverse" if inverse else "forward"
        if text.count(old) != 1:
            raise AssertionError(
                f"patch_{line}/{direction}: expected one exact source hunk; "
                f"found {text.count(old)} old/{text.count(new)} new"
            )
        text = text.replace(old, new, 1)
        audit.append({
            "source_line": line,
            "atomic_occurrences": PATCH_ATOMIC_OCCURRENCES[line],
            "direction": direction,
        })
    return text, audit


def forwarders(
    text: str, inventory: dict[str, object], *, inverse: bool
) -> tuple[str, list[dict[str, object]]]:
    entries = inventory.get("entries")
    if inventory.get("count") != 47 or not isinstance(entries, list) or len(entries) != 47:
        raise AssertionError("forwarder inventory schema/count drift")
    rows = list(entries)
    if inverse:
        rows.reverse()
    audit: list[dict[str, object]] = []
    for entry in rows:
        name = str(entry["name"])
        source_kind = "abbrev" if inverse else "theorem"
        matches = list(
            re.finditer(rf"(?m)^{source_kind} {re.escape(name)}\b", text)
        )
        if not matches:
            raise AssertionError(f"forwarder theorem missing: {name}")
        # The aliases are the last declaration for the two duplicate names.
        start = matches[-1].start()
        old = f"abbrev {name}" if inverse else f"theorem {name}"
        new = f"theorem {name}" if inverse else f"abbrev {name}"
        terminator = text.find(":=", matches[-1].end())
        header = text[start:terminator + 2] if terminator >= 0 else ""
        if header.count(old) != 1 or header.count(new) != 0 or header.count(":=") != 1:
            raise AssertionError(
                f"forwarder {name}: expected one {old!r} and zero {new!r}; "
                f"found {header.count(old)}/{header.count(new)}"
            )
        text = text[:start] + new + text[start + len(old):]
        audit.append({"name": name, "direction": "inverse" if inverse else "forward"})
    return text, audit


def forward(
    raw: bytes, late: ModuleType, early: ModuleType, mid: ModuleType,
    patch_hunks: list[dict[str, object]], inventory: dict[str, object],
) -> tuple[bytes, dict[str, object]]:
    stages: list[dict[str, object]] = []
    late_raw = late._forward(raw)
    stages.append({"stage": "late_static", **hygiene(late_raw, "late")})
    text = late_raw.decode("utf-8")

    text = exact_replace(text, WEIGHTED_OLD, WEIGHTED_NEW, "weighted_hstar_two")
    stages.append({"stage": "weighted_hstar_two", **hygiene(text.encode(), "weighted")})

    early_audit: list[dict[str, object]] = []
    for repair in early.REPAIRS:
        text, entry = early.exact_replace(text, repair)
        early_audit.append(entry)
    stages.append({"stage": "early_exact_five", **hygiene(text.encode(), "early")})

    text, p0_audit = mid.transform(text, inverse=False)
    stages.append({"stage": "mid_p0", **hygiene(text.encode(), "mid_p0")})

    text, confirmed_audit = apply_confirmed_patch(text, patch_hunks, inverse=False)
    stages.append({"stage": "mid_confirmed", **hygiene(text.encode(), "mid_confirmed")})

    text, forwarder_audit = forwarders(text, inventory, inverse=False)
    result = text.encode("utf-8")
    stages.append({"stage": "forwarders_47", **hygiene(result, "forwarders")})
    return result, {
        "stages": stages,
        "early": early_audit,
        "mid_p0": p0_audit,
        "mid_confirmed": confirmed_audit,
        "forwarders": forwarder_audit,
    }


def inverse(
    raw: bytes, late: ModuleType, early: ModuleType, mid: ModuleType,
    patch_hunks: list[dict[str, object]], inventory: dict[str, object],
) -> bytes:
    text = raw.decode("utf-8")
    text, _ = forwarders(text, inventory, inverse=True)
    text, _ = apply_confirmed_patch(text, patch_hunks, inverse=True)
    text, _ = mid.transform(text, inverse=True)
    text = early.invert_exact(text)
    text = exact_replace(text, WEIGHTED_NEW, WEIGHTED_OLD, "inverse_weighted_hstar_two")
    return late._inverse(text.encode("utf-8"))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--mode", choices=("forward", "inverse"), default="forward")
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--audit", type=Path)
    parser.add_argument("--check-only", action="store_true")
    parser.add_argument("--late-transformer", type=Path, required=True)
    parser.add_argument("--early-transformer", type=Path, required=True)
    parser.add_argument("--mid-p0-transformer", type=Path, required=True)
    parser.add_argument("--mid-confirmed-patch", type=Path, required=True)
    parser.add_argument("--forwarder-inventory", type=Path, required=True)
    args = parser.parse_args()

    for key, path in (
        ("mid_confirmed_patch", args.mid_confirmed_patch),
        ("forwarder_inventory", args.forwarder_inventory),
    ):
        if sha256(path.read_bytes()) != HELPER_SHA256[key]:
            raise AssertionError(f"{key}: SHA-256 mismatch")
    late = load_exact_module(args.late_transformer, HELPER_SHA256["late"], "late")
    early = load_exact_module(args.early_transformer, HELPER_SHA256["early"], "early")
    mid = load_exact_module(args.mid_p0_transformer, HELPER_SHA256["mid_p0"], "mid_p0")
    patch_hunks = parse_confirmed_patch(args.mid_confirmed_patch.read_bytes())
    inventory = json.loads(args.forwarder_inventory.read_text(encoding="utf-8"))
    source = args.input.read_bytes()
    source_info = hygiene(source, "source")

    if args.mode == "forward":
        if (source_info["sha256"], source_info["git_blob"], source_info["bytes"], source_info["lf"]) != (
            EXPECTED_INPUT_SHA256, EXPECTED_INPUT_GIT_BLOB, EXPECTED_INPUT_BYTES, EXPECTED_INPUT_LF
        ):
            raise AssertionError("exact candidate64f input seal mismatch")
        result, detail = forward(source, late, early, mid, patch_hunks, inventory)
        restored = inverse(result, late, early, mid, patch_hunks, inventory)
    else:
        result = inverse(source, late, early, mid, patch_hunks, inventory)
        restored, detail = forward(result, late, early, mid, patch_hunks, inventory)
    if restored != source:
        raise AssertionError("composed byte-exact roundtrip failed")

    result_info = hygiene(result, "result")
    if args.mode == "forward" and EXPECTED_OUTPUT_SHA256 != "__TO_BE_SEALED__":
        if (result_info["sha256"], result_info["git_blob"], result_info["bytes"], result_info["lf"]) != (
            EXPECTED_OUTPUT_SHA256, EXPECTED_OUTPUT_GIT_BLOB, EXPECTED_OUTPUT_BYTES, EXPECTED_OUTPUT_LF
        ):
            raise AssertionError("sealed integrated output mismatch")
    before_trust = trust_counts(source.decode("utf-8"))
    after_trust = trust_counts(result.decode("utf-8"))
    if before_trust != after_trust:
        raise AssertionError("trust-marker inventory changed")

    audit = {
        "schema": SCHEMA,
        "status": "STATIC_COMPOSITION_PASS_NOT_LEAN_EXECUTED",
        "mode": args.mode,
        "source": source_info,
        "result": result_info,
        "active_occurrences": {
            "late_static": 165,
            "weighted_hstar_two": 1,
            "early_exact": 5,
            "mid_p0": 17,
            "mid_confirmed_unique": sum(
                count for line, count in PATCH_ATOMIC_OCCURRENCES.items()
                if line not in DELEGATED_PATCH_HUNKS
            ),
            "forwarders": 47,
            "total": 165 + 1 + 5 + 17 + 19 + 47,
        },
        "confirmed_patch": {
            "conceptual_occurrences_total": sum(PATCH_ATOMIC_OCCURRENCES.values()),
            "delegated_to_early": sorted(DELEGATED_PATCH_HUNKS),
            "delegated_occurrences": 5,
            "integrated_after_p0_occurrences": 19,
        },
        "run2_mid_header_lines": list(RUN2_MID_HEADER_LINES),
        "run2_weighted_header_line": 4683,
        "forwarder_strategy": {
            "replacement": "inventoried declaration-start theorem to abbrev",
            "count": 47,
            "rhs_and_parameters_unchanged": True,
            "declaration_kind_tradeoff": "diagnostic probe only",
            "rejected_strategy": "theorem name : _ := rhs",
            "rejected_reason": "rc1 resolves theorem header holes before proof RHS",
        },
        "deferred_late_trailing_dot_count": 11,
        "deferred_late_active": False,
        "detail": detail,
        "trust_counts": before_trust,
        "inverse_byte_equal": True,
        "lean_executed": False,
        "remote_accessed": False,
    }
    print(json.dumps(audit, indent=2, sort_keys=True))
    if args.check_only:
        if args.output is not None or args.audit is not None:
            raise AssertionError("--check-only forbids --output/--audit")
        return
    if args.output is None or args.audit is None:
        raise AssertionError("--output and --audit required unless --check-only")
    args.output.write_bytes(result)
    args.audit.write_text(
        json.dumps(audit, indent=2, sort_keys=True) + "\n",
        encoding="utf-8", newline="\n",
    )


if __name__ == "__main__":
    main()
