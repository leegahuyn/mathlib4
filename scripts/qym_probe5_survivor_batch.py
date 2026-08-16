#!/usr/bin/env python3
"""Exact, reversible Probe5 repairs for direct Probe4 survivor headers.

This static transformer accepts only the exact Probe4 candidate.  It joins ten
namespace-qualified identifiers which Lean 4.33 parsed as a namespace followed
by invalid field notation because a line ended with ``.``.  It never invokes
Lean, Lake, Git, or the network and does not mutate repository source files.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from dataclasses import dataclass
from pathlib import Path


SCHEMA = "qym-probe5-survivor-batch-transform-v1"
EXPECTED_INPUT_SHA256 = "fb9d451c88d55e71398f3e3a4b38b3cc9ff5e0a37273115579fc2351d1fdad9c"
EXPECTED_INPUT_GIT_BLOB = "b08d7bb621d8acc8338f3afa3f12ac2ff2c7e6d1"
EXPECTED_INPUT_BYTES = 2_910_229
EXPECTED_INPUT_LF = 61_523
AUTHORITY_LOG_SHA256 = "3ce6d19d831d1723b19fb15181e9561cb1e6b8744e130812838469a03011ddc6"
AUTHORITY_ERROR_HEADERS = 624

# Sealed after first exact projection; ``--allow-unsealed`` is verifier-only.
EXPECTED_OUTPUT_SHA256 = "dc721d886e8e1e78b3c7354d6cce0a50eae27f8164c132fa9c19271b7c4b9cb7"
EXPECTED_OUTPUT_GIT_BLOB = "9c53dc719cbb04e6d5765b4af3c4a4460e2da2d1"
EXPECTED_OUTPUT_BYTES = 2_910_141
EXPECTED_OUTPUT_LF = 61_513


@dataclass(frozen=True)
class Repair:
    label: str
    actual_error_line: int
    old: str
    new: str
    actual_headers_targeted: int = 2
    occurrences: int = 1


REPAIRS: tuple[Repair, ...] = (
    Repair(
        "join_pmap_formal_adjoint_wrapper",
        24904,
        "  intro 𝕜 H _ _ _ _ T lambda hT hlambda\n"
        "  exact QYM.UnboundedCompactSpectralMappingExtension.pmap_eigenvalue_is_real\n"
        "    (T := T)\n"
        "    (QYM.UnboundedCompactSpectralMappingExtension.\n"
        "      pmap_isFormalAdjoint_of_selfAdjoint hT)\n"
        "    hlambda\n",
        "  intro 𝕜 H _ _ _ _ T lambda hT hlambda\n"
        "  exact QYM.UnboundedCompactSpectralMappingExtension.pmap_eigenvalue_is_real\n"
        "    (T := T)\n"
        "    (QYM.UnboundedCompactSpectralMappingExtension."
        "pmap_isFormalAdjoint_of_selfAdjoint hT)\n"
        "    hlambda\n",
    ),
    Repair(
        "join_not_eigenvalue_at_resolvent",
        26598,
        "          QYM.UnboundedCompactSpectralMappingExtension.\n"
        "            not_hasPMapEigenvalue_at_resolvent ρ hlambda.1\n",
        "          QYM.UnboundedCompactSpectralMappingExtension."
        "not_hasPMapEigenvalue_at_resolvent ρ hlambda.1\n",
    ),
    Repair(
        "join_resolvent_eigenvalue_equivalence",
        26600,
        "      refine ⟨(QYM.UnboundedCompactSpectralMappingExtension.\n"
        "        hasPMapEigenvalue_iff_resolvent_hasEigenvalue ρ hzlambda).mp hlambda.1, ?_⟩\n",
        "      refine ⟨(QYM.UnboundedCompactSpectralMappingExtension."
        "hasPMapEigenvalue_iff_resolvent_hasEigenvalue ρ hzlambda).mp hlambda.1, ?_⟩\n",
    ),
    Repair(
        "join_nonnegative_real_pmap_eigenvalue",
        26750,
        "    exact QYM.UnboundedCompactSpectralMappingExtension.\n"
        "      real_pmap_eigenvalue_nonnegative hnonnegative (heigen n)\n",
        "    exact QYM.UnboundedCompactSpectralMappingExtension."
        "real_pmap_eigenvalue_nonnegative hnonnegative (heigen n)\n",
    ),
    Repair(
        "join_index_one_ground_complement_bound",
        26893,
        "    QYM.UnboundedCompactSpectralMappingExtension.\n"
        "      real_pmap_eigenvalue_ge_of_groundComplementCoercivity\n"
        "        hsymm hcoercive hone hx\n",
        "    QYM.UnboundedCompactSpectralMappingExtension."
        "real_pmap_eigenvalue_ge_of_groundComplementCoercivity\n"
        "      hsymm hcoercive hone hx\n",
    ),
    Repair(
        "join_arbitrary_index_ground_complement_bound",
        26915,
        "    QYM.UnboundedCompactSpectralMappingExtension.\n"
        "      real_pmap_eigenvalue_ge_of_groundComplementCoercivity\n"
        "        hsymm hcoercive hk hx\n",
        "    QYM.UnboundedCompactSpectralMappingExtension."
        "real_pmap_eigenvalue_ge_of_groundComplementCoercivity\n"
        "      hsymm hcoercive hk hx\n",
    ),
    Repair(
        "join_pure_discrete_divergence_forwarder",
        27160,
        "    QYM.CompactResolventPureDiscreteExtension.\n"
        "      nonnegative_finiteFiber_pointEigenvalueSequence_tendsto_atTop\n"
        "        ρ hT hcompact hnonnegative eigenvalue heigen hfiniteFiber\n",
        "    QYM.CompactResolventPureDiscreteExtension."
        "nonnegative_finiteFiber_pointEigenvalueSequence_tendsto_atTop\n"
        "      ρ hT hcompact hnonnegative eigenvalue heigen hfiniteFiber\n",
    ),
    Repair(
        "join_adjacent_ground_gap_forwarder",
        27232,
        "    QYM.CompactResolventLowLyingGapExtension.\n"
        "      adjacentGroundGap_ge_of_indexOne_offGround\n"
        "        hT hcoercive eigenvalue heigen hground hone\n",
        "    QYM.CompactResolventLowLyingGapExtension."
        "adjacentGroundGap_ge_of_indexOne_offGround\n"
        "      hT hcoercive eigenvalue heigen hground hone\n",
    ),
    Repair(
        "join_first_off_ground_gap_forwarder",
        27254,
        "    QYM.CompactResolventLowLyingGapExtension.\n"
        "      firstOffGroundGap_ge hT hcoercive eigenvalue heigen hground hexists\n",
        "    QYM.CompactResolventLowLyingGapExtension."
        "firstOffGroundGap_ge hT hcoercive eigenvalue heigen hground hexists\n",
    ),
    Repair(
        "join_positive_liminf_gap_family_forwarder",
        27283,
        "    QYM.CompactResolventLowLyingGapExtension.\n"
        "      exists_gapFamily_with_positive_ennreal_liminf\n"
        "        ρ hμ hc hT hcompact hcoercive hzero hnonzero\n",
        "    QYM.CompactResolventLowLyingGapExtension."
        "exists_gapFamily_with_positive_ennreal_liminf\n"
        "      ρ hμ hc hT hcompact hcoercive hzero hnonzero\n",
    ),
)


TRUST_PATTERNS = {
    "sorry": re.compile(r"(?<![\w.])sorry(?![\w])"),
    "admit": re.compile(r"(?<![\w.])admit(?![\w])"),
    "native_decide": re.compile(r"(?<![\w.])native_decide(?![\w])"),
    "Lean.ofReduceBool": re.compile(r"(?<![\w.])Lean\.ofReduceBool(?![\w])"),
    "axiom_declaration": re.compile(r"^[ \t]*axiom\b", re.MULTILINE),
    "unsafe_declaration": re.compile(
        r"^[ \t]*unsafe[ \t]+(?:def|theorem|abbrev|instance)\b", re.MULTILINE
    ),
    "maxHeartbeats_zero": re.compile(
        r"^[ \t]*set_option[ \t]+maxHeartbeats[ \t]+0\b", re.MULTILINE
    ),
}


def sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def git_blob(raw: bytes) -> str:
    return hashlib.sha1(f"blob {len(raw)}\0".encode("ascii") + raw).hexdigest()


def identity(raw: bytes, label: str) -> dict[str, object]:
    if raw.startswith(b"\xef\xbb\xbf") or b"\r" in raw or b"\x00" in raw:
        raise AssertionError(f"{label}: BOM, CR, and NUL are forbidden")
    if not raw.endswith(b"\n"):
        raise AssertionError(f"{label}: terminal LF required")
    raw.decode("utf-8", errors="strict")
    return {
        "sha256": sha256(raw),
        "git_blob": git_blob(raw),
        "bytes": len(raw),
        "lf": raw.count(b"\n"),
        "utf8": True,
        "terminal_lf": True,
        "bom": False,
        "cr": False,
        "nul": False,
    }


def expected_input() -> dict[str, object]:
    return {
        "sha256": EXPECTED_INPUT_SHA256,
        "git_blob": EXPECTED_INPUT_GIT_BLOB,
        "bytes": EXPECTED_INPUT_BYTES,
        "lf": EXPECTED_INPUT_LF,
    }


def expected_output() -> dict[str, object]:
    return {
        "sha256": EXPECTED_OUTPUT_SHA256,
        "git_blob": EXPECTED_OUTPUT_GIT_BLOB,
        "bytes": EXPECTED_OUTPUT_BYTES,
        "lf": EXPECTED_OUTPUT_LF,
    }


def assert_identity(
    actual: dict[str, object], expected: dict[str, object], label: str, allow_unsealed: bool
) -> None:
    if allow_unsealed and expected["sha256"] == "TO_BE_SEALED":
        return
    observed = {key: actual[key] for key in expected}
    if observed != expected:
        raise AssertionError(f"{label}: {observed} != {expected}")


def trust_counts(text: str) -> dict[str, int]:
    return {name: len(pattern.findall(text)) for name, pattern in TRUST_PATTERNS.items()}


def transform(text: str, inverse: bool) -> tuple[str, list[dict[str, object]]]:
    ordered = tuple(reversed(REPAIRS)) if inverse else REPAIRS
    audit: list[dict[str, object]] = []
    for repair in ordered:
        source = repair.new if inverse else repair.old
        target = repair.old if inverse else repair.new
        found = text.count(source)
        if found != repair.occurrences:
            raise AssertionError(
                f"{repair.label}: found {found}, expected {repair.occurrences}"
            )
        text = text.replace(source, target)
        audit.append(
            {
                "label": repair.label,
                "actual_error_line": repair.actual_error_line,
                "actual_headers_targeted": repair.actual_headers_targeted,
                "occurrences": repair.occurrences,
                "inverse": inverse,
            }
        )
    return text, audit


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--audit", type=Path, required=True)
    parser.add_argument("--inverse", action="store_true")
    parser.add_argument("--allow-unsealed", action="store_true", help=argparse.SUPPRESS)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    if args.input.resolve() == args.output.resolve():
        raise AssertionError("input and output paths must differ")
    raw = args.input.read_bytes()
    before = identity(raw, "input")
    assert_identity(
        before,
        expected_output() if args.inverse else expected_input(),
        "input identity",
        args.allow_unsealed,
    )
    text = raw.decode("utf-8")
    before_trust = trust_counts(text)
    transformed, rules = transform(text, args.inverse)
    after_trust = trust_counts(transformed)
    if after_trust != before_trust:
        raise AssertionError(f"trust changed: {before_trust} -> {after_trust}")
    out_raw = transformed.encode("utf-8")
    after = identity(out_raw, "output")
    assert_identity(
        after,
        expected_input() if args.inverse else expected_output(),
        "output identity",
        args.allow_unsealed,
    )
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.audit.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_bytes(out_raw)
    args.audit.write_text(
        json.dumps(
            {
                "schema": SCHEMA,
                "inverse": args.inverse,
                "authority": {
                    "probe4_candidate_sha256": EXPECTED_INPUT_SHA256,
                    "probe4_candidate_git_blob": EXPECTED_INPUT_GIT_BLOB,
                    "probe4_log_sha256": AUTHORITY_LOG_SHA256,
                    "probe4_error_headers": AUTHORITY_ERROR_HEADERS,
                },
                "input": before,
                "output": after,
                "rules": rules,
                "active_occurrences": sum(r.occurrences for r in REPAIRS),
                "actual_error_headers_targeted": sum(
                    r.actual_headers_targeted for r in REPAIRS
                ),
                "trust_before": before_trust,
                "trust_after": after_trust,
                "trust_delta_zero": before_trust == after_trust,
                "lean_invoked": False,
                "lake_invoked": False,
                "remote_mutated": False,
                "repository_source_mutated": False,
            },
            indent=2,
            ensure_ascii=False,
        )
        + "\n",
        encoding="utf-8",
        newline="\n",
    )


if __name__ == "__main__":
    main()
