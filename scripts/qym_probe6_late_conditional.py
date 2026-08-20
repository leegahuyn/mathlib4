#!/usr/bin/env python3
"""Static, conditional Probe6 late repairs over the exact sealed Probe5 bytes.

This helper never invokes Lean, Lake, Git, or the network.  It accepts only the
exact Probe5 candidate, checks the immutable Probe4 compiler log and error
header inventory, applies eight occurrence-counted repair families, and proves
an exact inverse plus unchanged executable-trust counters.  The output remains
conditional until an authoritative Probe5 run shows which diagnostics survive.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Any


SCHEMA = "qym-probe6-late-conditional-transform-v1"

EXPECTED_PROBE5_INPUT_SHA256 = (
    "30edb320b25eadbfda284160016a5a23cc28a95d6228cbd061161d4ec615de7c"
)
EXPECTED_PROBE5_INPUT_GIT_BLOB = "9ea2ef7d03555cca4e82cbeeb01cba033dff6b99"
EXPECTED_PROBE5_INPUT_BYTES = 2_911_806
EXPECTED_PROBE5_INPUT_LF = 61_557

EXPECTED_PROBE4_SHA256 = (
    "fb9d451c88d55e71398f3e3a4b38b3cc9ff5e0a37273115579fc2351d1fdad9c"
)
EXPECTED_PROBE4_GIT_BLOB = "b08d7bb621d8acc8338f3afa3f12ac2ff2c7e6d1"
EXPECTED_PROBE4_BYTES = 2_910_229
EXPECTED_PROBE4_LF = 61_523
EXPECTED_PROBE4_LOG_SHA256 = (
    "3ce6d19d831d1723b19fb15181e9561cb1e6b8744e130812838469a03011ddc6"
)
EXPECTED_PROBE4_ERROR_HEADERS_SHA256 = (
    "a9b9ae54fcc4f44800bff26a75f6513beeaa469601df8aba7418a20e04356431"
)

# Sealed after one deterministic local projection, then enforced both ways.
EXPECTED_OUTPUT_SHA256 = (
    "38c4493bbc24c165ebed4daf2a02ea5eab63f43a2841e1a898caf687c6454290"
)
EXPECTED_OUTPUT_GIT_BLOB = "83f35481a26055f4a98706632c0c0e8f63f0a66a"
EXPECTED_OUTPUT_BYTES = 2_911_441
EXPECTED_OUTPUT_LF = 61_547


@dataclass(frozen=True)
class DirectHeader:
    line: int
    column: int
    message_contains: str


@dataclass(frozen=True)
class ExactReplacement:
    old: str
    new: str
    occurrences: int = 1


@dataclass(frozen=True)
class RepairFamily:
    label: str
    kind: str
    direct_headers: tuple[DirectHeader, ...]
    replacements: tuple[ExactReplacement, ...]
    cascade_headers_deliberately_not_repaired: tuple[int, ...] = ()


REPAIRS: tuple[RepairFamily, ...] = (
    RepairFamily(
        label="circular_arc_add_positive_api",
        kind="api",
        direct_headers=(DirectHeader(43440, 32, "Unknown constant `add_pos.mpr`"),),
        replacements=(
            ExactReplacement(
                old="""  have hb := circularArc_strict_bounds ht
  have hp : 0 < (1 - t) * (t + 1) :=
    mul_pos (sub_pos.mpr hb.2) (add_pos.mpr hb.1)
""",
                new="""  have hb := circularArc_strict_bounds ht
  have htAdd : 0 < t + 1 := by
    linarith [hb.1]
  have hp : 0 < (1 - t) * (t + 1) :=
    mul_pos (sub_pos.mpr hb.2) htAdd
""",
            ),
        ),
    ),
    RepairFamily(
        label="subtraction_normal_form_api",
        kind="api",
        direct_headers=(
            DirectHeader(44828, 30, "Unknown identifier `add_neg_eq_sub`"),
            DirectHeader(46319, 30, "Unknown identifier `add_neg_eq_sub`"),
        ),
        replacements=(
            ExactReplacement(
                old="Int.cast_neg, add_neg_eq_sub] using hre\n",
                new="Int.cast_neg, sub_eq_add_neg] using hre\n",
                occurrences=2,
            ),
        ),
    ),
    RepairFamily(
        label="fixed_phase_orbit_multiplier_namespace",
        kind="namespace_producer",
        direct_headers=(
            DirectHeader(47367, 24, "Unknown identifier `OrbitMultiplier`"),
        ),
        replacements=(
            ExactReplacement(
                old="(OrbitMultiplier ",
                new=(
                    "(Mock2FA.PaperCorrections.AutomorphicSobolev."
                    "DefinitionOneSobolev.FixedPhasePeterssonCoordinates."
                    "OrbitMultiplier "
                ),
                occurrences=2,
            ),
        ),
        cascade_headers_deliberately_not_repaired=(47369, 47407),
    ),
    RepairFamily(
        label="product_collar_width_two_circle_namespace",
        kind="namespace_producer",
        direct_headers=(
            DirectHeader(
                48544,
                13,
                "Unknown identifier `QYM.FullCertification."
                "P2ActualFixedPhaseCuspTraceGraphExtension.WidthTwoCircle`",
            ),
        ),
        replacements=(
            ExactReplacement(
                old=(
                    "    (theta : QYM.FullCertification."
                    "P2ActualFixedPhaseCuspTraceGraphExtension.WidthTwoCircle)\n"
                ),
                new=(
                    "    (theta : QYM.FullCertification."
                    "P2SmoothQuotientAtlasExtension.WidthTwoCircle)\n"
                ),
            ),
        ),
        cascade_headers_deliberately_not_repaired=(48621,),
    ),
    RepairFamily(
        label="product_collar_selected_cusp_circle_namespace",
        kind="namespace_producer",
        direct_headers=(
            DirectHeader(
                48547,
                9,
                "Unknown identifier `QYM.FullCertification."
                "P2ActualFixedPhaseCuspTraceGraphExtension.selectedCuspCircle`",
            ),
        ),
        replacements=(
            ExactReplacement(
                old=(
                    "    (b : ActualFixedPhaseCollarBoundary n Y) :\n"
                    "    QYM.FullCertification.P2CuspCollarClosureExtension."
                    "cuspCollarHomeomorph q hY\n"
                    "        (QYM.FullCertification."
                    "P2ActualFixedPhaseCuspTraceGraphExtension.selectedCuspCircle "
                    "q Y theta) =\n"
                ),
                new=(
                    "    (b : ActualFixedPhaseCollarBoundary n Y) :\n"
                    "    QYM.FullCertification.P2CuspCollarClosureExtension."
                    "cuspCollarHomeomorph q hY\n"
                    "        (QYM.FullCertification."
                    "P2SmoothQuotientAtlasExtension.selectedCuspCircle q Y theta) =\n"
                ),
            ),
        ),
    ),
    RepairFamily(
        label="idempotent_projection_to_linear_map_api",
        kind="api_producer",
        direct_headers=(
            DirectHeader(55467, 59, "Invalid field `toLinearMap`"),
            DirectHeader(56124, 59, "Invalid field `toLinearMap`"),
            DirectHeader(58180, 42, "Invalid field `toLinearMap`"),
        ),
        replacements=(
            ExactReplacement(
                old="""  have hCompl :=
    (actualNormalizedInverseEtaProjection_isIdempotent hY).toLinearMap.isCompl
""",
                new="""  have hCompl :=
    (ContinuousLinearMap.IsIdempotentElem.toLinearMap
      (actualNormalizedInverseEtaProjection_isIdempotent hY)).isCompl
""",
            ),
            ExactReplacement(
                old="""  ⟨(actualInverseEtaProjectionHamiltonian_isIdempotent hY).toLinearMap,
    actualInverseEtaProjectionHamiltonian_isSymmetric hY⟩
""",
                new="""  ⟨ContinuousLinearMap.IsIdempotentElem.toLinearMap
      (actualInverseEtaProjectionHamiltonian_isIdempotent hY),
    actualInverseEtaProjectionHamiltonian_isSymmetric hY⟩
""",
            ),
            ExactReplacement(
                old="""  have h := groundProjection_isIdempotent.toLinearMap.isCompl
""",
                new="""  have h :=
    (ContinuousLinearMap.IsIdempotentElem.toLinearMap
      groundProjection_isIdempotent).isCompl
""",
            ),
        ),
        cascade_headers_deliberately_not_repaired=(55465, 58179),
    ),
    RepairFamily(
        label="idempotent_positive_iff_explicit_api",
        kind="api",
        direct_headers=(DirectHeader(56132, 2, "Function expected at"),),
        replacements=(
            ExactReplacement(
                old="""  (actualInverseEtaProjectionHamiltonian_isIdempotent hY)
    .isPositive_iff_isSelfAdjoint.mpr
    (actualInverseEtaProjectionHamiltonian_isSelfAdjoint hY)
""",
                new="""  (ContinuousLinearMap.IsIdempotentElem.isPositive_iff_isSelfAdjoint
    (actualInverseEtaProjectionHamiltonian_isIdempotent hY)).mpr
    (actualInverseEtaProjectionHamiltonian_isSelfAdjoint hY)
""",
            ),
        ),
    ),
    RepairFamily(
        label="closed_operator_api_drop_obsolete_green_arguments",
        kind="api_producer",
        direct_headers=tuple(
            DirectHeader(line, 2, "Function expected at")
            for line in (57670, 57680, 57690, 57702, 57712, 57722)
        ),
        replacements=(
            ExactReplacement(
                old="""  Mock2FA.PaperCorrections.AutomorphicSobolev.FixedPhaseClosedOperators.physicalRaise_isClosable n
    (physicalGreenIdentityAt_of_actualHighCutoffBoundaryEqualityResidual
      hResidual n)
""",
                new="""  Mock2FA.PaperCorrections.AutomorphicSobolev.FixedPhaseClosedOperators.physicalRaise_isClosable n
""",
            ),
            ExactReplacement(
                old="""  Mock2FA.PaperCorrections.AutomorphicSobolev.FixedPhaseClosedOperators.physicalLowerFromSucc_isClosable n
    (physicalGreenIdentityAt_of_actualHighCutoffBoundaryEqualityResidual
      hResidual n)
""",
                new="""  Mock2FA.PaperCorrections.AutomorphicSobolev.FixedPhaseClosedOperators.physicalLowerFromSucc_isClosable n
""",
            ),
            ExactReplacement(
                old="""  Mock2FA.PaperCorrections.AutomorphicSobolev.FixedPhaseClosedOperators.physicalJointFromSucc_isClosable n
    (physicalGreenIdentityAt_of_actualHighCutoffBoundaryEqualityResidual
      hResidual n)
    (physicalGreenIdentityAt_of_actualHighCutoffBoundaryEqualityResidual
      hResidual (n + 1))
""",
                new="""  Mock2FA.PaperCorrections.AutomorphicSobolev.FixedPhaseClosedOperators.physicalJointFromSucc_isClosable n
""",
            ),
            ExactReplacement(
                old="""  Mock2FA.PaperCorrections.AutomorphicSobolev.FixedPhaseClosedOperators.closedRaise_isClosed n
    (physicalGreenIdentityAt_of_actualHighCutoffBoundaryEqualityResidual
      hResidual n)
""",
                new="""  Mock2FA.PaperCorrections.AutomorphicSobolev.FixedPhaseClosedOperators.closedRaise_isClosed n
""",
            ),
            ExactReplacement(
                old="""  Mock2FA.PaperCorrections.AutomorphicSobolev.FixedPhaseClosedOperators.closedLowerFromSucc_isClosed n
    (physicalGreenIdentityAt_of_actualHighCutoffBoundaryEqualityResidual
      hResidual n)
""",
                new="""  Mock2FA.PaperCorrections.AutomorphicSobolev.FixedPhaseClosedOperators.closedLowerFromSucc_isClosed n
""",
            ),
            ExactReplacement(
                old="""  Mock2FA.PaperCorrections.AutomorphicSobolev.FixedPhaseClosedOperators.closedJointFromSucc_isClosed n
    (physicalGreenIdentityAt_of_actualHighCutoffBoundaryEqualityResidual
      hResidual n)
    (physicalGreenIdentityAt_of_actualHighCutoffBoundaryEqualityResidual
      hResidual (n + 1))
""",
                new="""  Mock2FA.PaperCorrections.AutomorphicSobolev.FixedPhaseClosedOperators.closedJointFromSucc_isClosed n
""",
            ),
        ),
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

HEADER_RE = re.compile(
    r"^.*QYM\.lean:(?P<line>\d+):(?P<column>\d+): "
    r"error(?:\([^)]*\))?: (?P<message>.*)$"
)


def sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def git_blob(raw: bytes) -> str:
    return hashlib.sha1(
        b"blob " + str(len(raw)).encode("ascii") + b"\0" + raw
    ).hexdigest()


def shape(raw: bytes, label: str) -> dict[str, Any]:
    if raw.startswith(b"\xef\xbb\xbf"):
        raise RuntimeError(f"{label}: UTF-8 BOM forbidden")
    if b"\r" in raw:
        raise RuntimeError(f"{label}: CR forbidden")
    if b"\0" in raw:
        raise RuntimeError(f"{label}: NUL forbidden")
    if not raw.endswith(b"\n"):
        raise RuntimeError(f"{label}: terminal LF required")
    raw.decode("utf-8", errors="strict")
    return {
        "sha256": sha256(raw),
        "git_blob": git_blob(raw),
        "bytes": len(raw),
        "lf": raw.count(b"\n"),
        "utf8": True,
        "bom": False,
        "cr": False,
        "nul": False,
        "terminal_lf": True,
    }


def expected_shape(*, output: bool) -> tuple[str, str, int, int]:
    if output:
        return (
            EXPECTED_OUTPUT_SHA256,
            EXPECTED_OUTPUT_GIT_BLOB,
            EXPECTED_OUTPUT_BYTES,
            EXPECTED_OUTPUT_LF,
        )
    return (
        EXPECTED_PROBE5_INPUT_SHA256,
        EXPECTED_PROBE5_INPUT_GIT_BLOB,
        EXPECTED_PROBE5_INPUT_BYTES,
        EXPECTED_PROBE5_INPUT_LF,
    )


def assert_shape(
    actual: dict[str, Any], expected: tuple[str, str, int, int], *,
    allow_unsealed: bool, label: str
) -> None:
    if expected[0] == "__TO_SEAL__":
        if allow_unsealed:
            return
        raise RuntimeError(f"{label}: output identity has not been sealed")
    keys = ("sha256", "git_blob", "bytes", "lf")
    got = tuple(actual[key] for key in keys)
    if got != expected:
        raise RuntimeError(f"{label}: identity {got!r} != {expected!r}")


def trust_counts(text: str) -> dict[str, int]:
    return {name: len(pattern.findall(text)) for name, pattern in TRUST_PATTERNS.items()}


def occurrence_lines(text: str, needle: str) -> list[int]:
    lines: list[int] = []
    start = 0
    while True:
        offset = text.find(needle, start)
        if offset < 0:
            return lines
        lines.append(text.count("\n", 0, offset) + 1)
        start = offset + len(needle)


def parse_error_headers(raw: bytes) -> dict[tuple[int, int], list[str]]:
    rows: dict[tuple[int, int], list[str]] = {}
    for line in raw.decode("utf-8").splitlines():
        match = HEADER_RE.match(line)
        if match is None:
            continue
        key = (int(match.group("line")), int(match.group("column")))
        rows.setdefault(key, []).append(match.group("message"))
    return rows


def validate_direct_headers(headers_raw: bytes) -> list[dict[str, Any]]:
    parsed = parse_error_headers(headers_raw)
    mapped: list[dict[str, Any]] = []
    for family in REPAIRS:
        for wanted in family.direct_headers:
            messages = parsed.get((wanted.line, wanted.column), [])
            matched = [m for m in messages if wanted.message_contains in m]
            if len(matched) != 1:
                raise RuntimeError(
                    f"{family.label}: header {wanted.line}:{wanted.column} "
                    f"containing {wanted.message_contains!r} matched {matched!r}"
                )
            mapped.append(
                {
                    "repair": family.label,
                    "probe4_line": wanted.line,
                    "column": wanted.column,
                    "message": matched[0],
                }
            )
    return mapped


def validate_authority(
    *, probe4_raw: bytes, log_raw: bytes, headers_raw: bytes
) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    probe4_identity = shape(probe4_raw, "Probe4 candidate")
    expected_probe4 = (
        EXPECTED_PROBE4_SHA256,
        EXPECTED_PROBE4_GIT_BLOB,
        EXPECTED_PROBE4_BYTES,
        EXPECTED_PROBE4_LF,
    )
    assert_shape(
        probe4_identity, expected_probe4, allow_unsealed=False,
        label="Probe4 candidate"
    )
    if sha256(log_raw) != EXPECTED_PROBE4_LOG_SHA256:
        raise RuntimeError("Probe4 log SHA-256 mismatch")
    if sha256(headers_raw) != EXPECTED_PROBE4_ERROR_HEADERS_SHA256:
        raise RuntimeError("Probe4 error-header SHA-256 mismatch")
    mapped = validate_direct_headers(headers_raw)
    return probe4_identity, mapped


def transform(
    text: str, *, inverse: bool, probe4_text: str
) -> tuple[str, list[dict[str, Any]]]:
    families = tuple(reversed(REPAIRS)) if inverse else REPAIRS
    audit: list[dict[str, Any]] = []
    for family in families:
        replacements = (
            tuple(reversed(family.replacements)) if inverse else family.replacements
        )
        family_rows: list[dict[str, Any]] = []
        for replacement in replacements:
            source = replacement.new if inverse else replacement.old
            target = replacement.old if inverse else replacement.new
            source_lines = occurrence_lines(text, source)
            if len(source_lines) != replacement.occurrences:
                raise RuntimeError(
                    f"{family.label}: expected {replacement.occurrences} exact "
                    f"source occurrences, found {len(source_lines)}"
                )
            # On the forward path, every anchor must also be byte-identical in
            # Probe4.  This is the local proof that Probe5 did not edit it.
            probe4_lines: list[int] = []
            if not inverse:
                probe4_lines = occurrence_lines(probe4_text, replacement.old)
                if len(probe4_lines) != replacement.occurrences:
                    raise RuntimeError(
                        f"{family.label}: exact anchor was not preserved from Probe4"
                    )
            text = text.replace(source, target)
            target_lines = occurrence_lines(text, target)
            if len(target_lines) != replacement.occurrences:
                raise RuntimeError(
                    f"{family.label}: target occurrence count is "
                    f"{len(target_lines)}, expected {replacement.occurrences}"
                )
            family_rows.append(
                {
                    "occurrences": replacement.occurrences,
                    "source_lines": source_lines,
                    "target_lines": target_lines,
                    "probe4_unchanged_anchor_lines": probe4_lines,
                }
            )
        audit.append(
            {
                "label": family.label,
                "kind": family.kind,
                "direction": "inverse" if inverse else "forward",
                "direct_probe4_headers": [
                    {
                        "line": row.line,
                        "column": row.column,
                        "message_contains": row.message_contains,
                    }
                    for row in family.direct_headers
                ],
                "cascade_headers_deliberately_not_repaired": list(
                    family.cascade_headers_deliberately_not_repaired
                ),
                "replacements": family_rows,
            }
        )
    return text, audit


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--audit", type=Path, required=True)
    parser.add_argument("--probe4", type=Path, required=True)
    parser.add_argument("--probe4-log", type=Path, required=True)
    parser.add_argument("--probe4-error-headers", type=Path, required=True)
    parser.add_argument("--inverse", action="store_true")
    parser.add_argument("--allow-unsealed", action="store_true", help=argparse.SUPPRESS)
    args = parser.parse_args()

    if args.input.resolve() == args.output.resolve():
        raise RuntimeError("input and output paths must differ")

    raw = args.input.read_bytes()
    before = shape(raw, "transform input")
    assert_shape(
        before,
        expected_shape(output=args.inverse),
        allow_unsealed=args.allow_unsealed,
        label="transform input",
    )

    probe4_raw = args.probe4.read_bytes()
    log_raw = args.probe4_log.read_bytes()
    headers_raw = args.probe4_error_headers.read_bytes()
    probe4_identity, direct_header_map = validate_authority(
        probe4_raw=probe4_raw, log_raw=log_raw, headers_raw=headers_raw
    )

    before_text = raw.decode("utf-8")
    before_trust = trust_counts(before_text)
    transformed_text, repair_audit = transform(
        before_text,
        inverse=args.inverse,
        probe4_text=probe4_raw.decode("utf-8"),
    )
    after_trust = trust_counts(transformed_text)
    if before_trust != after_trust:
        raise RuntimeError(f"trust counters changed: {before_trust} -> {after_trust}")

    out_raw = transformed_text.encode("utf-8")
    after = shape(out_raw, "transform output")
    assert_shape(
        after,
        expected_shape(output=not args.inverse),
        allow_unsealed=args.allow_unsealed,
        label="transform output",
    )

    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.audit.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_bytes(out_raw)
    payload = {
        "schema": SCHEMA,
        "status": "STATIC_CONDITIONAL_NOT_LEAN_EXECUTED",
        "direction": "inverse" if args.inverse else "forward",
        "conditional": True,
        "promotion": False,
        "input": before,
        "output": after,
        "probe4_authority": {
            "candidate": probe4_identity,
            "log_sha256": sha256(log_raw),
            "error_headers_sha256": sha256(headers_raw),
            "direct_header_count": len(direct_header_map),
            "direct_header_map": direct_header_map,
        },
        "repair_family_count": len(REPAIRS),
        "exact_replacement_count": sum(len(r.replacements) for r in REPAIRS),
        "active_occurrence_count": sum(
            replacement.occurrences
            for repair in REPAIRS
            for replacement in repair.replacements
        ),
        "repairs": repair_audit,
        "probe5_overlap": {
            "component_edit_overlap": False,
            "proof": "every forward old block remains byte-identical in exact Probe4 and exact Probe5",
        },
        "excluded": {
            "probe5_late_rules": True,
            "probe5_line_41115": True,
            "potential_probe5_cascades": True,
        },
        "trust_before": before_trust,
        "trust_after": after_trust,
        "trust_delta": {
            key: after_trust[key] - before_trust[key] for key in before_trust
        },
        "execution": {
            "lean": False,
            "lake": False,
            "git": False,
            "network": False,
            "remote": False,
            "repository_source_mutation": False,
        },
    }
    args.audit.write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
        newline="\n",
    )
    print(json.dumps(payload, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
