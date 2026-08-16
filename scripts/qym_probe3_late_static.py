#!/usr/bin/env python3
"""Deterministic, reversible late static repairs for the exact 64f QYM probe.

This transformer is deliberately narrower than a general Lean formatter.  It
accepts exactly one byte stream, applies only the eight audited repair
families listed in ``ACTIVE_REWRITES``, and seals the exact output hash.  The
47 result-type-free theorem forwarders are inventory-only and remain inactive.

No Lean/Lake process is invoked by this program.
"""

from __future__ import annotations

import argparse
import bisect
import hashlib
import json
import re
from pathlib import Path
from typing import Iterable


SCHEMA = "qym-probe3-late-static-v1"
EXPECTED_INPUT_SHA256 = (
    "64f045b04dc39e157ba609047e6ac9a0851962b7c74024af9987dbcbd46f19d1"
)
EXPECTED_OUTPUT_SHA256 = (
    "d606e0faaa824f6e080dcb916b31f543d4a17c14b09cd5bdd5c8a5305fa1081c"
)
EXPECTED_INPUT_GIT_BLOB = "5031023859a5cac44aaaf1760564c1e560ede13b"
EXPECTED_OUTPUT_GIT_BLOB = "6d4f6359b99cdca40869df74e66d71bb68247418"
EXPECTED_INPUT_BYTES = 2_906_438
EXPECTED_OUTPUT_BYTES = 2_905_170
EXPECTED_INPUT_LF = 61_580
EXPECTED_OUTPUT_LF = 61_450


# Each row is (one-based input line, prefix length in Unicode code points,
# indentation removed from the following line).  The input and output SHA
# guards make these positional edits collision-free.  The 11 syntactically
# similar but unobserved sites are intentionally excluded from this pass.
TRAILING_DOT_SPECS: tuple[tuple[int, int, int], ...] = (
    (25291, 48, 6), (25375, 48, 6), (25391, 48, 6), (25409, 49, 6),
    (25444, 49, 6), (25485, 49, 6), (25550, 44, 8), (25553, 44, 8),
    (25556, 44, 8), (25559, 44, 8), (25562, 44, 8), (25565, 44, 8),
    (25568, 44, 8), (25571, 44, 8), (25574, 44, 8), (25577, 44, 8),
    (25580, 44, 8), (25583, 44, 8), (25586, 44, 8), (25589, 44, 8),
    (25592, 44, 8), (25595, 44, 8), (25598, 44, 8), (25601, 44, 8),
    (25604, 44, 8), (25607, 44, 8), (25610, 44, 8), (25613, 44, 8),
    (25616, 44, 8), (25619, 44, 8), (25622, 44, 8), (25625, 44, 8),
    (25628, 44, 8), (25631, 44, 8), (25634, 44, 8), (25642, 46, 10),
    (25646, 46, 10), (25650, 46, 10), (25654, 46, 10), (25658, 46, 10),
    (25662, 46, 10), (25666, 46, 10), (25670, 46, 10), (25674, 46, 10),
    (25678, 46, 10), (25682, 46, 10), (25686, 46, 10), (25690, 46, 10),
    (25694, 46, 10), (25698, 46, 10), (25702, 46, 10), (25706, 46, 10),
    (25710, 46, 10), (25714, 46, 10), (25718, 46, 10), (25722, 46, 10),
    (25726, 46, 10), (25730, 46, 10), (25734, 46, 10), (25738, 46, 10),
    (25742, 46, 10), (25746, 46, 10), (25750, 46, 10), (25754, 46, 10),
    (26419, 49, 6), (26456, 49, 6), (26489, 49, 6), (26598, 51, 8),
    (26659, 64, 6), (26679, 64, 6), (26704, 64, 6), (26722, 64, 6),
    (26740, 64, 6), (26760, 64, 6), (26847, 49, 6), (26879, 48, 8),
    (26882, 48, 8), (26912, 49, 6), (26935, 49, 6), (27093, 42, 6),
    (27113, 42, 6), (27133, 46, 6), (27145, 49, 8), (27152, 46, 6),
    (27169, 46, 6), (27182, 53, 10), (27211, 49, 10), (27218, 45, 6),
    (27239, 49, 10), (27246, 45, 6), (27258, 53, 10), (27262, 53, 10),
    (27281, 53, 10), (27286, 52, 12), (27308, 51, 8), (27316, 51, 12),
    (27360, 44, 8), (27363, 44, 8), (27366, 44, 8), (27369, 44, 8),
    (27372, 44, 8), (27375, 44, 8), (27378, 44, 8), (27381, 44, 8),
    (27384, 44, 8), (27387, 44, 8), (27390, 44, 8), (27396, 50, 8),
    (27399, 50, 8), (27402, 50, 8), (27405, 50, 8), (27408, 50, 8),
    (27411, 50, 8), (27414, 50, 8), (27417, 50, 8), (27420, 50, 8),
    (27423, 50, 8), (27426, 50, 8), (30142, 49, 6), (30174, 49, 6),
    (30201, 49, 6), (30214, 50, 6), (31608, 66, 8), (31616, 66, 8),
    (43549, 69, 10), (43558, 69, 10), (43643, 68, 6), (43935, 71, 10),
    (46870, 120, 6), (47057, 65, 4),
)

TRAILING_DOT_DEFERRED_LINES = frozenset(
    {26611, 26613, 26769, 26916, 26939, 27191, 27269, 27293, 27324, 30146, 45212}
)


# (label, one-based input lines, old token, new token)
LINE_REWRITES: tuple[tuple[str, tuple[int, ...], str, str], ...] = (
    (
        "orthogonal_complement_typo_code_only",
        (36996, 37129, 48673, 48691, 48698, 48703, 48707, 48709, 48714, 48742,
         55229, 55505),
        "ᵎ",
        "ᗮ",
    ),
    (
        "neighborhood_notation_typo",
        (26298, 26310, 26311, 27106, 27107, 61537),
        "𝒩",
        "𝓝",
    ),
    (
        "unqualify_resolventSet",
        (54968, 54982, 54996, 55021, 56429, 56443, 56460, 56495, 58686, 58700),
        "spectrum.resolventSet",
        "resolventSet",
    ),
    (
        "correct_SL_neg_smul_namespace",
        (37690, 44890, 46381),
        "UpperHalfPlane.SL_neg_smul",
        "ModularGroup.SL_neg_smul",
    ),
    (
        "qualify_abs_re_le_norm_late_only",
        (52995, 53269),
        "abs_re_le_norm",
        "Complex.abs_re_le_norm",
    ),
    (
        "correct_lambda_arrow",
        (61536,),
        "fun n ⇒",
        "fun n =>",
    ),
)

LOCAL_INSTANCE_OLD = (
    "  letI : ContinuousConstSMul Gamma2 H where\n"
    "    continuous_const_smul := inverseEtaDeckAction_continuous\n"
)
LOCAL_INSTANCE_NEW = (
    "  letI : ContinuousConstSMul Gamma2 H :=\n"
    "    { continuous_const_smul := inverseEtaDeckAction_continuous }\n"
)
LOCAL_INSTANCE_LINE = 47_756


# Inventory only.  These commands are deliberately not changed in this pass.
INACTIVE_THEOREM_SPECS: tuple[tuple[int, int, str], ...] = (
    (56546, 56547, "certificate"),
    (57445, 57445, "transportedSmoothBundleCertificate"),
    (57449, 57449, "actualStagePeterssonL2Certificate"),
    (57453, 57454, "actualStagePeterssonL2PositiveCertificate"),
    (57458, 57458, "actualStageContinuousCoreCertificate"),
    (57462, 57463, "actualStageContinuousInjectiveDenseCertificate"),
    (57468, 57470, "actualStageNonconstantCoreCertificate"),
    (57475, 57476, "actualStageInfiniteDimensionalCertificate"),
    (57480, 57481, "actualStageContinuousPivotCertificate"),
    (57485, 57485, "actualDiscriminantMultiplierCertificate"),
    (57490, 57490, "actualSectorDiscriminantMultiplierCertificate"),
    (57495, 57495, "actualBoundedPotentialSelfAdjointCertificate"),
    (57499, 57499, "actualSectorBoundedPotentialSelfAdjointCertificate"),
    (57503, 57504, "actualRankOneInverseEtaTestOperatorCertificate"),
    (57509, 57511, "actualRankOneInverseEtaNoncoercivityCertificate"),
    (57516, 57517, "actualProjectionHamiltonianCertificate"),
    (57522, 57523, "actualVaryingStageL2MapsCertificate"),
    (57527, 57527, "actualGlobalCutoffStrongConvergenceCertificate"),
    (57534, 57534, "boundedPotentialCompactResolventNoGo"),
    (57539, 57539, "projectionHamiltonianCompactResolventNoGo"),
    (57792, 57795, "closedRaise_le_negativeLowerAdjoint_of_actualHighCutoffBoundaryEqualityResidual"),
    (57802, 57805, "closedLower_le_negativeRaiseAdjoint_of_actualHighCutoffBoundaryEqualityResidual"),
    (59688, 59688, "item2_fullStokes_iff_highCutoffCurvilinearResidual"),
    (59693, 59693, "item2_etaClosedRelation_and_StokesBoundary"),
    (59698, 59698, "item2_highCutoffResidual_closes_fixedPhaseTower"),
    (59705, 59705, "item3_etaDerivativeCoordinateGraph_isClosed"),
    (59710, 59710, "item3_etaCoreCoefficient_eq_genuineCovariantDerivative"),
    (59715, 59715, "item3_etaSingleValued_iff_verticalKernel_isTrivial"),
    (59720, 59720, "item3_verticalVector_forbids_ambientL2Operator"),
    (59727, 59727, "item4_finiteCoordinateDerivative_isClosed"),
    (59733, 59733, "item4_finiteCoordinateH1_RellichCertificate"),
    (59740, 59740, "item5_finiteCoordinateFriedrichsGraph_iff_literal_DstarD_plus_V"),
    (59745, 59745, "item5_finiteCoordinate_literal_DstarD_plus_V_realization"),
    (59752, 59752, "item6_finiteCoordinate_closed_selfAdjoint_compactResolvent"),
    (59757, 59757, "item6_finiteCoordinate_groundBlockSpectrum"),
    (59770, 59770, "item6_actualStage_boundedCompactResolventSurrogate_noGo"),
    (59777, 59777, "item7_lowerFrame_and_energyComparison_imply_excessCoercivity"),
    (59782, 59782, "item7_actualInverseEtaRankOne_isNotLowerFrame"),
    (59787, 59787, "item7_actualOffGround_compactAnalysis_noPositiveLowerFrame"),
    (59793, 59793, "item8_cutoffNegativeOneShift_rightInverse"),
    (59797, 59797, "item8_cutoffNegativeOneShift_leftInverse"),
    (59801, 59801, "item8_cutoffNegativeOneShift_bijective"),
    (59806, 59806, "item8_cutoffNegativeOneResolvent_tendstoStrong"),
    (59812, 59812, "item8_cutoffStrongResolventFirewall"),
    (59816, 59816, "item8_movingOffGroundNontrivial_iff_nonzeroFixedVector"),
    (59821, 59821, "item8_pointwisePositiveConstants_doNotSupplyUniformGap"),
    (59827, 59827, "items2To8_actualMockRS_and_cutoffBoundary"),
)


ACTIVE_REWRITES = (
    ("join_observed_trailing_dot_newlines", 130),
    ("orthogonal_complement_typo_code_only", 12),
    ("neighborhood_notation_typo", 6),
    ("local_ContinuousConstSMul_instance_syntax", 1),
    ("unqualify_resolventSet", 10),
    ("correct_SL_neg_smul_namespace", 3),
    ("qualify_abs_re_le_norm_late_only", 2),
    ("correct_lambda_arrow", 1),
)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git_blob(data: bytes) -> str:
    header = f"blob {len(data)}\0".encode("ascii")
    return hashlib.sha1(header + data).hexdigest()


def _require_hygiene(raw: bytes, *, expected_lf: int, label: str) -> str:
    if raw.startswith(b"\xef\xbb\xbf"):
        raise AssertionError(f"{label}: UTF-8 BOM is forbidden")
    if b"\r" in raw or b"\x00" in raw:
        raise AssertionError(f"{label}: CR/NUL byte invariant violated")
    if not raw.endswith(b"\n") or raw.count(b"\n") != expected_lf:
        raise AssertionError(f"{label}: LF/final-newline invariant violated")
    return raw.decode("utf-8")


def _code_mask(text: str) -> bytearray:
    """Return 1 for code and 0 for nested comments/strings."""
    mask = bytearray([1]) * len(text)
    i = 0
    block_depth = 0
    in_string = False
    escaped = False
    while i < len(text):
        if block_depth:
            mask[i] = 0
            if text.startswith("/-", i):
                mask[i:i + 2] = b"\x00\x00"
                block_depth += 1
                i += 2
                continue
            if text.startswith("-/", i):
                mask[i:i + 2] = b"\x00\x00"
                block_depth -= 1
                i += 2
                continue
            i += 1
            continue
        if in_string:
            mask[i] = 0
            if escaped:
                escaped = False
            elif text[i] == "\\":
                escaped = True
            elif text[i] == '"':
                in_string = False
            i += 1
            continue
        if text.startswith("/-", i):
            mask[i:i + 2] = b"\x00\x00"
            block_depth = 1
            i += 2
            continue
        if text.startswith("--", i):
            end = text.find("\n", i)
            if end < 0:
                end = len(text)
            mask[i:end] = b"\x00" * (end - i)
            i = end
            continue
        if text[i] == '"':
            mask[i] = 0
            in_string = True
        i += 1
    if block_depth or in_string:
        raise AssertionError("unterminated block comment or string")
    return mask


def _trailing_dot_inventory(text: str) -> tuple[tuple[int, int, int], ...]:
    lines = text.splitlines(keepends=True)
    starts: list[int] = []
    offset = 0
    for line in lines:
        starts.append(offset)
        offset += len(line)
    mask = _code_mask(text)
    rows: list[tuple[int, int, int]] = []
    next_identifier = re.compile(r"^([ \t]+)([A-Za-z_][A-Za-z0-9_']*)")
    for index in range(19_999, len(lines) - 1):
        line = lines[index]
        if not line.endswith(".\n"):
            continue
        match = next_identifier.match(lines[index + 1])
        if match is None:
            continue
        dot_offset = starts[index] + len(line) - 2
        member_offset = starts[index + 1] + match.start(2)
        if mask[dot_offset] and mask[member_offset]:
            rows.append((index + 1, len(line) - 1, len(match.group(1))))
    return tuple(rows)


def _validate_inactive_theorems(lines: list[str]) -> None:
    if len(INACTIVE_THEOREM_SPECS) != 47:
        raise AssertionError("inactive theorem inventory must remain exactly 47")
    for start, end, name in INACTIVE_THEOREM_SPECS:
        header = "".join(lines[start - 1:end])
        if re.search(rf"\btheorem\s+{re.escape(name)}\b", header) is None:
            raise AssertionError(f"inactive theorem missing at {start}: {name}")
        if ":=" not in header:
            raise AssertionError(f"inactive theorem terminator missing at {end}: {name}")


def _replace_line_token(
    lines: list[str], line_numbers: Iterable[int], old: str, new: str, label: str
) -> None:
    for line_number in line_numbers:
        line = lines[line_number - 1]
        if line.count(old) != 1:
            raise AssertionError(
                f"{label}: line {line_number} expected one {old!r}, found {line.count(old)}"
            )
        lines[line_number - 1] = line.replace(old, new)


def _forward(raw: bytes) -> bytes:
    if len(raw) != EXPECTED_INPUT_BYTES or sha256(raw) != EXPECTED_INPUT_SHA256:
        raise AssertionError("exact64f input byte/SHA-256 guard failed")
    if git_blob(raw) != EXPECTED_INPUT_GIT_BLOB:
        raise AssertionError("exact64f input Git-blob guard failed")
    text = _require_hygiene(raw, expected_lf=EXPECTED_INPUT_LF, label="input")
    lines = text.splitlines(keepends=True)
    if len(lines) != EXPECTED_INPUT_LF:
        raise AssertionError("input logical-line inventory changed")
    _validate_inactive_theorems(lines)

    inventory = _trailing_dot_inventory(text)
    if len(inventory) != 141:
        raise AssertionError(f"trailing-dot eligible inventory changed: {len(inventory)}")
    observed = tuple(row for row in inventory if row[0] not in TRAILING_DOT_DEFERRED_LINES)
    deferred = frozenset(row[0] for row in inventory if row[0] in TRAILING_DOT_DEFERRED_LINES)
    if observed != TRAILING_DOT_SPECS or deferred != TRAILING_DOT_DEFERRED_LINES:
        raise AssertionError("trailing-dot active/deferred positional seal mismatch")

    if text.count("ᵎ") != 15:
        raise AssertionError("orthogonal-complement total inventory changed")
    if text.count("𝒩") != 6:
        raise AssertionError("bad neighborhood notation inventory changed")
    if text.count("spectrum.resolventSet") != 10:
        raise AssertionError("qualified resolventSet inventory changed")
    if text.count("UpperHalfPlane.SL_neg_smul") != 3:
        raise AssertionError("SL_neg_smul namespace inventory changed")
    if len(re.findall(r"(?<![A-Za-z0-9_.])abs_re_le_norm", text)) != 2:
        raise AssertionError("late unqualified abs_re_le_norm inventory changed")
    if text.count("fun n ⇒") != 1:
        raise AssertionError("bad lambda arrow inventory changed")
    if text.count(LOCAL_INSTANCE_OLD) != 1 or text.count(LOCAL_INSTANCE_NEW) != 0:
        raise AssertionError("local ContinuousConstSMul instance inventory changed")

    for label, line_numbers, old, new in LINE_REWRITES:
        _replace_line_token(lines, line_numbers, old, new, label)

    start = LOCAL_INSTANCE_LINE - 1
    if "".join(lines[start:start + 2]) != LOCAL_INSTANCE_OLD:
        raise AssertionError("local ContinuousConstSMul instance anchor changed")
    lines[start:start + 2] = LOCAL_INSTANCE_NEW.splitlines(keepends=True)

    for line_number, prefix_length, indent_length in reversed(TRAILING_DOT_SPECS):
        index = line_number - 1
        prefix = lines[index]
        continuation = lines[index + 1]
        if len(prefix) - 1 != prefix_length or not prefix.endswith(".\n"):
            raise AssertionError(f"trailing-dot prefix mismatch at line {line_number}")
        indent = " " * indent_length
        if not continuation.startswith(indent) or continuation.startswith(indent + " "):
            raise AssertionError(f"trailing-dot indentation mismatch at line {line_number + 1}")
        lines[index] = prefix[:-1] + continuation[indent_length:]
        del lines[index + 1]

    candidate = "".join(lines).encode("utf-8")
    if len(candidate) != EXPECTED_OUTPUT_BYTES or sha256(candidate) != EXPECTED_OUTPUT_SHA256:
        raise AssertionError("sealed candidate byte/SHA-256 mismatch")
    if git_blob(candidate) != EXPECTED_OUTPUT_GIT_BLOB:
        raise AssertionError("sealed candidate Git-blob mismatch")
    candidate_text = _require_hygiene(
        candidate, expected_lf=EXPECTED_OUTPUT_LF, label="candidate"
    )
    if candidate_text.count("ᵎ") != 3:
        raise AssertionError("three documentation-only orthogonal typos were not preserved")
    if candidate_text.count("𝒩") != 0:
        raise AssertionError("bad neighborhood notation remains")
    if candidate_text.count("spectrum.resolventSet") != 0:
        raise AssertionError("qualified resolventSet remains")
    if candidate_text.count("UpperHalfPlane.SL_neg_smul") != 0:
        raise AssertionError("old SL_neg_smul namespace remains")
    if len(re.findall(r"(?<![A-Za-z0-9_.])abs_re_le_norm", candidate_text)) != 0:
        raise AssertionError("late unqualified abs_re_le_norm remains")
    if candidate_text.count("fun n ⇒") != 0:
        raise AssertionError("bad lambda arrow remains")
    remaining = _trailing_dot_inventory(candidate_text)
    if len(remaining) != 11:
        raise AssertionError("deferred trailing-dot inventory changed after transform")
    return candidate


def _removed_before(original_line: int) -> int:
    active_lines = [row[0] for row in TRAILING_DOT_SPECS]
    return bisect.bisect_left(active_lines, original_line)


def _inverse(raw: bytes) -> bytes:
    if len(raw) != EXPECTED_OUTPUT_BYTES or sha256(raw) != EXPECTED_OUTPUT_SHA256:
        raise AssertionError("sealed candidate byte/SHA-256 guard failed")
    if git_blob(raw) != EXPECTED_OUTPUT_GIT_BLOB:
        raise AssertionError("sealed candidate Git-blob guard failed")
    text = _require_hygiene(raw, expected_lf=EXPECTED_OUTPUT_LF, label="candidate")
    lines = text.splitlines(keepends=True)

    for original_line, prefix_length, indent_length in reversed(TRAILING_DOT_SPECS):
        mapped_line = original_line - _removed_before(original_line)
        index = mapped_line - 1
        joined = lines[index]
        if len(joined) <= prefix_length or joined[prefix_length - 1] != ".":
            raise AssertionError(f"inverse trailing-dot anchor mismatch at mapped line {mapped_line}")
        prefix = joined[:prefix_length]
        continuation = joined[prefix_length:]
        if not continuation or continuation == "\n":
            raise AssertionError(f"inverse trailing-dot continuation missing at {mapped_line}")
        lines[index] = prefix + "\n"
        lines.insert(index + 1, (" " * indent_length) + continuation)

    start = LOCAL_INSTANCE_LINE - 1
    if "".join(lines[start:start + 2]) != LOCAL_INSTANCE_NEW:
        raise AssertionError("inverse local ContinuousConstSMul anchor changed")
    lines[start:start + 2] = LOCAL_INSTANCE_OLD.splitlines(keepends=True)

    for label, line_numbers, old, new in reversed(LINE_REWRITES):
        _replace_line_token(lines, line_numbers, new, old, "inverse_" + label)

    restored = "".join(lines).encode("utf-8")
    if len(restored) != EXPECTED_INPUT_BYTES or sha256(restored) != EXPECTED_INPUT_SHA256:
        raise AssertionError("inverse did not restore exact64f bytes")
    if git_blob(restored) != EXPECTED_INPUT_GIT_BLOB:
        raise AssertionError("inverse did not restore exact64f Git blob")
    _require_hygiene(restored, expected_lf=EXPECTED_INPUT_LF, label="restored")
    return restored


def _audit(mode: str, source: bytes, result: bytes, roundtrip_ok: bool) -> dict[str, object]:
    return {
        "schema": SCHEMA,
        "status": "STATIC_ONLY_NOT_LEAN_EXECUTED",
        "mode": mode,
        "source": {
            "bytes": len(source),
            "lf": source.count(b"\n"),
            "sha256": sha256(source),
            "git_blob": git_blob(source),
        },
        "result": {
            "bytes": len(result),
            "lf": result.count(b"\n"),
            "sha256": sha256(result),
            "git_blob": git_blob(result),
        },
        "active_rewrites": [
            {"label": label, "occurrences": count} for label, count in ACTIVE_REWRITES
        ],
        "active_occurrences_total": sum(count for _, count in ACTIVE_REWRITES),
        "trailing_dot": {
            "eligible": 141,
            "active_observed": 130,
            "deferred_unobserved": 11,
        },
        "inactive_theorem_forwarders": {
            "active": False,
            "count": len(INACTIVE_THEOREM_SPECS),
            "reason": "explicit Prop/result-type validation required",
        },
        "hygiene": {
            "utf8": True,
            "bom": False,
            "cr": False,
            "nul": False,
            "final_lf": True,
            "documentation_orthogonal_typos_preserved": 3,
        },
        "inverse_byte_equal": roundtrip_ok,
        "lean_executed": False,
        "remote_accessed": False,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--mode", choices=("forward", "inverse"), default="forward")
    parser.add_argument("--input", required=True)
    parser.add_argument("--output")
    parser.add_argument("--audit")
    parser.add_argument(
        "--check-only",
        action="store_true",
        help="simulate the transform and exact inverse entirely in memory",
    )
    args = parser.parse_args()

    if not args.check_only and args.output is None:
        parser.error("--output is required unless --check-only is used")
    source = Path(args.input).read_bytes()
    if args.mode == "forward":
        result = _forward(source)
        roundtrip = _inverse(result)
    else:
        result = _inverse(source)
        roundtrip = _forward(result)
    roundtrip_ok = roundtrip == source
    if not roundtrip_ok:
        raise AssertionError("in-memory roundtrip mismatch")
    audit = _audit(args.mode, source, result, roundtrip_ok)

    if args.check_only:
        print(json.dumps(audit, ensure_ascii=False, indent=2, sort_keys=True))
        return
    Path(args.output).write_bytes(result)
    if args.audit is not None:
        Path(args.audit).write_text(
            json.dumps(audit, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
            newline="\n",
        )


if __name__ == "__main__":
    main()
