#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import importlib.util
import json
import os
import re
import sys
from pathlib import Path

ROOT = Path.cwd()
BASE = ROOT / "scripts/fa506_prepare_complex_height_strip_coe.py"
spec = importlib.util.spec_from_file_location("fa506base", BASE)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load {BASE}")
fa506 = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = fa506
spec.loader.exec_module(fa506)

fa466 = fa506.fa466
orig_norm_repairs = fa506.norm_repairs

EXACT_FA506_VARIANT = "explicit_upper_half_plane_coe_projections"
EXACT_FA507_VARIANT = "fragment_only_cumulative_abc_2840_2888"

REQUIRED_FA506_SOURCE_SHA256 = (
    "fbf76ffa75885c76492c6795ac907d47693d964d30043fd8cced93ca71719611"
)
REQUIRED_FA506_SOURCE_BYTES = 2_700_268
REQUIRED_FA506_SOURCE_LINES = 60_541
EXPECTED_CANDIDATE_SHA256 = (
    "bf4ea05a41edacf0aa9b7d51496d52003bddc45b5cc3d743e0b06fd7aaa2201b"
)
EXPECTED_CANDIDATE_BYTES = 2_702_238
EXPECTED_CANDIDATE_LINES = 60_573
EXPECTED_DECLARATION_COUNT = 4_397

FA505_SOURCE_SHA256 = (
    "c56e320e31dbb4c2d80a7b6c05e3417b9683fe982a9f006bbd6166add95ea9e7"
)
FA505_SOURCE_BYTES = 2_700_162
FA505_SOURCE_LINES = 60_539
FA505_PREVIOUS_FRONTIER = "integral_selectedHeightGraphDensity_stripTail_eq_iterated"
FA505_PREVIOUS_FRONTIER_INDEX = 2_835
FA505_FIRST_ERROR = "complex_image_heightStrip_eq_coe_image_selectedBaseCuspStrip"
FA505_FIRST_ERROR_INDEX = 2_839

FA506_PREVIOUS_FRONTIER = FA505_FIRST_ERROR
FA506_PREVIOUS_FRONTIER_INDEX = FA505_FIRST_ERROR_INDEX
FA506_FIRST_ERROR = "selectedBaseCuspStrip_subset_fd"
FA506_FIRST_ERROR_INDEX = 2_840

TARGETS: tuple[tuple[str, int, str], ...] = (
    ("selectedBaseCuspStrip_subset_fd", 2_840, "A"),
    (
        "ambientFixedPhaseEuclideanGraphDensity_integrableOn_chosenCarrier",
        2_847,
        "A",
    ),
    (
        "integral_selectedHeightGraphDensity_strip_eq_selectedImage",
        2_849,
        "A",
    ),
    ("weighted_coordinate_energy_le_coreMap", 2_856, "B"),
    ("coreGraphTraceEstimate_iff_three_coordinates", 2_866, "B"),
    ("completedSelectedCuspTrace", 2_867, "B"),
    ("completedSelectedCuspTrace_core", 2_868, "B"),
    ("completedSelectedCuspTrace_norm_apply_le", 2_869, "B"),
    ("completedSelectedCuspTrace_opNorm_le", 2_870, "B"),
    (
        "completedSelectedCuspTraceUniformFamily_tendsto_zero",
        2_873,
        "C",
    ),
    ("completedSelectedCuspTraceFamily_tendsto_zero", 2_883, "C"),
    ("inner_trace_tendsto_zero", 2_888, "C"),
)
TARGET_INDEX = {name: index for name, index, _group in TARGETS}
TARGET_GROUP = {name: group for name, _index, group in TARGETS}
TARGET_NAMES = tuple(name for name, _index, _group in TARGETS)

_DECL_START = re.compile(
    r"(?m)^(?:protected\s+|private\s+|noncomputable\s+)?"
    r"(?:theorem|lemma|def|abbrev|instance|structure|class)\s+"
    r"(?P<name>[^\s(:]+)"
)

_FORBIDDEN = {
    "sorry": re.compile(r"\bsorry\b"),
    "admit": re.compile(r"\badmit\b"),
    "new_global_axiom": re.compile(r"(?m)^\s*axiom\b"),
    "unsafe": re.compile(r"\bunsafe\b"),
    "native_decide": re.compile(r"\bnative_decide\b"),
    "Lean.ofReduceBool": re.compile(r"\bLean\.ofReduceBool\b"),
}

CANONICAL_INSTANCE_PREAMBLE = """  letI : Module ℂ (InverseEtaFixedPhaseCore n) :=
    DefinitionOneSobolev.FixedPhaseGraphCompletion.fixedPhaseGraphCoreModule n
  letI : AddCommGroup (InverseEtaFixedPhaseCore n) :=
    DefinitionOneSobolev.FixedPhaseGraphCompletion.fixedPhaseGraphCoreAddCommGroup n"""

REPLACEMENTS: tuple[tuple[str, str, str, str], ...] = (
    (
        "selectedBaseCuspStrip_subset_fd",
        "A",
        "    simp only [Complex.normSq_apply]\n"
        "    nlinarith [sq_nonneg z.re, sq_nonneg (z.im - 1)]",
        "    simp only [Complex.normSq_apply, UpperHalfPlane.coe_re,\n"
        "      UpperHalfPlane.coe_im]\n"
        "    nlinarith [sq_nonneg z.re, sq_nonneg (z.im - 1)]",
    ),
    (
        "ambientFixedPhaseEuclideanGraphDensity_integrableOn_chosenCarrier",
        "A",
        """:= by
  change Integrable (ambientFixedPhaseEuclideanGraphDensity n u)
    ambientChosenEuclideanMeasure
  rw [← map_chosenEuclideanCarrierMeasure,
    UpperHalfPlane.measurableEmbedding_coe.integrable_map_iff]
  simpa only [Function.comp_apply,
    ambientFixedPhaseEuclideanGraphDensity_coe] using
      fixedPhaseEuclideanGraphDensity_integrable n u""",
        """:= by
  change Integrable (ambientFixedPhaseEuclideanGraphDensity n u)
    ambientChosenEuclideanMeasure
  rw [← map_chosenEuclideanCarrierMeasure,
    UpperHalfPlane.measurableEmbedding_coe.integrable_map_iff]
  have hFunction :
      ambientFixedPhaseEuclideanGraphDensity n u ∘ UpperHalfPlane.coe =
        fixedPhaseEuclideanGraphDensity n u := by
    funext z
    exact ambientFixedPhaseEuclideanGraphDensity_coe n u z
  rw [hFunction]
  exact fixedPhaseEuclideanGraphDensity_integrable n u""",
    ),
    (
        "integral_selectedHeightGraphDensity_strip_eq_selectedImage",
        "A",
        """    rintro _w ⟨z, _hz, rfl⟩
    rw [selectedCosetAmbientMap_coe]
    simp only [G, selectedHeightBasePoint_re_im,
      ambientFixedPhaseEuclideanGraphDensity_coe]""",
        """    rintro _w ⟨z, _hz, rfl⟩
    dsimp only [G]
    rw [selectedCosetAmbientMap_coe]
    simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im,
      selectedHeightBasePoint_re_im,
      ambientFixedPhaseEuclideanGraphDensity_coe]""",
    ),
    (
        "weighted_coordinate_energy_le_coreMap",
        "B",
        ":= by\n  have hsquare :",
        f":= by\n{CANONICAL_INSTANCE_PREAMBLE}\n  have hsquare :",
    ),
    (
        "coreGraphTraceEstimate_iff_three_coordinates",
        "B",
        ":= by\n  constructor",
        f":= by\n{CANONICAL_INSTANCE_PREAMBLE}\n  constructor",
    ),
    (
        "completedSelectedCuspTrace",
        "B",
        """:=
  (selectedCuspCoreTrace n q Y).extendOfNorm (coreMap n)""",
        """:= by
  letI : Module ℂ (InverseEtaFixedPhaseCore n) :=
    DefinitionOneSobolev.FixedPhaseGraphCompletion.fixedPhaseGraphCoreModule n
  letI : AddCommGroup (InverseEtaFixedPhaseCore n) :=
    DefinitionOneSobolev.FixedPhaseGraphCompletion.fixedPhaseGraphCoreAddCommGroup n
  exact (selectedCuspCoreTrace n q Y).extendOfNorm (coreMap n)""",
    ),
    (
        "completedSelectedCuspTrace_core",
        "B",
        ":= by\n  exact LinearMap.extendOfNorm_eq",
        f":= by\n{CANONICAL_INSTANCE_PREAMBLE}\n  exact LinearMap.extendOfNorm_eq",
    ),
    (
        "completedSelectedCuspTrace_norm_apply_le",
        "B",
        ":= by\n  exact LinearMap.norm_extendOfNorm_apply_le",
        f":= by\n{CANONICAL_INSTANCE_PREAMBLE}\n  exact LinearMap.norm_extendOfNorm_apply_le",
    ),
    (
        "completedSelectedCuspTrace_opNorm_le",
        "B",
        ":= by\n  exact LinearMap.opNorm_extendOfNorm_le",
        f":= by\n{CANONICAL_INSTANCE_PREAMBLE}\n  exact LinearMap.opNorm_extendOfNorm_le",
    ),
    (
        "completedSelectedCuspTraceUniformFamily_tendsto_zero",
        "C",
        "        field_simp [ne_of_gt hCOne]\n        ring",
        "        field_simp [ne_of_gt hCOne] <;> ring",
    ),
    (
        "completedSelectedCuspTraceFamily_tendsto_zero",
        "C",
        """    ((completedSelectedCuspTraceFamily_opNorm_tendsto_zero
      n q C hC hEstimate hCZero).mul_const ‖x‖)""",
        """    (by
      simpa only [zero_mul] using
        ((completedSelectedCuspTraceFamily_opNorm_tendsto_zero
          n q C hC hEstimate hCZero).mul_const ‖x‖))""",
    ),
    (
        "inner_trace_tendsto_zero",
        "C",
        "  simpa using hT.inner hU",
        "  simpa using Filter.Tendsto.inner (𝕜 := ℂ) hT hU",
    ),
)


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_text(text: str) -> str:
    return sha256_bytes(text.encode("utf-8"))


def declarations(text: str) -> list[re.Match[str]]:
    return list(_DECL_START.finditer(text))


def declaration_sequence(text: str) -> list[str]:
    return [match.group("name") for match in declarations(text)]


def bounds(text: str, declaration: str) -> tuple[int, int, int]:
    starts = declarations(text)
    hits = [i for i, match in enumerate(starts) if match.group("name") == declaration]
    if len(hits) != 1:
        raise RuntimeError(f"expected one {declaration}, found {len(hits)}")
    i = hits[0]
    end = starts[i + 1].start() if i + 1 < len(starts) else len(text)
    return starts[i].start(), end, i


def header(region: str) -> str:
    marker = region.find(":=")
    if marker < 0:
        raise RuntimeError("target header has no :=")
    return region[: marker + 2]


def forbidden_counts(text: str) -> dict[str, int]:
    return {name: len(pattern.findall(text)) for name, pattern in _FORBIDDEN.items()}


def mask_lean_comments_and_strings(text: str) -> str:
    """Preserve code/newlines while masking nested comments and string payloads."""
    output: list[str] = []
    i = 0
    block_depth = 0
    in_line_comment = False
    in_string = False
    escaped = False
    while i < len(text):
        char = text[i]
        following = text[i + 1] if i + 1 < len(text) else ""
        if in_line_comment:
            if char == "\n":
                in_line_comment = False
                output.append("\n")
            else:
                output.append(" ")
            i += 1
            continue
        if block_depth:
            if char == "/" and following == "-":
                output.extend((" ", " "))
                block_depth += 1
                i += 2
            elif char == "-" and following == "/":
                output.extend((" ", " "))
                block_depth -= 1
                i += 2
            else:
                output.append("\n" if char == "\n" else " ")
                i += 1
            continue
        if in_string:
            output.append("\n" if char == "\n" else " ")
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
            i += 1
            continue
        if char == "-" and following == "-":
            output.extend((" ", " "))
            in_line_comment = True
            i += 2
        elif char == "/" and following == "-":
            output.extend((" ", " "))
            block_depth = 1
            i += 2
        elif char == '"':
            output.append(" ")
            in_string = True
            escaped = False
            i += 1
        else:
            output.append(char)
            i += 1
    if block_depth or in_string:
        raise RuntimeError("FA507 source has unterminated comment or string")
    return "".join(output)


def executable_forbidden_counts(text: str) -> dict[str, int]:
    return forbidden_counts(mask_lean_comments_and_strings(text))


def require_env(name: str, expected: str) -> None:
    actual = os.environ.get(name)
    if actual != expected:
        raise RuntimeError(f"FA507 requires {name}={expected}, got {actual!r}")


def require_positive_decimal(name: str) -> int:
    actual = os.environ.get(name, "")
    if re.fullmatch(r"[1-9][0-9]*", actual) is None:
        raise RuntimeError(f"FA507 requires positive decimal {name}, got {actual!r}")
    return int(actual)


def require_sha(name: str, width: int) -> str:
    actual = os.environ.get(name, "")
    if re.fullmatch(rf"[0-9a-f]{{{width}}}", actual) is None or actual == "0" * width:
        raise RuntimeError(f"FA507 requires nonzero {width}-hex {name}, got {actual!r}")
    return actual


def require_artifact_name(name: str) -> str:
    actual = os.environ.get(name, "")
    if (
        not actual
        or "PENDING" in actual.upper()
        or "UNVERIFIED" in actual.upper()
        or re.fullmatch(r"[A-Za-z0-9_.-]+", actual) is None
    ):
        raise RuntimeError(f"FA507 requires hydrated artifact name {name}, got {actual!r}")
    return actual


def require_artifact_digest(name: str) -> str:
    actual = os.environ.get(name, "")
    if re.fullmatch(r"sha256:[0-9a-f]{64}", actual) is None:
        raise RuntimeError(f"FA507 requires sha256 artifact digest {name}, got {actual!r}")
    return actual


def require_direct_evidence(
    prefix: str,
    source_sha256: str,
    source_bytes: int,
    source_lines: int,
    previous_frontier: str,
    previous_index: int,
    first_error: str,
    first_error_index: int,
) -> dict[str, object]:
    require_env(f"{prefix}_EVIDENCE_STATUS", "VERIFIED")
    require_env(f"{prefix}_EVIDENCE_LIVE_ATTESTED", "VERIFIED")
    run_id = require_positive_decimal(f"{prefix}_EVIDENCE_RUN_ID")
    job_id = require_positive_decimal(f"{prefix}_EVIDENCE_JOB_ID")
    head_sha = require_sha(f"{prefix}_EVIDENCE_HEAD_SHA", 40)
    artifact_id = require_positive_decimal(f"{prefix}_EVIDENCE_ARTIFACT_ID")
    artifact_name = require_artifact_name(f"{prefix}_EVIDENCE_ARTIFACT_NAME")
    artifact_size = require_positive_decimal(f"{prefix}_EVIDENCE_ARTIFACT_SIZE")
    artifact_digest = require_artifact_digest(f"{prefix}_EVIDENCE_ARTIFACT_DIGEST")
    require_env(f"{prefix}_EVIDENCE_SOURCE_SHA256", source_sha256)
    require_env(f"{prefix}_EVIDENCE_SOURCE_BYTES", str(source_bytes))
    require_env(f"{prefix}_EVIDENCE_SOURCE_LINES", str(source_lines))
    require_env(f"{prefix}_CLASSIFICATION", "LEAN_FAILURE")
    require_env(f"{prefix}_INFRA_REASONS", "[]")
    require_env(f"{prefix}_MOCK2_EXIT", "0")
    require_env(f"{prefix}_MOCK2_ADVANCED_EXIT", "0")
    require_env(f"{prefix}_FA_EXIT", "1")
    require_env(f"{prefix}_PREVIOUS_FRONTIER_DECLARATION", previous_frontier)
    require_env(f"{prefix}_PREVIOUS_FRONTIER_INDEX", str(previous_index))
    require_env(f"{prefix}_FIRST_ERROR_DECLARATION", first_error)
    require_env(f"{prefix}_FIRST_ERROR_INDEX", str(first_error_index))
    first_line = require_positive_decimal(f"{prefix}_FIRST_ERROR_LINE")
    first_col = require_positive_decimal(f"{prefix}_FIRST_ERROR_COL")
    return {
        "status": "VERIFIED",
        "run_id": run_id,
        "job_id": job_id,
        "head_sha": head_sha,
        "artifact_id": artifact_id,
        "artifact_name": artifact_name,
        "artifact_size": artifact_size,
        "artifact_digest": artifact_digest,
        "source_sha256": source_sha256,
        "source_bytes": source_bytes,
        "source_lines": source_lines,
        "previous_frontier_declaration": previous_frontier,
        "previous_frontier_index": previous_index,
        "first_error_line": first_line,
        "first_error_col": first_col,
        "first_error_declaration": first_error,
        "first_error_index": first_error_index,
    }


def require_live_attestation(evidence: dict[str, dict[str, object]]) -> dict[str, object]:
    require_env("FA507_UPSTREAM_ATTESTATION_PATH", "/tmp/fa507-upstream-attestation.json")
    path = Path("/tmp/fa507-upstream-attestation.json")
    if not path.is_file():
        raise RuntimeError(f"FA507 live attestation is missing: {path}")
    expected_sha = require_sha("FA507_UPSTREAM_ATTESTATION_SHA256", 64)
    data = path.read_bytes()
    actual_sha = sha256_bytes(data)
    if actual_sha != expected_sha:
        raise RuntimeError(
            f"FA507 live attestation SHA mismatch: {actual_sha}; expected {expected_sha}"
        )
    payload = json.loads(data)
    if payload.get("schema") != "fa507-upstream-evidence-v1":
        raise RuntimeError("FA507 live attestation schema mismatch")
    if payload.get("all_checks_passed") is not True:
        raise RuntimeError("FA507 live attestation did not pass all checks")
    for prefix in ("FA505", "FA506"):
        key = prefix.lower()
        attested = payload.get(key, {})
        required = evidence[prefix]
        for field in ("run_id", "job_id", "head_sha", "artifact_id"):
            if attested.get(field) != required[field]:
                raise RuntimeError(
                    f"FA507 attestation {key}.{field} mismatch: "
                    f"{attested.get(field)!r} != {required[field]!r}"
                )
        if attested.get("all_checks_passed") is not True:
            raise RuntimeError(f"FA507 attestation {key} checks did not all pass")
    return {
        "path": str(path),
        "sha256": actual_sha,
        "schema": payload["schema"],
        "all_checks_passed": True,
    }


def apply_cumulative_repairs(text: str) -> tuple[str, dict[str, object]]:
    source_bytes = len(text.encode("utf-8"))
    source_lines = len(text.splitlines())
    source_sha = sha256_text(text)
    if (
        source_sha != REQUIRED_FA506_SOURCE_SHA256
        or source_bytes != REQUIRED_FA506_SOURCE_BYTES
        or source_lines != REQUIRED_FA506_SOURCE_LINES
    ):
        raise RuntimeError(
            "FA507 exact FA506 input mismatch: "
            f"sha={source_sha}, bytes={source_bytes}, lines={source_lines}"
        )

    before_sequence = declaration_sequence(text)
    if len(before_sequence) != EXPECTED_DECLARATION_COUNT:
        raise RuntimeError(
            f"FA507 declaration count drift: {len(before_sequence)}; "
            f"expected {EXPECTED_DECLARATION_COUNT}"
        )
    for name, expected_index, _group in TARGETS:
        _start, _end, actual_index = bounds(text, name)
        if actual_index != expected_index:
            raise RuntimeError(
                f"FA507 target index drift for {name}: {actual_index}; "
                f"expected {expected_index}"
            )

    before_regions: list[str] = []
    before_headers: dict[str, str] = {}
    starts_before = declarations(text)
    for match_index, _name in enumerate(before_sequence):
        start = starts_before[match_index].start()
        end = (
            starts_before[match_index + 1].start()
            if match_index + 1 < len(starts_before)
            else len(text)
        )
        before_regions.append(text[start:end])
    for name in TARGET_NAMES:
        before_headers[name] = header(before_regions[TARGET_INDEX[name]])

    first_old = REPLACEMENTS[0][2]
    last_old = REPLACEMENTS[-1][2]
    first_old_pos = text.find(first_old)
    last_old_pos = text.find(last_old)
    if first_old_pos < 0 or last_old_pos < 0:
        raise RuntimeError("FA507 boundary fragments are missing")
    preserved_prefix = text[:first_old_pos]
    preserved_suffix = text[last_old_pos + len(last_old) :]

    candidate = text
    replacement_audit: list[dict[str, object]] = []
    for declaration, group, old, new in REPLACEMENTS:
        start, end, actual_index = bounds(candidate, declaration)
        region = candidate[start:end]
        counts = {
            "old_target_before": region.count(old),
            "old_global_before": candidate.count(old),
            "new_target_before": region.count(new),
            "new_global_before": candidate.count(new),
        }
        if counts["old_target_before"] != 1 or counts["new_target_before"] != 0:
            raise RuntimeError(
                f"FA507 {declaration} declaration-local old/new counts were "
                f"{counts['old_target_before']}/{counts['new_target_before']}, "
                "expected 1/0"
            )
        new_region = region.replace(old, new, 1)
        mode = "checked_fragment"
        candidate = candidate[:start] + new_region + candidate[end:]
        replacement_audit.append(
            {
                "group": group,
                "declaration": declaration,
                "declaration_index": actual_index,
                "mode": mode,
                **counts,
                "old_sha256": sha256_text(old),
                "new_sha256": sha256_text(new),
            }
        )

    after_sequence = declaration_sequence(candidate)
    if before_sequence != after_sequence:
        raise RuntimeError("FA507 declaration sequence drift")

    starts_after = declarations(candidate)
    after_regions: list[str] = []
    for match_index, _name in enumerate(after_sequence):
        start = starts_after[match_index].start()
        end = (
            starts_after[match_index + 1].start()
            if match_index + 1 < len(starts_after)
            else len(candidate)
        )
        after_regions.append(candidate[start:end])

    changed_indices = [
        i
        for i, (before_region, after_region) in enumerate(
            zip(before_regions, after_regions, strict=True)
        )
        if before_region != after_region
    ]
    changed = [before_sequence[i] for i in changed_indices]
    if changed != list(TARGET_NAMES):
        raise RuntimeError(
            f"FA507 changed declaration set/order drift: {changed}; "
            f"expected {list(TARGET_NAMES)}"
        )

    before_skeleton_regions = list(before_regions)
    after_skeleton_regions = list(after_regions)
    for replacement_number, (declaration, _group, old, new) in enumerate(
        REPLACEMENTS
    ):
        index = TARGET_INDEX[declaration]
        marker = f"\x00FA507_REPLACEMENT_{replacement_number:02d}\x00"
        if before_skeleton_regions[index].count(old) != 1:
            raise RuntimeError(f"FA507 before-skeleton mismatch: {declaration}")
        if after_skeleton_regions[index].count(new) != 1:
            raise RuntimeError(f"FA507 after-skeleton mismatch: {declaration}")
        before_skeleton_regions[index] = before_skeleton_regions[index].replace(
            old, marker, 1
        )
        after_skeleton_regions[index] = after_skeleton_regions[index].replace(
            new, marker, 1
        )
    before_skeleton = "".join(before_skeleton_regions)
    after_skeleton = "".join(after_skeleton_regions)
    if before_skeleton != after_skeleton:
        raise RuntimeError(
            "FA507 immutable source skeleton drift outside selected fragments"
        )

    header_audit: dict[str, dict[str, object]] = {}
    for name in TARGET_NAMES:
        before_header = before_headers[name]
        after_header = header(after_regions[TARGET_INDEX[name]])
        if before_header != after_header:
            raise RuntimeError(f"FA507 declaration header drift: {name}")
        header_audit[name] = {
            "declaration_index": TARGET_INDEX[name],
            "group": TARGET_GROUP[name],
            "header_sha256": sha256_text(before_header),
            "preserved": True,
        }

    first_new = REPLACEMENTS[0][3]
    last_new = REPLACEMENTS[-1][3]
    first_new_pos = candidate.find(first_new)
    last_new_pos = candidate.find(last_new)
    if (
        first_new_pos < 0
        or last_new_pos < 0
        or candidate[:first_new_pos] != preserved_prefix
        or candidate[last_new_pos + len(last_new) :] != preserved_suffix
    ):
        raise RuntimeError("FA507 source prefix/suffix drift")

    forbidden_before = forbidden_counts(text)
    forbidden_after = forbidden_counts(candidate)
    if forbidden_before != forbidden_after:
        raise RuntimeError(
            f"FA507 forbidden-token drift: {forbidden_before} -> {forbidden_after}"
        )
    executable_forbidden_before = executable_forbidden_counts(text)
    executable_forbidden_after = executable_forbidden_counts(candidate)
    if executable_forbidden_before != executable_forbidden_after:
        raise RuntimeError(
            "FA507 executable forbidden-token drift: "
            f"{executable_forbidden_before} -> {executable_forbidden_after}"
        )

    candidate_sha = sha256_text(candidate)
    candidate_bytes = len(candidate.encode("utf-8"))
    candidate_lines = len(candidate.splitlines())
    if (
        candidate_sha != EXPECTED_CANDIDATE_SHA256
        or candidate_bytes != EXPECTED_CANDIDATE_BYTES
        or candidate_lines != EXPECTED_CANDIDATE_LINES
    ):
        raise RuntimeError(
            "FA507 candidate identity drift: "
            f"sha={candidate_sha}, bytes={candidate_bytes}, lines={candidate_lines}"
        )

    audit: dict[str, object] = {
        "input_source_sha256": source_sha,
        "input_source_bytes": source_bytes,
        "input_source_lines": source_lines,
        "candidate_source_sha256": candidate_sha,
        "candidate_source_bytes": candidate_bytes,
        "candidate_source_lines": candidate_lines,
        "declaration_count": len(before_sequence),
        "declaration_sequence_sha256": sha256_text("\n".join(before_sequence)),
        "declaration_sequence_preserved": True,
        "changed_declarations": changed,
        "changed_declaration_indices": changed_indices,
        "changed_declarations_exact": True,
        "immutable_source_skeleton_sha256": sha256_text(before_skeleton),
        "immutable_source_skeleton_bytes": len(before_skeleton.encode("utf-8")),
        "immutable_source_skeleton_preserved": True,
        "doc_comments_preserved": True,
        "attributes_preserved": True,
        "target_headers": header_audit,
        "all_target_headers_preserved": True,
        "claims_preserved": True,
        "source_prefix_sha256": sha256_text(preserved_prefix),
        "source_prefix_bytes": len(preserved_prefix.encode("utf-8")),
        "source_prefix_preserved": True,
        "source_suffix_sha256": sha256_text(preserved_suffix),
        "source_suffix_bytes": len(preserved_suffix.encode("utf-8")),
        "source_suffix_preserved": True,
        "replacement_count": len(REPLACEMENTS),
        "replacement_audit": replacement_audit,
        "forbidden_counts_before": forbidden_before,
        "forbidden_counts_after": forbidden_after,
        "forbidden_counts_preserved": True,
        "executable_forbidden_counts_before": executable_forbidden_before,
        "executable_forbidden_counts_after": executable_forbidden_after,
        "executable_forbidden_counts_preserved": True,
    }
    return candidate, audit


def norm_repairs(text: str):
    require_env("FA506_VARIANT", EXACT_FA506_VARIANT)
    require_env("FA507_VARIANT", EXACT_FA507_VARIANT)

    evidence = {
        "FA505": require_direct_evidence(
            "FA505",
            FA505_SOURCE_SHA256,
            FA505_SOURCE_BYTES,
            FA505_SOURCE_LINES,
            FA505_PREVIOUS_FRONTIER,
            FA505_PREVIOUS_FRONTIER_INDEX,
            FA505_FIRST_ERROR,
            FA505_FIRST_ERROR_INDEX,
        ),
        "FA506": require_direct_evidence(
            "FA506",
            REQUIRED_FA506_SOURCE_SHA256,
            REQUIRED_FA506_SOURCE_BYTES,
            REQUIRED_FA506_SOURCE_LINES,
            FA506_PREVIOUS_FRONTIER,
            FA506_PREVIOUS_FRONTIER_INDEX,
            FA506_FIRST_ERROR,
            FA506_FIRST_ERROR_INDEX,
        ),
    }
    attestation = require_live_attestation(evidence)

    text, repairs = orig_norm_repairs(text)
    candidate, audit = apply_cumulative_repairs(text)
    return candidate, repairs + [
        {
            "declaration": "FA507 cumulative frontier 2840-2888",
            "strategy": EXACT_FA507_VARIANT,
            "groups": {
                "A": [name for name, _index, group in TARGETS if group == "A"],
                "B": [name for name, _index, group in TARGETS if group == "B"],
                "C": [name for name, _index, group in TARGETS if group == "C"],
            },
            "target_declarations": list(TARGET_NAMES),
            "target_declaration_indices": [index for _name, index, _group in TARGETS],
            "later_repair_count": 0,
            "max_errors": 32,
            "required_fa505_evidence": evidence["FA505"],
            "required_fa506_evidence": evidence["FA506"],
            "live_attestation": attestation,
            **audit,
        }
    ]


fa466.norm_repairs = norm_repairs

if __name__ == "__main__":
    fa466.main()
