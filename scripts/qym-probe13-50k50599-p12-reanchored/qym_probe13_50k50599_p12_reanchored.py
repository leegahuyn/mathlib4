#!/usr/bin/env python3
"""Exact-Probe12 direct repairs for QYM lines 50000--50599.

This package selects only three high-confidence local producer/API repairs:
the two removed subtype-measure convenience APIs are expanded through the
current generic ``Measure.map_apply``/``Measure.comap_apply`` interface, and a
Probe9 Petersson-definiteness refinement uses the still-compiled
``inner_self_eq_norm_sq_to_K`` producer.

The effective-quotient versus literal-quotient inverse-eta bundle cluster is
not patched.  It needs a validated quotient equivalence, a pulled-back bundle,
and measurable/topological transports; guessing a coercion would make the
theorem statements ill-typed.  The exact blocker partition is recorded below.

The transformer is activation-disabled, byte-locked, exact-counted,
reversible, trust0, and collision-audited against the active Probe12 helpers,
the exact-Probe12 Probe12 siblings, and the active Probe9 owner refined here.
It never invokes Lean, Lake, Git, a network, or a remote service, and never
mutates repository sources.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from types import ModuleType


sys.dont_write_bytecode = True

SCHEMA = "qym-probe13-50k50599-p12-reanchored-v1"
INPUT_SHA256 = "4a123f69912bd7ce2ab070433f8cad0ecc284652a9cbab634def1936e9037212"
INPUT_GIT_BLOB = "76dd931638b9a6ad50ee764c65cd14489e8be310"
INPUT_BYTES = 2_936_558
INPUT_LF = 62_068
LOG_SHA256 = "62ce7c1b4ec23a23d690c64d49e45901faec66ff751d86e314e669b8c876c398"
HEADERS_SHA256 = "0cebf8d7bbcb923165a13f68f2afbbef1843bb26d77e072252c570b8e77b0dd9"
DIAGNOSTICS_SHA256 = "16b69f25e53f28d028cbefca21d5401e25dbfaa2847bdfdc8f7532034690ca23"

# Frozen from the single deterministic bootstrap projection.
OUTPUT_SHA256 = "9fd2c7c432af883647c3c5113c8ae13454d40c147148428db54c471a91ba1e84"
OUTPUT_GIT_BLOB = "ca9def9938791d2dce4f12b2e3b81370390f9026"
OUTPUT_BYTES = 2_936_991
OUTPUT_LF = 62_079


def sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def git_blob(raw: bytes) -> str:
    return hashlib.sha1(f"blob {len(raw)}\0".encode("ascii") + raw).hexdigest()


@dataclass(frozen=True)
class Header:
    line: int
    column: int
    message: str
    code: str | None = None


@dataclass(frozen=True)
class Rule:
    label: str
    old: str
    new: str
    headers: tuple[Header, ...]
    rationale: str
    precedent: str
    occurrences: int = 1


RULES: tuple[Rule, ...] = (
    Rule(
        "map_stage_comap_expand_current_generic_api",
        "theorem map_actualStageMeasure_subtypeVal (Y : ℝ) :\n"
        "    (actualStageMeasure Y).map\n"
        "        (Subtype.val : QYM.FullCertification.P2IntrinsicTruncatedQuotientExtension.X Y -> Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.GammaTwoQuotient) =\n"
        "      actualQuotientHyperbolicMeasure.restrict (QYM.FullCertification.P2IntrinsicTruncatedQuotientExtension.XSet Y) := by\n"
        "  unfold actualStageMeasure\n"
        "  exact Measure.map_comap_subtype_coe\n"
        "    (QYM.FullCertification.P2IntrinsicTruncatedQuotientExtension.XSet_measurable Y) actualQuotientHyperbolicMeasure\n",
        "theorem map_actualStageMeasure_subtypeVal (Y : ℝ) :\n"
        "    (actualStageMeasure Y).map\n"
        "        (Subtype.val : QYM.FullCertification.P2IntrinsicTruncatedQuotientExtension.X Y -> Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.GammaTwoQuotient) =\n"
        "      actualQuotientHyperbolicMeasure.restrict (QYM.FullCertification.P2IntrinsicTruncatedQuotientExtension.XSet Y) := by\n"
        "  ext s hs\n"
        "  rw [Measure.map_apply\n"
        "      (actualStageSubtype_measurableEmbedding Y).measurable hs,\n"
        "    actualStageMeasure,\n"
        "    Measure.comap_apply _\n"
        "      (actualStageSubtype_measurableEmbedding Y).injective\n"
        "      (actualStageSubtype_measurableEmbedding Y).measurableSet_image'\n"
        "      _ ((actualStageSubtype_measurableEmbedding Y).measurable hs),\n"
        "    Measure.restrict_apply hs, Set.image_preimage_eq_inter_range,\n"
        "    Subtype.range_coe]\n",
        (
            Header(
                50161,
                8,
                "Unknown constant `MeasureTheory.Measure.map_comap_subtype_coe`",
                "lean.unknownIdentifier",
            ),
        ),
        "Expand the deleted subtype convenience theorem by extensionality, map evaluation, generic comap evaluation through the existing measurable embedding, and the subtype range identity.",
        "Exact Probe12 already compiles the same Measure.comap_apply argument at source lines 51885--51888; Measure.map_apply and Measure.restrict_apply are compiled repeatedly in the same authority source.",
    ),
    Rule(
        "stage_comap_univ_expand_current_generic_api",
        "theorem actualStageMeasure_univ (Y : ℝ) :\n"
        "    actualStageMeasure Y Set.univ =\n"
        "      actualQuotientHyperbolicMeasure (QYM.FullCertification.P2IntrinsicTruncatedQuotientExtension.XSet Y) := by\n"
        "  rw [actualStageMeasure,\n"
        "    Measure.comap_subtype_coe_apply\n"
        "      (QYM.FullCertification.P2IntrinsicTruncatedQuotientExtension.XSet_measurable Y) actualQuotientHyperbolicMeasure]\n"
        "  simp only [Set.image_univ, Subtype.range_coe]\n",
        "theorem actualStageMeasure_univ (Y : ℝ) :\n"
        "    actualStageMeasure Y Set.univ =\n"
        "      actualQuotientHyperbolicMeasure (QYM.FullCertification.P2IntrinsicTruncatedQuotientExtension.XSet Y) := by\n"
        "  rw [actualStageMeasure,\n"
        "    Measure.comap_apply _\n"
        "      (actualStageSubtype_measurableEmbedding Y).injective\n"
        "      (actualStageSubtype_measurableEmbedding Y).measurableSet_image'\n"
        "      _ MeasurableSet.univ]\n"
        "  simp only [Set.image_univ, Subtype.range_coe]\n",
        (
            Header(
                50170,
                4,
                "Unknown constant `MeasureTheory.Measure.comap_subtype_coe_apply`",
                "lean.unknownIdentifier",
            ),
            Header(50168, 110, "unsolved goals"),
        ),
        "Evaluate the subtype comap on univ through the generic comap theorem and the already-proved measurable embedding.",
        "Exact Probe12 source lines 51885--51888 contain the identical generic comap producer and close successfully in the authoritative run.",
    ),
    Rule(
        "petersson_definiteness_use_toK_norm_square",
        "  change (inner ℂ u u).re = 0 ↔ u = 0\n"
        "  rw [inner_self_eq_norm_sq (𝕜 := ℂ),\n"
        "    sq_eq_zero_iff, norm_eq_zero]\n",
        "  unfold actualStagePeterssonInner\n"
        "  rw [inner_self_eq_norm_sq_to_K]\n"
        "  simp only [Complex.ofReal_pow, Complex.ofReal_re,\n"
        "    sq_eq_zero_iff, norm_eq_zero]\n",
        (
            Header(
                50388,
                6,
                "Tactic `rewrite` failed: Did not find an occurrence of the pattern",
            ),
        ),
        "Use the field-valued inner-self norm-square theorem, then reduce the concrete Complex real cast and norm-square zero equivalence.",
        "Exact Probe12 line 26188 compiles inner_self_eq_norm_sq_to_K followed by simp for the same RCLike.re(inner self) shape; lines 56517 and 58826 also compile the same producer for Complex.",
    ),
    Rule(
        "actual_stage_high_height_make_goal_explicit",
        "  let h : QYM.FullCertification.P2CuspCollarClosureExtension.HighHeight :=\n"
        "    ⟨(1 + Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.gammaTwoCuspLevel Y) / 2, by\n"
        "      linarith⟩\n",
        "  let h : QYM.FullCertification.P2CuspCollarClosureExtension.HighHeight :=\n"
        "    ⟨(1 + Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.gammaTwoCuspLevel Y) / 2, by\n"
        "      change 1 < (1 + Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.gammaTwoCuspLevel Y) / 2\n"
        "      linarith⟩\n",
        (
            Header(50206, 6, "linarith failed to find a contradiction"),
        ),
        "Expose the Set.Ioi subtype membership as its concrete real inequality before invoking linear arithmetic.",
        "The exact local hypothesis is hY : 1 < gammaTwoCuspLevel Y; after change the goal follows by linear arithmetic.",
    ),
)


FOREIGN_HELPERS: tuple[tuple[str, str, str], ...] = (
    ("probe11_early_frontier", "qym-probe11-early-frontier-static/qym_probe11_early_frontier_static.py", "9177e4fd6aa03215aec4728415d095e7e099594f6bc12facbf5a2fd879175b9a"),
    ("probe11_mid", "qym-probe11-mid-p10-authority/qym_probe11_mid_p10_authority.py", "f2adebd8803e40df538a8b85401ea5a26af4585aefe521135c77dde8576a1fc6"),
    ("probe11_tail", "qym-probe11-tail-p10-conditional/qym_probe11_tail_p10_conditional.py", "e76d0830315918d8d51c5063048b0f85ad9f4a68c8dffa2dbab19da25a9aae49"),
    ("probe11_earlymid", "qym-probe11-earlymid-p10-conditional/qym_probe11_earlymid_p10_conditional.py", "683e740e96970dd4ca53c51016f30839a4ead5c641c7c8619f5b85733e9612e6"),
    ("probe11_40k", "qym-probe11-40k-p10-conditional/qym_probe11_40k_p10_conditional.py", "6765e05b8681e4d7e13bc735c4d37ea038c75423a7d5ebc1ad73b179a99e0052"),
    ("probe11_structural50", "qym-probe11-50k-structural-p10/qym_probe11_50k_structural_p10.py", "82189532a76f4785734d851f459a67c2dc04e373d1fc70eb5a137506f2dc57ae"),
    ("probe12_refinement", "qym-probe12-p10-midlate-refinement/qym_probe12_p10_midlate_refinement.py", "058dba8e252db0562b7b83ed5d6701445b41f189db0559e06613823f1565207d"),
    ("probe12_frontier_p11", "qym-probe12-early-frontier-p11-conditional/qym_probe12_early_frontier_p11_conditional.py", "35b5ccf5f04899c810ca798cbcf700230fdfc4b930d16ab5d9cf646584954215"),
    ("probe12_36k42k_p11", "qym-probe12-36k42k-p11-reanchored/qym_probe12_36k42k_p11_reanchored.py", "5bd02f57232ac30c336b3e13574b7cba4dc4b0998f159e3fdebd41ed6354a365"),
    ("probe12_43k49k_p11", "qym-probe12-43k49k-p11-conditional/qym_probe12_43k49k_p11_conditional.py", "5070ada686ac425b76403ae53210e586bda305a8a70606d6d3bc6529ff2b2523"),
    ("probe12_50k53k_p11", "qym-probe12-50k53k-p11-conditional/qym_probe12_50k53k_p11_conditional.py", "5352b37ec754a5131164e91649b54a277b5d257258bc316f653b6d218bfb63c8"),
    ("probe12_52k61k_p11", "qym-probe12-52k61k-p11-conditional/qym_probe12_52k61k_p11_conditional.py", "7066e3297bd171ec58a4547ed426a8d9a6228abf4de78bf3ad203d880ef7f795"),
    ("probe9_50k", "qym-probe9-50k-static/qym_probe9_50k_static.py", "44b17336ea2cfa089c461e8c23cf25d2de95987e106e8473f2765cb2bf5faab4"),
)


DECLARED_REFINEMENTS: dict[str, tuple[str, str]] = {
    "petersson_definiteness_use_toK_norm_square": (
        "probe9_50k",
        "petersson_definiteness_expose_complex_inner",
    ),
    "actual_stage_high_height_make_goal_explicit": (
        "probe12_43k49k_p11",
        "actual_stage_high_height_proof_skip_noop_dsimp",
    ),
}
DECLARED_EXACT_EQUALITIES: frozenset[str] = frozenset({
    "petersson_definiteness_use_toK_norm_square",
    "actual_stage_high_height_make_goal_explicit",
})
DECLARED_OVERLAP_VARIANTS: dict[str, frozenset[str]] = {
    "petersson_definiteness_use_toK_norm_square": frozenset({"new"}),
    "actual_stage_high_height_make_goal_explicit": frozenset({"new"}),
}
DECLARED_INVERSE_OVERLAP_VARIANTS: dict[str, frozenset[str]] = {
    "petersson_definiteness_use_toK_norm_square": frozenset(),
    "actual_stage_high_height_make_goal_explicit": frozenset(),
}


EXCLUDED: tuple[dict[str, object], ...] = (
    {
        "headers": [
            {"line": line, "column": column}
            for line, column in (
                (50276, 78), (50297, 6), (50303, 78), (50326, 6),
                (50397, 97), (50409, 48), (50410, 108), (50416, 43),
                (50417, 82), (50419, 43), (50422, 52), (50424, 52),
                (50426, 84), (50435, 180), (50513, 84), (50517, 27),
                (50573, 10),
            )
        ],
        "kind": "effective_to_literal_quotient_bundle_type_blocker",
        "reason": "GammaTwoQuotient is the effective-action orbit quotient, while InverseEtaBase is Mock2's literal Gamma(2) orbit quotient; no coercion or bridge is present",
        "minimal_missing_constructions": [
            "an explicit Equiv/Homeomorph effectiveGammaTwoQuotientEquivLiteral with quotient-map compatibility in both directions",
            "the pullback of InverseEtaTotal/InverseEtaFibre along that equivalence, rather than claiming the literal projection equals an effective-quotient point",
            "transported global sections and eta-coordinate/projection laws for the pulled-back bundle",
        ],
    },
    {
        "headers": [
            {"line": 50291, "column": 8},
            {"line": 50443, "column": 2},
            {"line": 50459, "column": 8},
        ],
        "kind": "literal_quotient_bundle_measurability_blocker",
        "reason": "continuous-to-measurable conversion lacks OpensMeasurableSpace on InverseEtaBase, InverseEtaBase x Complex, and InverseEtaTotal",
        "minimal_missing_constructions": [
            "OpensMeasurableSpace proofs compatible with the literal quotient/coinduced measurable structures",
            "measurability of the quotient equivalence and of the pulled-back total/scalar coordinate maps",
        ],
    },
    {
        "headers": [
            {"line": 50294, "column": 2},
            {"line": 50426, "column": 91},
            {"line": 50433, "column": 63},
            {"line": 50513, "column": 180},
        ],
        "kind": "structural_cascades_not_selected",
        "reason": "these missing declarations, holes, and continuity goals are downstream of the ill-typed quotient/bundle producers and must be revalidated only after the bridge is constructed",
    },
)


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
        "axiom_declaration": len(re.findall(r"(?m)^\s*axiom\s+", text)),
        "unsafe_declaration": len(re.findall(r"(?m)^\s*unsafe\s+", text)),
        "maxHeartbeats_zero": len(re.findall(r"set_option\s+maxHeartbeats\s+0\b", text)),
    }


def input_expected() -> dict[str, object]:
    return {
        "sha256": INPUT_SHA256,
        "git_blob": INPUT_GIT_BLOB,
        "bytes": INPUT_BYTES,
        "lf": INPUT_LF,
        "cr": False,
        "nul": False,
        "bom": False,
        "terminal_lf": True,
    }


def output_expected() -> dict[str, object]:
    return {
        "sha256": OUTPUT_SHA256,
        "git_blob": OUTPUT_GIT_BLOB,
        "bytes": OUTPUT_BYTES,
        "lf": OUTPUT_LF,
        "cr": False,
        "nul": False,
        "bom": False,
        "terminal_lf": True,
    }


def sentinels_unsealed() -> bool:
    return OUTPUT_SHA256 == "" and OUTPUT_GIT_BLOB == "" and OUTPUT_BYTES == 0 and OUTPUT_LF == 0


def check_shape(actual: dict[str, object], expected: dict[str, object], *, unsealed: bool = False) -> None:
    keys = ("cr", "nul", "bom", "terminal_lf") if unsealed else tuple(expected)
    if any(actual[key] != expected[key] for key in keys):
        raise RuntimeError(f"shape mismatch: {actual} != {expected}")


def verify_authority(log_raw: bytes, header_raw: bytes, diagnostics_raw: bytes) -> list[dict[str, object]]:
    for label, actual, expected in (
        ("log", sha256(log_raw), LOG_SHA256),
        ("headers", sha256(header_raw), HEADERS_SHA256),
        ("diagnostics", sha256(diagnostics_raw), DIAGNOSTICS_SHA256),
    ):
        if actual != expected:
            raise RuntimeError(f"Probe12 {label} identity mismatch: {actual}")
    header_lines = header_raw.decode("utf-8", errors="strict").splitlines()
    rows = [json.loads(line) for line in diagnostics_raw.decode("utf-8", errors="strict").splitlines()]
    if len(header_lines) != 183:
        raise RuntimeError(f"expected 183 exact error headers, got {len(header_lines)}")
    if sum(row.get("severity") == "error" for row in rows) != 183:
        raise RuntimeError("diagnostic error count is not 183")
    if sum(row.get("severity") == "warning" for row in rows) != 350:
        raise RuntimeError("diagnostic warning count is not 350")
    mapped: list[dict[str, object]] = []
    for rule in RULES:
        for header in rule.headers:
            code = f"\\({re.escape(header.code)}\\)" if header.code else ""
            pattern = re.compile(
                rf"^PrimalitySheafVerification/QYM\.lean:{header.line}:{header.column}: "
                rf"error{code}: {re.escape(header.message)}"
            )
            hm = [line for line in header_lines if pattern.match(line)]
            dm = [
                row
                for row in rows
                if row.get("severity") == "error"
                and row.get("line") == header.line
                and row.get("column") == header.column
                and row.get("code") == header.code
                and str(row.get("message", "")).startswith(header.message)
            ]
            if len(hm) != 1 or len(dm) != 1:
                raise RuntimeError(f"{rule.label}: authority mapping mismatch at {header.line}:{header.column}")
            mapped.append(
                {
                    "rule": rule.label,
                    **header.__dict__,
                    "kind": (
                        "declared_active_probe9_rule_refinement"
                        if rule.label in DECLARED_REFINEMENTS
                        else "exact_probe12_direct_local_root"
                    ),
                }
            )
    return mapped


def spans(text: str, needle: str) -> list[tuple[int, int]]:
    result: list[tuple[int, int]] = []
    start = 0
    while True:
        found = text.find(needle, start)
        if found < 0:
            return result
        result.append((found, found + len(needle)))
        start = found + 1


def load_foreign(name: str, relative: str, expected_sha: str) -> ModuleType:
    path = Path(__file__).resolve().parent.parent / relative
    raw = path.read_bytes()
    if sha256(raw) != expected_sha:
        raise RuntimeError(f"foreign helper identity mismatch: {name}: {sha256(raw)}")
    module_name = "_qym_50k50599_foreign_" + name
    spec = importlib.util.spec_from_file_location(module_name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot import foreign helper: {name}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[module_name] = module
    spec.loader.exec_module(module)
    return module


def audit_collisions(text: str, *, inverse: bool) -> dict[str, object]:
    own: list[tuple[int, int, str]] = []
    for rule in RULES:
        active = rule.new if inverse else rule.old
        found = spans(text, active)
        if len(found) != rule.occurrences:
            raise RuntimeError(f"{rule.label}: active anchor count {len(found)}")
        for start, end in found:
            line = text.count("\n", 0, start) + 1
            if not 50000 <= line <= 50599:
                raise RuntimeError(f"{rule.label}: scope violation at line {line}")
            own.append((start, end, rule.label))
    own_sorted = sorted(own)
    own_overlaps: list[dict[str, object]] = []
    for left, right in zip(own_sorted, own_sorted[1:]):
        if left[1] > right[0]:
            own_overlaps.append({"left": left[2], "right": right[2]})
    equalities: list[dict[str, str]] = []
    overlaps: list[dict[str, object]] = []
    foreign_active_spans = 0
    identities: dict[str, str] = {}
    for name, relative, expected_sha in FOREIGN_HELPERS:
        module = load_foreign(name, relative, expected_sha)
        identities[name] = expected_sha
        foreign_rules = getattr(module, "RULES", None)
        if foreign_rules is None:
            raise RuntimeError(f"foreign helper has no RULES: {name}")
        for foreign in foreign_rules:
            for variant, anchor in (("old", foreign.old), ("new", foreign.new)):
                found = spans(text, anchor)
                foreign_active_spans += len(found)
                for own_rule in RULES:
                    for own_variant, own_anchor in (("old", own_rule.old), ("new", own_rule.new)):
                        if own_anchor == anchor:
                            equalities.append(
                                {
                                    "own": own_rule.label,
                                    "own_variant": own_variant,
                                    "foreign": f"{name}:{foreign.label}",
                                    "foreign_variant": variant,
                                }
                            )
                for fstart, fend in found:
                    for ostart, oend, own_label in own:
                        if max(fstart, ostart) < min(fend, oend):
                            overlaps.append(
                                {
                                    "own": own_label,
                                    "foreign": f"{name}:{foreign.label}",
                                    "foreign_variant": variant,
                                    "own_span": [ostart, oend],
                                    "foreign_span": [fstart, fend],
                                }
                            )
    expected_equalities = {
        (own, "old", f"{owner_name}:{owner_rule}", "new")
        for own, (owner_name, owner_rule) in DECLARED_REFINEMENTS.items()
        if own in DECLARED_EXACT_EQUALITIES
    }
    actual_equalities = {
        (item["own"], item["own_variant"], item["foreign"], item["foreign_variant"])
        for item in equalities
    }
    expected_overlaps = {
        (own, f"{owner_name}:{owner_rule}", variant)
        for own, (owner_name, owner_rule) in DECLARED_REFINEMENTS.items()
        for variant in (
            DECLARED_INVERSE_OVERLAP_VARIANTS[own]
            if inverse
            else DECLARED_OVERLAP_VARIANTS[own]
        )
    }
    actual_overlaps = {
        (item["own"], item["foreign"], item["foreign_variant"])
        for item in overlaps
    }
    undeclared_equalities = actual_equalities - expected_equalities
    missing_equalities = expected_equalities - actual_equalities
    undeclared_overlaps = actual_overlaps - expected_overlaps
    missing_overlaps = expected_overlaps - actual_overlaps
    if own_overlaps or undeclared_equalities or missing_equalities or undeclared_overlaps or missing_overlaps:
        raise RuntimeError(
            "collision contract mismatch: "
            f"own={own_overlaps}, "
            f"undeclared_equalities={sorted(undeclared_equalities)}, "
            f"missing_equalities={sorted(missing_equalities)}, "
            f"undeclared_overlaps={sorted(undeclared_overlaps)}, "
            f"missing_overlaps={sorted(missing_overlaps)}"
        )
    return {
        "foreign_helper_sha256": identities,
        "own_spans_checked": len(own),
        "foreign_active_spans_checked": foreign_active_spans,
        "own_span_overlaps": own_overlaps,
        "declared_exact_anchor_equalities": equalities,
        "declared_foreign_span_overlaps": overlaps,
        "declared_refinements": {
            label: {
                "foreign_helper": owner[0],
                "foreign_rule": owner[1],
                "exact_anchor_equality": label in DECLARED_EXACT_EQUALITIES,
                "overlap_variants": sorted(DECLARED_OVERLAP_VARIANTS[label]),
                "inverse_overlap_variants": sorted(DECLARED_INVERSE_OVERLAP_VARIANTS[label]),
            }
            for label, owner in DECLARED_REFINEMENTS.items()
        },
        "undeclared_exact_anchor_equalities": [],
        "undeclared_foreign_span_overlaps": [],
    }


def apply_rules(text: str, inverse: bool = False) -> tuple[str, list[dict[str, object]]]:
    audits: list[dict[str, object]] = []
    ordered = tuple(reversed(RULES)) if inverse else RULES
    for rule in ordered:
        old, new = (rule.new, rule.old) if inverse else (rule.old, rule.new)
        count = text.count(old)
        if count != rule.occurrences:
            raise RuntimeError(f"{rule.label}: exact anchor count {count}, expected {rule.occurrences}")
        text = text.replace(old, new)
        audits.append(
            {
                "label": rule.label,
                "direction": "inverse" if inverse else "forward",
                "occurrences": count,
                "headers": [header.__dict__ for header in rule.headers],
                "rationale": rule.rationale,
                "precedent": rule.precedent,
                "declared_refinement": (
                    {
                        "foreign_helper": DECLARED_REFINEMENTS[rule.label][0],
                        "foreign_rule": DECLARED_REFINEMENTS[rule.label][1],
                    }
                    if rule.label in DECLARED_REFINEMENTS
                    else None
                ),
            }
        )
    return text, audits


transform = apply_rules


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--probe11-log", type=Path, required=True)
    parser.add_argument("--probe11-error-headers", type=Path, required=True)
    parser.add_argument("--probe11-diagnostics", type=Path, required=True)
    parser.add_argument("--audit", type=Path, required=True)
    parser.add_argument("--mode", choices=("forward", "inverse"), default="forward")
    parser.add_argument("--bootstrap-seal", action="store_true")
    args = parser.parse_args()
    inverse = args.mode == "inverse"
    if args.bootstrap_seal and not sentinels_unsealed():
        raise RuntimeError("bootstrap refused: output identity already sealed")
    if not args.bootstrap_seal and sentinels_unsealed():
        raise RuntimeError("output identity unsealed")
    source = args.input.read_bytes()
    source_shape = shape(source)
    check_shape(
        source_shape,
        output_expected() if inverse else input_expected(),
        unsealed=args.bootstrap_seal and inverse,
    )
    mapped = verify_authority(
        args.probe11_log.read_bytes(),
        args.probe11_error_headers.read_bytes(),
        args.probe11_diagnostics.read_bytes(),
    )
    source_text = source.decode("utf-8", errors="strict")
    collision = audit_collisions(source_text, inverse=inverse)
    before_trust = trust(source_text)
    result_text, rule_audit = apply_rules(source_text, inverse=inverse)
    result = result_text.encode("utf-8")
    result_shape = shape(result)
    check_shape(
        result_shape,
        input_expected() if inverse else output_expected(),
        unsealed=args.bootstrap_seal and not inverse,
    )
    after_trust = trust(result_text)
    if before_trust != after_trust or any(after_trust.values()):
        raise RuntimeError(f"trust0 failure: {before_trust} -> {after_trust}")
    restored, _ = apply_rules(result_text, inverse=not inverse)
    if restored.encode("utf-8") != source:
        raise RuntimeError("opposite transform failed byte-exact restoration")
    if args.output.exists() or args.audit.exists():
        raise RuntimeError("refusing to overwrite output or audit")
    record = {
        "schema": SCHEMA,
        "status": "STATIC_PASS_EXACT_TERMINAL_PROBE12_NOT_LEAN_EXECUTED",
        "activation": False,
        "promotion": False,
        "mode": args.mode,
        "authority": {
            "candidate_sha256": INPUT_SHA256,
            "candidate_git_blob": INPUT_GIT_BLOB,
            "log_sha256": LOG_SHA256,
            "error_headers_sha256": HEADERS_SHA256,
            "diagnostics_sha256": DIAGNOSTICS_SHA256,
            "errors": 183,
            "warnings": 350,
            "panic": 0,
            "exit": 1,
        },
        "scope": {
            "candidate_lines": [50000, 50599],
            "independent_direct_roots_only": True,
            "declared_active_rule_refinements": len(DECLARED_REFINEMENTS),
            "undeclared_foreign_helper_span_overlap": False,
            "cascade_diagnostics_selected": False,
            "excluded": EXCLUDED,
        },
        "source": source_shape,
        "result": result_shape,
        "repair_families": len(RULES),
        "repair_occurrences": sum(item["occurrences"] for item in rule_audit),
        "direct_diagnostics": len(mapped),
        "selected_exact_probe12_lines": sorted({header.line for rule in RULES for header in rule.headers}),
        "diagnostic_map": mapped,
        "rules": rule_audit,
        "collision_audit": collision,
        "inverse_byte_equal": True,
        "trust": after_trust,
        "execution": {
            "lean": False,
            "lake": False,
            "git": False,
            "network": False,
            "remote": False,
            "repository_source_mutation": False,
        },
    }
    args.output.write_bytes(result)
    args.audit.write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(json.dumps(record, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
