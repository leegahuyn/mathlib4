#!/usr/bin/env python3
"""Deterministic, reversible static transformer for the QYM mid-file P0 repairs.

This tool is intentionally pinned to the exact probe2 candidate whose SHA-256 is
64f045b04dc39e157ba609047e6ac9a0851962b7c74024af9987dbcbd46f19d1.
It does not run Lean and it does not fetch or promote anything.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from dataclasses import dataclass
from pathlib import Path


EXPECTED_FORWARD_INPUT_SHA256 = (
    "64f045b04dc39e157ba609047e6ac9a0851962b7c74024af9987dbcbd46f19d1"
)
EXPECTED_FORWARD_INPUT_BYTES = 2_906_438
EXPECTED_FORWARD_INPUT_LF = 61_580

EXPECTED_FORWARD_OUTPUT_SHA256 = (
    "3a67c67a9a132764b71ce5434fd1b476a5ce47f6f3e648b8cd23cfe84797ae14"
)
EXPECTED_FORWARD_OUTPUT_BYTES = 2_906_731
EXPECTED_FORWARD_OUTPUT_LF = 61_584

TRUST_MARKERS = (
    "sorry",
    "admit",
    "axiom",
    "unsafe",
    "import ",
    "set_option",
)


@dataclass(frozen=True)
class Rewrite:
    label: str
    old: str
    new: str
    expected: int = 1
    region_start: str | None = None
    region_end: str | None = None


FORM_DOMAIN_REGION_START = "namespace QYM.FormDomainRealizationExtension\n"
FORM_DOMAIN_REGION_END = "end QYM.FormDomainRealizationExtension\n"

EVIDENCE_REGION_START = (
    "namespace QYM.FullCertification.TypedEvidenceUnboundedFormResolventExtension\n"
)
EVIDENCE_REGION_END = (
    "end QYM.FullCertification.TypedEvidenceUnboundedFormResolventExtension\n"
)


REWRITES: tuple[Rewrite, ...] = (
    Rewrite(
        "p0_1_pin_real_scalar_binders_in_IsRealBilinear",
        "    (∀ a x y, bilinear (a • x) y = a • bilinear x y) ∧\n"
        "    (∀ x y₁ y₂, bilinear x (y₁ + y₂) =\n"
        "      bilinear x y₁ + bilinear x y₂) ∧\n"
        "    (∀ a x y, bilinear x (a • y) = a • bilinear x y)",
        "    (∀ (a : ℝ) x y, bilinear (a • x) y = a • bilinear x y) ∧\n"
        "    (∀ x y₁ y₂, bilinear x (y₁ + y₂) =\n"
        "      bilinear x y₁ + bilinear x y₂) ∧\n"
        "    (∀ (a : ℝ) x y, bilinear x (a • y) = a • bilinear x y)",
    ),
    Rewrite(
        "p0_2_supply_invariant_subspace_proof_explicitly",
        "    QYM.HilbertOperatorFormExtension.exists_positive_compact_invariantRestriction\n"
        "      hpositive hcompact hclosed",
        "    QYM.HilbertOperatorFormExtension.exists_positive_compact_invariantRestriction\n"
        "      (hV := hV) hpositive hcompact hclosed",
    ),
    Rewrite(
        "p0_3_make_mem_graph_operator_explicit",
        "    rw [LinearPMap.mem_graph_iff] at hz\n"
        "    rcases hz with ⟨x, hxFirst, hxSecond⟩",
        "    rcases (LinearPMap.mem_graph_iff T).mp hz with ⟨x, hxFirst, hxSecond⟩",
    ),
    Rewrite(
        "p0_4_lift_graph_membership_into_closure",
        "    exact Filter.Eventually.of_forall (fun i => T.mem_graph (u i))",
        "    exact Filter.Eventually.of_forall\n"
        "      (fun i => subset_closure (T.mem_graph (u i)))",
    ),
    Rewrite(
        "p0_5_pin_generic_clm_resolvent_coercions",
        "    (hcompact : IsCompactOperator (resolvent T r : H → H)) :\n"
        "    IsCompactOperator (resolvent T s : H → H) := by",
        "    (hcompact :\n"
        "      IsCompactOperator ((resolvent T r : H →L[𝕜] H) : H → H)) :\n"
        "    IsCompactOperator ((resolvent T s : H →L[𝕜] H) : H → H) := by",
    ),
    Rewrite(
        "p0_5_pin_real_clm_resolvent_r_coercions",
        "IsCompactOperator (resolvent T r : H → H)",
        "IsCompactOperator ((resolvent T r : H →L[ℝ] H) : H → H)",
        expected=5,
    ),
    Rewrite(
        "p0_5_pin_real_clm_resolvent_s_coercion",
        "IsCompactOperator (resolvent T s : H → H)",
        "IsCompactOperator ((resolvent T s : H →L[ℝ] H) : H → H)",
    ),
    Rewrite(
        "p0_5_pin_zero_clm_resolvent_coercions",
        "(resolvent (0 : H →L[ℝ] H) (1 : ℝ) : H → H)",
        "((resolvent (0 : H →L[ℝ] H) (1 : ℝ) : H →L[ℝ] H) : H → H)",
        expected=2,
    ),
    Rewrite(
        "p0_6_pin_lax_milgram_evidence_universes",
        "  | .laxMilgramOperatorBridge =>\n"
        "      QYM.FullCertification.PaperNormalized.lemma4_13_boundedRealFormOperatorBridgeStatement ∧\n"
        "        QYM.FullCertification.PaperNormalized.lemma4_13_boundedRealFormEquivalenceStatement\n"
        "  | .laxMilgramUniqueSolution =>\n"
        "      QYM.FullCertification.PaperNormalized.lemma4_16_boundedRealFormUniqueSolutionStatement ∧\n"
        "        QYM.FullCertification.PaperNormalized.lemma4_16_boundedRealFormQuantitativeSolutionStatement\n"
        "  | .laxMilgramPerturbation =>\n"
        "      QYM.FullCertification.PaperNormalized.lemma4_16_boundedRealFormPerturbationStatement",
        "  | .laxMilgramOperatorBridge =>\n"
        "      QYM.FullCertification.PaperNormalized.lemma4_13_boundedRealFormOperatorBridgeStatement.{0} ∧\n"
        "        QYM.FullCertification.PaperNormalized.lemma4_13_boundedRealFormEquivalenceStatement.{0}\n"
        "  | .laxMilgramUniqueSolution =>\n"
        "      QYM.FullCertification.PaperNormalized.lemma4_16_boundedRealFormUniqueSolutionStatement.{0} ∧\n"
        "        QYM.FullCertification.PaperNormalized.lemma4_16_boundedRealFormQuantitativeSolutionStatement.{0}\n"
        "  | .laxMilgramPerturbation =>\n"
        "      QYM.FullCertification.PaperNormalized.lemma4_16_boundedRealFormPerturbationStatement.{0}",
        region_start=EVIDENCE_REGION_START,
        region_end=EVIDENCE_REGION_END,
    ),
    Rewrite(
        "p0_7_expose_domain_equiv_underlying_map",
        "  simp only [domainEquiv, LinearEquiv.ofInjective_apply, formEmbedding_apply]",
        "  change formEmbedding B j u = j (u : V)\n"
        "  exact formEmbedding_apply B j u",
        region_start=FORM_DOMAIN_REGION_START,
        region_end=FORM_DOMAIN_REGION_END,
    ),
    Rewrite(
        "p0_7_expose_form_embedding_in_membership_witness",
        "      simpa only [formEmbedding_apply] using hw",
        "      change formEmbedding B j w = j u at hw\n"
        "      exact hw",
        region_start=FORM_DOMAIN_REGION_START,
        region_end=FORM_DOMAIN_REGION_END,
    ),
    Rewrite(
        "p0_7_expose_dense_range_composition_beta",
        "  simpa only [Function.comp_apply] using hcomp",
        "  change DenseRange (fun u : formDomain B j => j (u : V)) at hcomp\n"
        "  exact hcomp",
        region_start=FORM_DOMAIN_REGION_START,
        region_end=FORM_DOMAIN_REGION_END,
    ),
)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def assert_text_hygiene(raw: bytes, *, label: str) -> str:
    if b"\r" in raw:
        raise AssertionError(f"{label}: CR byte forbidden")
    if b"\x00" in raw:
        raise AssertionError(f"{label}: NUL byte forbidden")
    if raw.startswith(b"\xef\xbb\xbf"):
        raise AssertionError(f"{label}: UTF-8 BOM forbidden")
    if not raw.endswith(b"\n"):
        raise AssertionError(f"{label}: terminal LF required")
    return raw.decode("utf-8", errors="strict")


def replace_one(
    text: str,
    rewrite: Rewrite,
    *,
    inverse: bool,
    audit: list[dict[str, object]],
) -> str:
    old = rewrite.new if inverse else rewrite.old
    new = rewrite.old if inverse else rewrite.new
    direction = "inverse" if inverse else "forward"

    if rewrite.region_start is None:
        count = text.count(old)
        if count != rewrite.expected:
            raise AssertionError(
                f"{rewrite.label}/{direction}: expected {rewrite.expected}, found {count}"
            )
        result = text.replace(old, new)
    else:
        assert rewrite.region_end is not None
        if text.count(rewrite.region_start) != 1:
            raise AssertionError(f"{rewrite.label}: non-unique region start")
        if text.count(rewrite.region_end) != 1:
            raise AssertionError(f"{rewrite.label}: non-unique region end")
        start = text.index(rewrite.region_start) + len(rewrite.region_start)
        end = text.index(rewrite.region_end, start)
        region = text[start:end]
        count = region.count(old)
        if count != rewrite.expected:
            raise AssertionError(
                f"{rewrite.label}/{direction}: expected {rewrite.expected} in region, "
                f"found {count}"
            )
        result = text[:start] + region.replace(old, new) + text[end:]

    audit.append(
        {
            "direction": direction,
            "expected_occurrences": rewrite.expected,
            "label": rewrite.label,
            "observed_occurrences": count,
            "region_scoped": rewrite.region_start is not None,
        }
    )
    return result


def transform(text: str, *, inverse: bool) -> tuple[str, list[dict[str, object]]]:
    audit: list[dict[str, object]] = []
    sequence = reversed(REWRITES) if inverse else REWRITES
    for rewrite in sequence:
        text = replace_one(text, rewrite, inverse=inverse, audit=audit)
    return text, audit


def trust_marker_counts(text: str) -> dict[str, int]:
    return {marker: text.count(marker) for marker in TRUST_MARKERS}


def validate_input(path: Path, *, inverse: bool) -> tuple[bytes, str]:
    if path.is_symlink():
        raise AssertionError("input must not be a symbolic link")
    raw = path.read_bytes()
    expected_sha = (
        EXPECTED_FORWARD_OUTPUT_SHA256 if inverse else EXPECTED_FORWARD_INPUT_SHA256
    )
    expected_bytes = (
        EXPECTED_FORWARD_OUTPUT_BYTES if inverse else EXPECTED_FORWARD_INPUT_BYTES
    )
    expected_lf = EXPECTED_FORWARD_OUTPUT_LF if inverse else EXPECTED_FORWARD_INPUT_LF
    if expected_sha == "__UNSEALED__" or expected_bytes < 0 or expected_lf < 0:
        raise AssertionError("transformer output seal has not been finalized")
    actual_sha = sha256(raw)
    if actual_sha != expected_sha:
        raise AssertionError(
            f"input SHA-256 mismatch: expected {expected_sha}, found {actual_sha}"
        )
    if len(raw) != expected_bytes:
        raise AssertionError(
            f"input byte-count mismatch: expected {expected_bytes}, found {len(raw)}"
        )
    if raw.count(b"\n") != expected_lf:
        raise AssertionError(
            f"input LF-count mismatch: expected {expected_lf}, found {raw.count(b'\n')}"
        )
    return raw, assert_text_hygiene(raw, label="input")


def validate_output(
    raw_before: bytes,
    text_before: str,
    text_after: str,
    *,
    inverse: bool,
) -> bytes:
    raw_after = text_after.encode("utf-8")
    assert_text_hygiene(raw_after, label="output")
    expected_sha = (
        EXPECTED_FORWARD_INPUT_SHA256 if inverse else EXPECTED_FORWARD_OUTPUT_SHA256
    )
    expected_bytes = (
        EXPECTED_FORWARD_INPUT_BYTES if inverse else EXPECTED_FORWARD_OUTPUT_BYTES
    )
    expected_lf = EXPECTED_FORWARD_INPUT_LF if inverse else EXPECTED_FORWARD_OUTPUT_LF
    if sha256(raw_after) != expected_sha:
        raise AssertionError("output SHA-256 seal mismatch")
    if len(raw_after) != expected_bytes:
        raise AssertionError("output byte-count seal mismatch")
    if raw_after.count(b"\n") != expected_lf:
        raise AssertionError("output LF-count seal mismatch")
    if trust_marker_counts(text_before) != trust_marker_counts(text_after):
        raise AssertionError("trust-marker inventory changed")

    roundtrip, _ = transform(text_after, inverse=not inverse)
    if roundtrip.encode("utf-8") != raw_before:
        raise AssertionError("exact textual inverse check failed")
    return raw_after


def reserve_output_paths(output: Path, audit: Path, input_path: Path) -> None:
    resolved_input = input_path.resolve(strict=True)
    if not output.parent.is_dir() or not audit.parent.is_dir():
        raise AssertionError("output and audit parents must already exist")
    for path in (output, audit):
        if path.exists() or path.is_symlink():
            raise AssertionError(f"refusing to overwrite existing path: {path}")
        if path.resolve(strict=False) == resolved_input:
            raise AssertionError("output path must differ from input path")
    if output.resolve(strict=False) == audit.resolve(strict=False):
        raise AssertionError("output and audit paths must differ")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", required=True)
    parser.add_argument("--mode", choices=("forward", "inverse"), default="forward")
    parser.add_argument("--output")
    parser.add_argument("--audit")
    parser.add_argument("--check-only", action="store_true")
    args = parser.parse_args()

    inverse = args.mode == "inverse"
    input_path = Path(args.input)
    raw_before, text_before = validate_input(input_path, inverse=inverse)
    text_after, rewrites = transform(text_before, inverse=inverse)
    raw_after = validate_output(
        raw_before, text_before, text_after, inverse=inverse
    )

    result = {
        "input_bytes": len(raw_before),
        "input_lf": raw_before.count(b"\n"),
        "input_sha256": sha256(raw_before),
        "inverse_roundtrip_verified": True,
        "mode": args.mode,
        "output_bytes": len(raw_after),
        "output_lf": raw_after.count(b"\n"),
        "output_sha256": sha256(raw_after),
        "promotion_authorized": False,
        "rewrites": rewrites,
        "schema": "qym-probe3-mid-p0-transform-v1",
        "trust_marker_counts": trust_marker_counts(text_after),
    }

    if args.check_only:
        if args.output is not None or args.audit is not None:
            raise AssertionError("--check-only forbids --output and --audit")
        print(json.dumps(result, indent=2, sort_keys=True))
        return

    if args.output is None or args.audit is None:
        raise AssertionError("--output and --audit are required outside --check-only")
    output_path = Path(args.output)
    audit_path = Path(args.audit)
    reserve_output_paths(output_path, audit_path, input_path)
    with output_path.open("xb") as handle:
        handle.write(raw_after)
    with audit_path.open("x", encoding="utf-8", newline="\n") as handle:
        handle.write(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
