#!/usr/bin/env python3
"""Finalize the scope-safe QYM probe with exact independent-frontier repairs."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


EXPECTED_INPUT_SHA256 = (
    "52907b000d31b3f925fd8437ec6aa96beea682d3ba362afbf76c9e49fa188388"
)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def replace_exact(text: str, old: str, new: str, expected: int, label: str,
                  audit: list[dict[str, object]]) -> str:
    count = text.count(old)
    if count != expected:
        raise AssertionError(f"{label}: expected {expected}, found {count}")
    audit.append({"label": label, "occurrences": count})
    return text.replace(old, new)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", required=True)
    parser.add_argument("--output", required=True)
    parser.add_argument("--audit", required=True)
    args = parser.parse_args()

    input_path = Path(args.input)
    raw = input_path.read_bytes()
    if sha256(raw) != EXPECTED_INPUT_SHA256:
        raise AssertionError("scope-safe QYM input SHA-256 mismatch")
    if b"\r" in raw or b"\x00" in raw or not raw.endswith(b"\n"):
        raise AssertionError("scope-safe QYM encoding/newline invariant mismatch")
    text = raw.decode("utf-8")
    audit: list[dict[str, object]] = []

    text = replace_exact(
        text,
        "inductive X where\n"
        "  | left\n"
        "  | middle\n"
        "  | right\n"
        "deriving DecidableEq, Fintype",
        "inductive X where\n"
        "  | left\n"
        "  | middle\n"
        "  | right\n"
        "deriving DecidableEq\n\n"
        "instance : Fintype X where\n"
        "  elems := {X.left, X.middle, X.right}\n"
        "  complete := by\n"
        "    intro x\n"
        "    cases x <;> simp",
        1,
        "replace_broken_fintype_deriving_X",
        audit,
    )
    text = replace_exact(
        text,
        "inductive Patch0Point where\n"
        "  | left\n"
        "  | middle\n"
        "deriving DecidableEq, Fintype",
        "inductive Patch0Point where\n"
        "  | left\n"
        "  | middle\n"
        "deriving DecidableEq\n\n"
        "instance : Fintype Patch0Point where\n"
        "  elems := {Patch0Point.left, Patch0Point.middle}\n"
        "  complete := by\n"
        "    intro x\n"
        "    cases x <;> simp",
        1,
        "replace_broken_fintype_deriving_Patch0Point",
        audit,
    )
    text = replace_exact(
        text,
        "inductive Patch1Point where\n"
        "  | middle\n"
        "  | right\n"
        "deriving DecidableEq, Fintype",
        "inductive Patch1Point where\n"
        "  | middle\n"
        "  | right\n"
        "deriving DecidableEq\n\n"
        "instance : Fintype Patch1Point where\n"
        "  elems := {Patch1Point.middle, Patch1Point.right}\n"
        "  complete := by\n"
        "    intro x\n"
        "    cases x <;> simp",
        1,
        "replace_broken_fintype_deriving_Patch1Point",
        audit,
    )
    text = replace_exact(
        text,
        "inductive OverlapPoint where\n"
        "  | middle\n"
        "deriving DecidableEq, Fintype",
        "inductive OverlapPoint where\n"
        "  | middle\n"
        "deriving DecidableEq\n\n"
        "instance : Fintype OverlapPoint where\n"
        "  elems := {OverlapPoint.middle}\n"
        "  complete := by\n"
        "    intro x\n"
        "    cases x <;> simp",
        1,
        "replace_broken_fintype_deriving_OverlapPoint",
        audit,
    )
    text = replace_exact(
        text,
        "  simpa only [paperSignLevel_apply] using\n"
        "    tendsto_atBot_add_const_right atTop c hneg",
        "  change Tendsto (fun n : ℕ => -(n : ℝ) + c) atTop atBot\n"
        "  exact tendsto_atBot_add_const_right atTop c hneg",
        1,
        "make_paper_sign_tendsto_target_explicit",
        audit,
    )
    text = replace_exact(
        text,
        "  simpa only [correctedSignLevel] using\n"
        "    tendsto_atTop_add_const_right atTop c\n"
        "      (tendsto_natCast_atTop_atTop :\n"
        "        Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)",
        "  change Tendsto (fun n : ℕ => (n : ℝ) + c) atTop atTop\n"
        "  exact tendsto_atTop_add_const_right atTop c\n"
        "    (tendsto_natCast_atTop_atTop :\n"
        "      Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)",
        1,
        "make_corrected_sign_tendsto_target_explicit",
        audit,
    )
    text = replace_exact(
        text,
        "  | .hypA_6 =>\n"
        "      [\"QYM.MassAbsorptionTruncationCore.nonnegative_forms_do_not_imply_positiveDomination\",\n"
        "       \"QYM.FullCertification.PaperNormalized.hypA_6_nonnegativeFormDominationInferenceStatement_refuted\"]\n"
        "  | _ => []",
        "  | .hypA_6 =>\n"
        "      [\"QYM.MassAbsorptionTruncationCore.nonnegative_forms_do_not_imply_positiveDomination\",\n"
        "       \"QYM.FullCertification.PaperNormalized.hypA_6_nonnegativeFormDominationInferenceStatement_refuted\"]",
        1,
        "remove_redundant_claim_match_alternative",
        audit,
    )
    text = replace_exact(
        text,
        "theorem auditRegistry_ids : auditRegistry.map AuditRecord.id = allClaims := by\n"
        "  simp [auditRegistry, record]",
        "theorem auditRegistry_ids : auditRegistry.map AuditRecord.id = allClaims := by\n"
        "  simp only [auditRegistry, List.map_map]\n"
        "  change List.map (fun claim : ClaimId => claim) allClaims = allClaims\n"
        "  simp only [List.map_id]",
        1,
        "make_audit_registry_projection_explicit",
        audit,
    )

    text = replace_exact(
        text,
        "/-- The specified coercivity constant gives the corresponding sharp "
        "operator lower bound. -/\nsection SpecifiedConstantLowerBound",
        "/- The specified coercivity constant gives the corresponding sharp "
        "operator lower bound. -/\nsection SpecifiedConstantLowerBound",
        1,
        "ordinary_comment_before_section",
        audit,
    )
    text = replace_exact(
        text,
        "    mod_cast congr_arg RCLike.re\n",
        "    exact_mod_cast congr_arg RCLike.re\n",
        2,
        "modernize_tactic_mode_mod_cast",
        audit,
    )
    text = replace_exact(
        text,
        "isCompact_iff_isClosed_bounded.mpr",
        "Metric.isCompact_iff_isClosed_bounded.mpr",
        1,
        "qualify_metric_compactness_criterion",
        audit,
    )
    text = replace_exact(
        text,
        "  min |x - y| |2 - |x - y||",
        "  min (abs (x - y)) (abs (2 - abs (x - y)))",
        1,
        "make_nested_absolute_values_parser_explicit",
        audit,
    )

    candidate = text.encode("utf-8")
    if b"\r" in candidate or b"\x00" in candidate or not candidate.endswith(b"\n"):
        raise AssertionError("final probe candidate encoding/newline invariant mismatch")
    output_path = Path(args.output)
    audit_path = Path(args.audit)
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_bytes(candidate)
    result = {
        "schema": "qym-repair-probe-finalizer-v1",
        "input_sha256": EXPECTED_INPUT_SHA256,
        "output_sha256": sha256(candidate),
        "input_bytes": len(raw),
        "output_bytes": len(candidate),
        "input_lf": raw.count(b"\n"),
        "output_lf": candidate.count(b"\n"),
        "rewrites": audit,
    }
    with audit_path.open("w", encoding="utf-8", newline="\n") as handle:
        handle.write(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
