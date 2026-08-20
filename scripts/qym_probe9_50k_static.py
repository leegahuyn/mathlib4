#!/usr/bin/env python3
"""Conditional static Probe9 projection for exact Probe8 QYM lines 50000--54999.

The transform is byte-locked to the terminal Probe8 candidate and diagnostic
artifacts.  It activates no promotion: the generated tranche remains
conditional until a terminal Probe9 execution validates the projection.
No Lean, Lake, Git, network, remote, or canonical-source operation is invoked.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import runpy
from dataclasses import dataclass
from pathlib import Path


SCHEMA = "qym-probe9-50k-static-transform-v2-exact-probe8"
INPUT_SHA256 = "63baae8766e3208ac1d8dfa66946ac5ae3cf4a4264d21218a1ccb17aed3c4fd8"
INPUT_GIT_BLOB = "a2d3f4f60018fc2bfebd904db17aa13025c39ed6"
INPUT_BYTES = 2_916_737
INPUT_LF = 61_671
LOG_SHA256 = "4408bf46825d32a935de970904c711510b774ef93026fbee3e20dbc18392beea"
ERROR_HEADERS_SHA256 = "9f0d91787942db9470e307c5a44d8523b2b362ad31f737da0eb48b3f9f2d181f"
HEADER_LINE_SHIFT = 78

OUTPUT_SHA256 = "a88a419b821e5128ad97ff3d853017bcbe73cfadaa5236064d4104b477343641"
OUTPUT_GIT_BLOB = "a9ed3cf38f3409f1aac8721711d5458bea78605f"
OUTPUT_BYTES = 2_917_207
OUTPUT_LF = 61_681

FOREIGN_HELPER_SHA256 = {
    "qym_probe7_reanchored.py":
        "1919650925df78ea6b87a742937ba4c57cd1e3eeb123d5a2111131189a4fa53a",
    "qym_probe8_early_independent.py":
        "67843a8608038295f570bb15feb8f08cbb6d90f9c166d078fecde9e1ba215cf4",
    "qym_probe8_mid_static.py":
        "b529f1df682a1e9b1588399f3a951914452d1d9afb049dd7be22cef1d8570dbf",
    "qym_probe8_late_static.py":
        "4b3470fa2296d61002460e6f8532402f0509ae8c3385f36b512a732ad55c8f9f",
}


@dataclass(frozen=True)
class Header:
    line: int
    column: int
    message: str

    def __post_init__(self) -> None:
        # All surviving direct headers moved uniformly by the exact Probe8
        # composition.  Normalize the Probe7-authored table at construction.
        object.__setattr__(self, "line", self.line + HEADER_LINE_SHIFT)


@dataclass(frozen=True)
class Rule:
    label: str
    old: str
    new: str
    headers: tuple[Header, ...]
    occurrences: int = 1
    rationale: str = ""


RULES: tuple[Rule, ...] = (
    Rule(
        "petersson_self_nonneg_fix_complex_scalar",
        "theorem actualStagePeterssonInner_self_re_nonneg\n"
        "    {Y : ℝ} (u : ActualStageInverseEtaL2Section Y) :\n"
        "    0 ≤ (actualStagePeterssonInner u u).re := by\n"
        "  unfold actualStagePeterssonInner\n"
        "  exact inner_self_nonneg\n",
        "theorem actualStagePeterssonInner_self_re_nonneg\n"
        "    {Y : ℝ} (u : ActualStageInverseEtaL2Section Y) :\n"
        "    0 ≤ (actualStagePeterssonInner u u).re := by\n"
        "  unfold actualStagePeterssonInner\n"
        "  exact inner_self_nonneg (𝕜 := ℂ)\n",
        (Header(50027, 8, "typeclass instance problem is stuck"),),
        rationale="Fix the inner-product scalar to Complex.",
    ),
    Rule(
        "petersson_definiteness_expose_complex_inner",
        "  simp only [actualStagePeterssonInner, inner_self_eq_norm_sq,\n"
        "    sq_eq_zero_iff, norm_eq_zero]\n",
        "  change (inner ℂ u u).re = 0 ↔ u = 0\n"
        "  rw [inner_self_eq_norm_sq (𝕜 := ℂ),\n"
        "    sq_eq_zero_iff, norm_eq_zero]\n",
        (Header(50032, 54, "unsolved goals"),),
        rationale="Expose the Complex inner product before the norm-square rewrite.",
    ),
    Rule(
        "distinguished_coordinate_unfold_lp_const",
        "  simpa only [actualStageFibreValue_coordinate,\n"
        "    Function.const_apply] using hx\n",
        "  simpa only [actualStageDistinguishedInverseEtaSection,\n"
        "    actualStageFibreValue_coordinate, Function.const_apply] using hx\n",
        (Header(50238, 2, "Type mismatch: After simplification"),),
        rationale="Unfold the named distinguished section to the Lp.const representative in hx.",
    ),
    Rule(
        "strict_cusp_band_beta_reduce_membership",
        "  simpa only [QYM.FullCertification.P2StageManifoldWithBoundaryExtension.stageBandInclusion_apply,\n"
        "    QYM.FullCertification.P2StageManifoldWithBoundaryExtension.oneSidedHeightToCuspBand_coe] using hp\n",
        "  change (p.2 : ℝ) <\n"
        "    Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.gammaTwoCuspLevel Y at hp\n"
        "  exact hp\n",
        (Header(51560, 2, "Type mismatch: After simplification"),),
        rationale="Beta-reduce membership in the local strict cusp-band set.",
    ),
    Rule(
        "boundary_closure_transport_by_point_equality",
        "  rw [htheta] at hClosure\n"
        "  exact hClosure\n",
        "  exact htheta ▸ hClosure\n",
        (Header(51596, 6, "Tactic `rewrite` failed"),),
        rationale="Transport the closure proof directly along the point equality.",
    ),
    Rule(
        "continuous_to_l2_one_unfold_distinguished_lp_const",
        "  simpa only [actualStageContinuousInverseEtaOne,\n"
        "    ContinuousMap.const_apply] using hx.trans hOne.symm\n",
        "  simpa only [actualStageContinuousInverseEtaOne,\n"
        "    QYM.FullCertification.P3ActualStageL2SectionsExtension.actualStageDistinguishedInverseEtaSection,\n"
        "    ContinuousMap.const_apply] using hx.trans hOne.symm\n",
        (Header(51883, 2, "Type mismatch: After simplification"),),
        rationale="Unfold the named distinguished section to the same Lp.const used by hOne.",
    ),
    Rule(
        "discriminant_mul_add_remove_stale_product_rewrites",
        "        (actualStageDiscriminantMul Y v)]\n"
        "    with x hsum hu hv huv hout\n"
        "  rw [hsum, hout, actualStageDiscriminantProduct_apply,\n"
        "    actualStageDiscriminantProduct_apply,\n"
        "    actualStageDiscriminantProduct_apply, huv, hu, hv, mul_add]\n",
        "        (actualStageDiscriminantMul Y v)]\n"
        "    with x hsum hu hv huv hout\n"
        "  rw [hsum, hout, huv, Pi.add_apply, hu, hv, mul_add]\n",
        (Header(52773, 4, "Tactic `rewrite` failed"),),
        rationale="The product delta-reduces after hsum; expose the remaining pointwise addition.",
    ),
    Rule(
        "discriminant_mul_smul_remove_stale_product_rewrites",
        "        (actualStageDiscriminantMul Y u)]\n"
        "    with x hleft hu hcu hright\n"
        "  rw [hleft, hright, actualStageDiscriminantProduct_apply,\n"
        "    actualStageDiscriminantProduct_apply, hcu, hu]\n"
        "  simp only [Pi.smul_apply, smul_eq_mul]\n"
        "  ring\n",
        "        (actualStageDiscriminantMul Y u)]\n"
        "    with x hleft hu hcu hright\n"
        "  rw [hleft, hright, hcu, Pi.smul_apply, hu]\n"
        "  simp only [smul_eq_mul]\n"
        "  ring\n",
        (Header(52790, 4, "Tactic `rewrite` failed"),),
        rationale="The product delta-reduces after hleft; expose the remaining pointwise smul.",
    ),
    Rule(
        "discriminant_operator_ae_change_named_product",
        "  simpa only [actualStageDiscriminantPotentialOperator_apply,\n"
        "    actualStageDiscriminantProduct_apply] using\n"
        "    actualStageDiscriminantMul_coeFn_ae Y u\n",
        "  change\n"
        "    ((actualStageDiscriminantMul Y u :\n"
        "        QYM.FullCertification.P3ActualStageL2SectionsExtension.ActualStageInverseEtaL2Section Y) :\n"
        "      QYM.FullCertification.P2IntrinsicTruncatedQuotientExtension.X Y → ℂ) =ᵐ[\n"
        "        QYM.FullCertification.P3ActualStageL2SectionsExtension.actualStageMeasure Y]\n"
        "      actualStageDiscriminantProduct Y u\n"
        "  exact actualStageDiscriminantMul_coeFn_ae Y u\n",
        (Header(52842, 2, "Type mismatch: After simplification"),),
        rationale="State the named representative equality consumed by the existing ae theorem.",
    ),
    Rule(
        "discriminant_inner_symmetry_fix_complex_scalar",
        "          ((actualStageDiscriminantPotential Y x : ℂ) • v x) by\n"
        "      rw [InnerProductSpace.Core.inner_smul_ofReal_left, InnerProductSpace.Core.inner_smul_ofReal_right])\n",
        "          ((actualStageDiscriminantPotential Y x : ℂ) • v x) by\n"
        "      rw [InnerProductSpace.Core.inner_smul_ofReal_left (𝕜 := ℂ),\n"
        "        InnerProductSpace.Core.inner_smul_ofReal_right (𝕜 := ℂ)])\n",
        (Header(52880, 10, "Tactic `rewrite` failed"),),
        rationale="Fix the Complex inner-product scalar for the two real-smul rewrites.",
    ),
    Rule(
        "discriminant_form_integral_re_fix_complex_scalar",
        "  rw [← integral_re\n"
        "    (MeasureTheory.L2.integrable_inner u\n"
        "      (actualStageDiscriminantPotentialOperator Y u))]\n",
        "  rw [← integral_re (𝕜 := ℂ)\n"
        "    (MeasureTheory.L2.integrable_inner u\n"
        "      (actualStageDiscriminantPotentialOperator Y u))]\n",
        (Header(52974, 6, "Tactic `rewrite` failed"),),
        rationale="Fix the RCLike scalar in the real-part integral rewrite.",
    ),
    Rule(
        "sector_discriminant_ae_expose_pi_smul",
        "  rw [actualStageSectorDiscriminantPotentialOperator_apply, hsmul, hbase]\n",
        "  rw [actualStageSectorDiscriminantPotentialOperator_apply, hsmul,\n"
        "    Pi.smul_apply, hbase]\n",
        (Header(53138, 67, "Tactic `rewrite` failed"),),
        rationale="Expose function-valued scalar multiplication before applying hbase.",
    ),
    Rule(
        "sector_discriminant_inner_symmetry_fix_complex_scalar",
        "    InnerProductSpace.Core.inner_smul_ofReal_left, InnerProductSpace.Core.inner_smul_ofReal_right,\n"
        "    actualStageDiscriminantPotentialOperator_inner_symmetric Y u v]\n",
        "    InnerProductSpace.Core.inner_smul_ofReal_left (𝕜 := ℂ),\n"
        "    InnerProductSpace.Core.inner_smul_ofReal_right (𝕜 := ℂ),\n"
        "    actualStageDiscriminantPotentialOperator_inner_symmetric Y u v]\n",
        (Header(53200, 4, "Tactic `rewrite` failed"),),
        rationale="Fix the Complex inner-product scalar for the sector coefficient rewrites.",
    ),
    Rule(
        "sqrt_mul_add_remove_stale_product_rewrites",
        "        (actualStageDiscriminantSqrtMul Y v)]\n"
        "    with x hsum hu hv huv hout\n"
        "  rw [hsum, hout, actualStageDiscriminantSqrtProduct_apply,\n"
        "    actualStageDiscriminantSqrtProduct_apply,\n"
        "    actualStageDiscriminantSqrtProduct_apply, huv, hu, hv, mul_add]\n",
        "        (actualStageDiscriminantSqrtMul Y v)]\n"
        "    with x hsum hu hv huv hout\n"
        "  rw [hsum, hout, huv, Pi.add_apply, hu, hv, mul_add]\n",
        (Header(53847, 4, "Tactic `rewrite` failed"),),
        rationale="The sqrt product delta-reduces after hsum; expose pointwise addition.",
    ),
    Rule(
        "sqrt_mul_smul_remove_stale_product_rewrites",
        "        (actualStageDiscriminantSqrtMul Y u)]\n"
        "    with x hleft hu hcu hright\n"
        "  rw [hleft, hright, actualStageDiscriminantSqrtProduct_apply,\n"
        "    actualStageDiscriminantSqrtProduct_apply, hcu, hu]\n"
        "  simp only [Pi.smul_apply, smul_eq_mul]\n"
        "  ring\n",
        "        (actualStageDiscriminantSqrtMul Y u)]\n"
        "    with x hleft hu hcu hright\n"
        "  rw [hleft, hright, hcu, Pi.smul_apply, hu]\n"
        "  simp only [smul_eq_mul]\n"
        "  ring\n",
        (Header(53864, 4, "Tactic `rewrite` failed"),),
        rationale="The sqrt product delta-reduces after hleft; expose pointwise smul.",
    ),
    Rule(
        "sqrt_operator_ae_change_named_product",
        "  simpa only [actualStageDiscriminantSqrtOperator_apply,\n"
        "    actualStageDiscriminantSqrtProduct_apply] using\n"
        "    actualStageDiscriminantSqrtMul_coeFn_ae Y u\n",
        "  change\n"
        "    ((actualStageDiscriminantSqrtMul Y u :\n"
        "        QYM.FullCertification.P3ActualStageL2SectionsExtension.ActualStageInverseEtaL2Section Y) :\n"
        "      QYM.FullCertification.P2IntrinsicTruncatedQuotientExtension.X Y → ℂ) =ᵐ[\n"
        "        QYM.FullCertification.P3ActualStageL2SectionsExtension.actualStageMeasure Y]\n"
        "      actualStageDiscriminantSqrtProduct Y u\n"
        "  exact actualStageDiscriminantSqrtMul_coeFn_ae Y u\n",
        (Header(53917, 2, "Type mismatch: After simplification"),),
        rationale="State the named sqrt representative equality consumed by the ae theorem.",
    ),
    Rule(
        "sqrt_inner_symmetry_fix_complex_scalar",
        "          ((actualStageDiscriminantSqrtPotential Y x : ℂ) • v x) by\n"
        "      rw [InnerProductSpace.Core.inner_smul_ofReal_left, InnerProductSpace.Core.inner_smul_ofReal_right])\n",
        "          ((actualStageDiscriminantSqrtPotential Y x : ℂ) • v x) by\n"
        "      rw [InnerProductSpace.Core.inner_smul_ofReal_left (𝕜 := ℂ),\n"
        "        InnerProductSpace.Core.inner_smul_ofReal_right (𝕜 := ℂ)])\n",
        (Header(53956, 10, "Tactic `rewrite` failed"),),
        rationale="Fix the Complex scalar in the sqrt real-smul inner rewrites.",
    ),
    Rule(
        "form_self_complex_ext_reduce_ofreal_parts",
        "  · simpa using\n"
        "      actualStageDiscriminantForm_self_re_eq_sqrt_norm_sq Y u\n"
        "  · simpa using QYM.FullCertification.P6ActualStageDiscriminantPotentialExtension.actualStageDiscriminantForm_self_im_eq_zero Y u\n",
        "  · simpa only [Complex.ofReal_re] using\n"
        "      actualStageDiscriminantForm_self_re_eq_sqrt_norm_sq Y u\n"
        "  · simpa only [Complex.ofReal_im] using\n"
        "      QYM.FullCertification.P6ActualStageDiscriminantPotentialExtension.actualStageDiscriminantForm_self_im_eq_zero Y u\n",
        (
            Header(54054, 4, "Type mismatch: After simplification"),
            Header(54056, 4, "Type mismatch: After simplification"),
        ),
        rationale="Reduce the real and imaginary parts of the embedded real norm square.",
    ),
    Rule(
        "sqrt_lower_bound_norm_expose_pi_smul",
        "    rw [hleft, hright, norm_smul, norm_mul, Complex.norm_real,\n"
        "      Real.norm_of_nonneg (Real.sqrt_nonneg _),\n"
        "      norm_actualStageDiscriminantSqrtPotentialComplex]\n",
        "    rw [hleft, hright, Pi.smul_apply, norm_smul, norm_mul,\n"
        "      Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),\n"
        "      norm_actualStageDiscriminantSqrtPotentialComplex]\n",
        (Header(54160, 23, "Tactic `rewrite` failed"),),
        rationale="Expose pointwise scalar multiplication before rewriting its norm.",
    ),
    Rule(
        "potential_lower_bound_norm_expose_pi_smul",
        "    rw [hleft, hright, norm_smul, norm_mul, Complex.norm_real,\n"
        "      Real.norm_of_nonneg\n"
        "        (actualStageDiscriminantPotentialLowerBound_pos Y).le,\n",
        "    rw [hleft, hright, Pi.smul_apply, norm_smul, norm_mul,\n"
        "      Complex.norm_real, Real.norm_of_nonneg\n"
        "        (actualStageDiscriminantPotentialLowerBound_pos Y).le,\n",
        (Header(54219, 23, "Tactic `rewrite` failed"),),
        rationale="Expose pointwise scalar multiplication in the potential lower-bound estimate.",
    ),
    Rule(
        "sector_sqrt_inner_symmetry_fix_complex_scalar",
        "    InnerProductSpace.Core.inner_smul_ofReal_left, InnerProductSpace.Core.inner_smul_ofReal_right,\n"
        "    actualStageDiscriminantSqrtOperator_inner_symmetric Y u v]\n",
        "    InnerProductSpace.Core.inner_smul_ofReal_left (𝕜 := ℂ),\n"
        "    InnerProductSpace.Core.inner_smul_ofReal_right (𝕜 := ℂ),\n"
        "    actualStageDiscriminantSqrtOperator_inner_symmetric Y u v]\n",
        (Header(54441, 4, "Tactic `rewrite` failed"),),
        rationale="Fix the Complex scalar in the sector sqrt coefficient rewrites.",
    ),
)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git_blob(data: bytes) -> str:
    return hashlib.sha1(
        b"blob " + str(len(data)).encode("ascii") + b"\0" + data
    ).hexdigest()


def shape(data: bytes) -> dict[str, object]:
    data.decode("utf-8")
    return {
        "sha256": sha256(data),
        "git_blob": git_blob(data),
        "bytes": len(data),
        "lf": data.count(b"\n"),
        "cr": b"\r" in data,
        "nul": b"\0" in data,
        "bom": data.startswith(b"\xef\xbb\xbf"),
        "terminal_lf": data.endswith(b"\n"),
    }


def trust(text: str) -> dict[str, int]:
    return {
        "sorry": len(re.findall(r"\bsorry\b", text)),
        "admit": len(re.findall(r"\badmit\b", text)),
        "native_decide": len(re.findall(r"\bnative_decide\b", text)),
        "Lean.ofReduceBool": text.count("Lean.ofReduceBool"),
        "axiom_declaration": len(re.findall(r"(?m)^\s*axiom\s+", text)),
        "unsafe_declaration": len(re.findall(r"(?m)^\s*unsafe\s+", text)),
        "maxHeartbeats_zero": len(
            re.findall(r"set_option\s+maxHeartbeats\s+0\b", text)
        ),
    }


def expected(inverse: bool, result: bool) -> tuple[str, str, int, int]:
    source = (INPUT_SHA256, INPUT_GIT_BLOB, INPUT_BYTES, INPUT_LF)
    output = (OUTPUT_SHA256, OUTPUT_GIT_BLOB, OUTPUT_BYTES, OUTPUT_LF)
    if inverse:
        source, output = output, source
    return output if result else source


def check_shape(
    actual: dict[str, object],
    wanted: tuple[str, str, int, int],
    *,
    allow_unsealed: bool = False,
) -> None:
    if wanted[0] == "__TO_SEAL__" and allow_unsealed:
        return
    for key, value in zip(("sha256", "git_blob", "bytes", "lf"), wanted, strict=True):
        if actual[key] != value:
            raise RuntimeError(f"{key}: {actual[key]} != {value}")
    if actual["cr"] or actual["nul"] or actual["bom"] or not actual["terminal_lf"]:
        raise RuntimeError(f"text hygiene failure: {actual}")


def verify_authority(log: bytes, error_headers: bytes) -> list[dict[str, object]]:
    if sha256(log) != LOG_SHA256:
        raise RuntimeError(f"Probe8 log sha256 {sha256(log)} != {LOG_SHA256}")
    if sha256(error_headers) != ERROR_HEADERS_SHA256:
        raise RuntimeError(
            f"Probe8 error-header sha256 {sha256(error_headers)} != "
            f"{ERROR_HEADERS_SHA256}"
        )
    log_text = log.decode("utf-8")
    log_error_lines = [
        line for line in log_text.splitlines()
        if re.match(
            r"^PrimalitySheafVerification/QYM\.lean:\d+:\d+: "
            r"error(?:\([^)]*\))?: ",
            line,
        )
    ]
    if log_error_lines != error_headers.decode("utf-8").splitlines():
        raise RuntimeError("Probe8 error-header artifact differs from the log")
    if len(log_error_lines) != 344:
        raise RuntimeError(f"Probe8 error count {len(log_error_lines)} != 344")
    warning_count = len(
        re.findall(
            r"(?m)^PrimalitySheafVerification/QYM\.lean:\d+:\d+: "
            r"warning(?:\([^)]*\))?: ",
            log_text,
        )
    )
    if warning_count != 374:
        raise RuntimeError(f"Probe8 warning count {warning_count} != 374")

    verified: list[dict[str, object]] = []
    for rule in RULES:
        for header in rule.headers:
            pattern = re.compile(
                rf"PrimalitySheafVerification/QYM\.lean:{header.line}:{header.column}: "
                rf"error(?:\([^\n)]*\))?: {re.escape(header.message)}"
            )
            count = len(pattern.findall(log_text))
            if count != 1:
                raise RuntimeError(
                    f"{rule.label}: diagnostic {header.line}:{header.column} "
                    f"{header.message!r} count {count}, expected 1"
                )
            verified.append(
                {
                    "rule": rule.label,
                    "line": header.line,
                    "column": header.column,
                    "message": header.message,
                    "count": count,
                }
            )
    return verified


def transform(text: str, inverse: bool) -> tuple[str, list[dict[str, object]]]:
    audit: list[dict[str, object]] = []
    rules = tuple(reversed(RULES)) if inverse else RULES
    for rule in rules:
        old, new = (rule.new, rule.old) if inverse else (rule.old, rule.new)
        count = text.count(old)
        if count != rule.occurrences:
            raise RuntimeError(
                f"{rule.label}: exact count {count}, expected {rule.occurrences}"
            )
        text = text.replace(old, new)
        audit.append(
            {
                "label": rule.label,
                "direction": "inverse" if inverse else "forward",
                "occurrences": count,
                "headers": [
                    {"line": h.line, "column": h.column, "message": h.message}
                    for h in rule.headers
                ],
                "rationale": rule.rationale,
            }
        )
    return text, audit


def spans(text: str, needle: str) -> list[tuple[int, int]]:
    found: list[tuple[int, int]] = []
    start = 0
    while True:
        index = text.find(needle, start)
        if index < 0:
            return found
        found.append((index, index + len(needle)))
        start = index + 1


def collision_audit(base_text: str, helper_paths: list[Path]) -> dict[str, object]:
    if {path.name for path in helper_paths} != set(FOREIGN_HELPER_SHA256):
        raise RuntimeError("foreign helper set is not exactly Probe7 plus Probe8 early/mid/late")

    own_spans: list[tuple[int, int, str]] = []
    for rule in RULES:
        matches = spans(base_text, rule.old)
        if len(matches) != rule.occurrences:
            raise RuntimeError(
                f"{rule.label}: collision audit count {len(matches)} != {rule.occurrences}"
            )
        own_spans.extend((start, end, rule.label) for start, end in matches)

    foreign_spans: list[tuple[int, int, str, str]] = []
    identities: dict[str, str] = {}
    exact_anchor_equalities = 0
    consumed_foreign_rules: list[str] = []
    own_anchors = {anchor for rule in RULES for anchor in (rule.old, rule.new)}
    for path in helper_paths:
        data = path.read_bytes()
        digest = sha256(data)
        expected_digest = FOREIGN_HELPER_SHA256[path.name]
        if digest != expected_digest:
            raise RuntimeError(f"foreign helper {path.name} sha256 {digest} != {expected_digest}")
        identities[path.name] = digest
        module = runpy.run_path(str(path))
        foreign_rules = module.get("RULES") or module.get("REPAIRS")
        if not isinstance(foreign_rules, tuple):
            raise RuntimeError(f"foreign helper {path.name} has no tuple rule table")
        active_new = path.name in {
            "qym_probe7_reanchored.py",
            "qym_probe8_early_independent.py",
            "qym_probe8_mid_static.py",
            "qym_probe8_late_static.py",
        }
        for foreign_rule in foreign_rules:
            old = getattr(foreign_rule, "old")
            new = getattr(foreign_rule, "new")
            exact_anchor_equalities += int(old in own_anchors) + int(new in own_anchors)
            active_anchor = new if active_new else old
            expected_count = int(getattr(foreign_rule, "occurrences", 1))
            matches = spans(base_text, active_anchor)
            if len(matches) != expected_count:
                alternate = old if active_new else new
                alternate_matches = spans(base_text, alternate)
                if not matches and len(alternate_matches) == expected_count:
                    matches = alternate_matches
                elif not matches and not alternate_matches:
                    consumed_foreign_rules.append(
                        f"{path.name}:{getattr(foreign_rule, 'label')}"
                    )
                    continue
                else:
                    raise RuntimeError(
                        f"foreign {path.name}:{getattr(foreign_rule, 'label')} "
                        f"active/alternate counts {len(matches)}/{len(alternate_matches)} "
                        f"!= {expected_count}"
                    )
            foreign_spans.extend(
                (start, end, path.name, getattr(foreign_rule, "label"))
                for start, end in matches
            )
    if exact_anchor_equalities:
        raise RuntimeError(f"foreign exact-anchor equality count {exact_anchor_equalities}")

    overlaps: list[dict[str, object]] = []
    for own_start, own_end, own_label in own_spans:
        for foreign_start, foreign_end, helper_name, foreign_label in foreign_spans:
            if own_start < foreign_end and foreign_start < own_end:
                overlaps.append(
                    {
                        "own": own_label,
                        "foreign_helper": helper_name,
                        "foreign_rule": foreign_label,
                    }
                )
    if overlaps:
        raise RuntimeError(f"foreign anchor-span overlaps: {overlaps}")
    return {
        "foreign_helper_sha256": identities,
        "foreign_rule_spans_checked": len(foreign_spans),
        "own_rule_spans_checked": len(own_spans),
        "foreign_rules_consumed_by_downstream": consumed_foreign_rules,
        "exact_anchor_equalities": exact_anchor_equalities,
        "span_overlaps": overlaps,
        "pass": True,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--probe8-log", type=Path, required=True)
    parser.add_argument("--probe8-error-headers", type=Path, required=True)
    parser.add_argument("--foreign-helper", action="append", type=Path, required=True)
    parser.add_argument("--audit", type=Path, required=True)
    parser.add_argument("--mode", choices=("forward", "inverse"), default="forward")
    parser.add_argument("--bootstrap-seal", action="store_true")
    args = parser.parse_args()
    inverse = args.mode == "inverse"

    source = args.input.read_bytes()
    source_shape = shape(source)
    check_shape(
        source_shape,
        expected(inverse, False),
        allow_unsealed=args.bootstrap_seal and inverse,
    )
    diagnostic_map = verify_authority(
        args.probe8_log.read_bytes(),
        args.probe8_error_headers.read_bytes(),
    )
    source_text = source.decode("utf-8")
    foreign_audit = None
    if not inverse:
        foreign_audit = collision_audit(source_text, args.foreign_helper)

    before_trust = trust(source_text)
    result_text, rule_audit = transform(source_text, inverse)
    result = result_text.encode("utf-8")
    result_shape = shape(result)
    check_shape(
        result_shape,
        expected(inverse, True),
        allow_unsealed=args.bootstrap_seal and not inverse,
    )
    after_trust = trust(result_text)
    if before_trust != after_trust or any(after_trust.values()):
        raise RuntimeError(f"trust inventory failure: {before_trust} -> {after_trust}")
    restored_text, _ = transform(result_text, not inverse)
    if restored_text.encode("utf-8") != source:
        raise RuntimeError("opposite transform did not restore source byte-for-byte")
    if args.output.exists() or args.audit.exists():
        raise RuntimeError("refusing to overwrite output or audit")

    selected_coordinates = {
        (header.line, header.column)
        for rule in RULES for header in rule.headers
    }
    header_pattern = re.compile(
        r"^PrimalitySheafVerification/QYM\.lean:(\d+):(\d+): "
        r"error(?:\(([^\n)]*)\))?: (.*)$",
        re.MULTILINE,
    )
    all_scope_headers = [
        {
            "line": int(line),
            "column": int(column),
            "code": code or None,
            "message": message,
        }
        for line, column, code, message in header_pattern.findall(
            args.probe8_log.read_text(encoding="utf-8")
        )
        if 50_000 <= int(line) <= 54_999
    ]
    unselected = [
        header for header in all_scope_headers
        if (int(header["line"]), int(header["column"])) not in selected_coordinates
    ]
    record = {
        "schema": SCHEMA,
        "status": "CONDITIONAL_STATIC_PASS_EXACT_PROBE8_NOT_LEAN_EXECUTED",
        "activation": False,
        "promotion": False,
        "activation_gate": "TERMINAL_PROBE9_EXECUTION_REQUIRED",
        "mode": args.mode,
        "authority": {
            "probe8_run_id": 31969310662,
            "probe8_candidate_sha256": INPUT_SHA256,
            "probe8_candidate_git_blob": INPUT_GIT_BLOB,
            "probe8_log_sha256": LOG_SHA256,
            "probe8_error_headers_sha256": ERROR_HEADERS_SHA256,
            "probe8_error_headers": 344,
            "probe8_warning_headers": 374,
            "probe8_exit": 1,
            "probe8_panic": 0,
        },
        "scope": {
            "candidate_lines": [50000, 54999],
            "direct_producer_roots_only": True,
            "existing_probe7_or_probe8_anchor_overlap": False,
            "upstream_owned_cascades_patched": False,
        },
        "source": source_shape,
        "result": result_shape,
        "repair_families": len(RULES),
        "active_occurrences": sum(item["occurrences"] for item in rule_audit),
        "direct_headers_verified": len(diagnostic_map),
        "rules": rule_audit,
        "selected_exact_probe8_diagnostics": diagnostic_map,
        "scope_error_headers": len(all_scope_headers),
        "deliberate_unselected_scope_error_headers": unselected,
        "foreign_anchor_collision_audit": foreign_audit,
        "inverse_byte_equal": True,
        "trust": after_trust,
        "execution": {
            "lean": False,
            "lake": False,
            "git_mutation": False,
            "network": False,
            "remote": False,
            "canonical_source_mutation": False,
        },
    }
    args.output.write_bytes(result)
    args.audit.write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(record, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
