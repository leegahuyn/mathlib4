#!/usr/bin/env python3
"""Conditional Probe11 repairs for exact terminal-Probe10 lines 40000-51999.

Only independent producer/API/parser roots are transformed.  The large
50000-51837 structural cascade and every frozen Probe10/Probe11 helper span are
excluded.  The transformer is byte-locked, exact-counted, reversible, trust0,
and activation-disabled.  It writes only caller-selected new ``work/`` files;
it never invokes Lean, Lake, Git, or the network.
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

SCHEMA = "qym-probe11-40k-p10-conditional-v1-exact-terminal-probe10"
INPUT_SHA256 = "ef19b4f666bd7238164aec7795e10c3f802d9a3e49e5d5f617cc09d4cbe617dc"
INPUT_GIT_BLOB = "496c24e5a90d1f72c66bb03fcc9d3565a06f4b2e"
INPUT_BYTES = 2_923_612
INPUT_LF = 61_783
LOG_SHA256 = "0fa01861e0984e1e45107a46789d894f33d2bbd4a035d9dbaa29060956ab3ad2"
HEADERS_SHA256 = "b1130e19aa9ca16b044eeab07ebf762c0cb2bdfe46c0b7d242ef68b0c151a7a5"
DIAGNOSTICS_SHA256 = "b51f3cc940634dc1eba28003770ae750f8621c4452483f27fdf464188591c43a"

# Sealed after one deterministic bootstrap projection.
OUTPUT_SHA256 = "eb0b22ec98ae72aad0d597a48abe5e93e4b8a177ea2e1cc597988beaf1e331ec"
OUTPUT_GIT_BLOB = "abd110b8139b4d7411009e94d81516ad8434d0d3"
OUTPUT_BYTES = 2_924_722
OUTPUT_LF = 61_813


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
        "selected_horocycle_continuity_pin_action_homeomorph",
        "  exact (continuous_const_smul (gammaTwoCosetRep q)).comp\n"
        "    (QYM.FullCertification.P2ActualFixedPhaseCuspTraceGraphExtension.actualFixedPhaseHorizontalHorocyclePoint_continuous Y)\n",
        "  exact ((Homeomorph.smul (gammaTwoCosetRep q) : ℍ ≃ₜ ℍ).continuous.comp\n"
        "    (QYM.FullCertification.P2ActualFixedPhaseCuspTraceGraphExtension.actualFixedPhaseHorizontalHorocyclePoint_continuous Y))\n",
        (
            Header(42663, 55, "unsolved goals"),
            Header(42669, 9, "failed to synthesize instance of type class", "lean.synthInstanceFailed"),
        ),
        "Pin the codomain homeomorphism so instance search chooses the certified SL(2,Z) action on the upper half-plane.",
        "The same typed action homeomorphism already proves continuity at exact P10 line 35117.",
    ),
    Rule(
        "circular_base_edge_derivative_expose_constructor",
        "      simpa [baseEdgeCoordinate, baseEdgeVelocity,\n"
        "        Complex.mk_eq_add_mul_I] using hx.add (hy.mul_const Complex.I)\n",
        "      change HasDerivAt\n"
        "        (fun s : ℝ =>\n"
        "          Complex.mk (s / 2) (Real.sqrt (1 - (s / 2) ^ 2)))\n"
        "        (Complex.mk ((1 : ℝ) / 2)\n"
        "          (-t / (4 * Real.sqrt (1 - (t / 2) ^ 2)))) t\n"
        "      simpa [Complex.mk_eq_add_mul_I] using\n"
        "        hx.add (hy.mul_const Complex.I)\n",
        (Header(43629, 6, "Type mismatch: After simplification"),),
        "Expose the circular constructor before applying the componentwise derivative producer.",
        "The goal formatter retained baseEdgeCoordinate after the old simplification, while hx.add hy is already the exact expanded curve.",
    ),
    Rule(
        "cusp_transition_integer_power_convert_functions",
        "    cases k with\n"
        "    | ofNat m =>\n"
        "        simpa only [hk, zpow_natCast] using hden.pow m\n"
        "    | negSucc m =>\n"
        "        simpa only [hk, zpow_negSucc] using\n"
        "          (hden.pow (m + 1)).inv\n"
        "            (fun x => pow_ne_zero _ (hdenNe x))\n",
        "    cases k with\n"
        "    | ofNat m =>\n"
        "        convert hden.pow m using 1\n"
        "        funext x\n"
        "        rw [hk, zpow_natCast]\n"
        "    | negSucc m =>\n"
        "        convert (hden.pow (m + 1)).inv\n"
        "          (fun x => pow_ne_zero _ (hdenNe x)) using 1\n"
        "        funext x\n"
        "        rw [hk, zpow_negSucc]\n",
        (
            Header(44067, 8, "Type mismatch: After simplification"),
            Header(44069, 8, "Type mismatch: After simplification"),
        ),
        "Convert the ContDiff functions first, then normalize the integer exponent pointwise in each constructor branch.",
        "The exact diagnostics show only Nat-power versus Int.ofNat/negSucc power shape differences.",
    ),
    Rule(
        "right_normal_orthogonality_finish_ring_nf",
        "  simp [Complex.mul_re]\n",
        "  simp [Complex.mul_re] <;> ring_nf\n",
        (Header(44344, 51, "unsolved goals"),),
        "Normalize the remaining commutator after complex-coordinate simplification.",
        "The exact P10 diagnostic explicitly recommends ring_nf for the residual real polynomial.",
    ),
    Rule(
        "right_normal_real_multiple_finish_ring_nf",
        "  simp [hyperbolicRightNormal, Complex.mul_re, Complex.mul_im]\n"
        "  ring\n",
        "  simp [hyperbolicRightNormal, Complex.mul_re, Complex.mul_im]\n"
        "  ring_nf\n",
        (Header(44356, 61, "unsolved goals"),),
        "Use normalization rather than closure-only ring on the residual coordinate polynomial.",
        "The exact P10 diagnostic explicitly recommends ring_nf for this goal.",
    ),
    Rule(
        "strict_outward_expose_normal_producer",
        "  intro e t ht\n"
        "  rw [conj_mul_hyperbolicRightNormal_im\n"
        "    (orientedActualEdgeVelocity_ne_zero e ht)]\n",
        "  intro e t ht\n"
        "  change\n"
        "    (star (orientedActualEdgeVelocity e t) *\n"
        "      hyperbolicRightNormal\n"
        "        (QYM.FullCertification.P2NormalGreenExtension.actualEdgePoint e t).im\n"
        "        (orientedActualEdgeVelocity e t)).im < 0\n"
        "  rw [conj_mul_hyperbolicRightNormal_im\n"
        "    (orientedActualEdgeVelocity_ne_zero e ht)]\n",
        (Header(44416, 6, "Tactic `rewrite` failed: Did not find an occurrence of the pattern"),),
        "Expose the concrete normal field before rewriting with its signed-area producer.",
        "The exact goal kept actualOutwardHyperbolicUnitNormal opaque while the rewrite theorem targets hyperbolicRightNormal.",
    ),
    Rule(
        "paired_normal_pushforward_unfold_all_normal_occurrences",
        "  rw [actualOutwardHyperbolicUnitNormal, hyperbolicRightNormal]\n"
        "  rw [paired_hyperbolicNormalScale e ht]\n",
        "  simp only [actualOutwardHyperbolicUnitNormal, hyperbolicRightNormal]\n"
        "  rw [paired_hyperbolicNormalScale e ht]\n",
        (Header(44602, 6, "Tactic `rewrite` failed: Did not find an occurrence of the pattern"),),
        "Unfold both normal occurrences, not merely the first rw match, before applying the paired scale identity.",
        "The exact target retained the paired RHS normal wrapper after rw unfolded only the source occurrence.",
    ),
    Rule(
        "conditional_smooth_residual_make_instance_implicit",
        "variable (hSmooth : SmoothTransitionResidual)\n",
        "variable [hSmooth : SmoothTransitionResidual]\n",
        (Header(45114, 0, "This instance has 1 argument that cannot be inferred using typeclass synthesis."),),
        "Make the residual instance-implicit so local HasGroupoid instances have an inferable dependency.",
        "The exact diagnostic identifies hSmooth as the sole explicit argument absent from the instance result type.",
    ),
    Rule(
        "collar_cutoff_limit_change_function_division",
        "  have hquot := hnum.div hden (by simpa using hbump.ne')\n"
        "  simpa only [widthTwoCollarCutoff, Pi.div_apply, add_zero,\n"
        "    div_self hbump.ne'] using hquot\n",
        "  have hquot := hnum.div hden (by simpa using hbump.ne')\n"
        "  change Tendsto\n"
        "    (fun n : ℕ => widthTwoCollarBump x /\n"
        "      (widthTwoCollarBump x + widthTwoCollarScale n))\n"
        "    atTop\n"
        "    (𝓝 (widthTwoCollarBump x / (widthTwoCollarBump x + 0))) at hquot\n"
        "  simpa only [widthTwoCollarCutoff, add_zero,\n"
        "    div_self hbump.ne'] using hquot\n",
        (Header(45529, 2, "Type mismatch: After simplification"),),
        "Beta-reduce the function-valued quotient in the Tendsto witness before closing the pointwise cutoff statement.",
        "The exact diagnostic differs only by (fun _ => a)/(fun n => b n) versus fun n => a/b n.",
    ),
    Rule(
        "horizontal_high_embedding_expose_product_composition",
        "    simpa only [Function.comp_def, Prod.map_apply, id_eq] using\n"
        "      Complex.equivRealProdCLM.symm.toHomeomorph.isOpenEmbedding.comp hProd\n",
        "    change IsOpenEmbedding\n"
        "      (Complex.equivRealProdCLM.symm.toHomeomorph ∘\n"
        "        Prod.map (id : ℝ → ℝ) ((↑) : HighHeight → ℝ))\n"
        "    exact\n"
        "      Complex.equivRealProdCLM.symm.toHomeomorph.isOpenEmbedding.comp hProd\n",
        (Header(46147, 4, "Type mismatch: After simplification"),),
        "Expose the exact homeomorphism-after-product-map composition returned by IsOpenEmbedding.comp.",
        "The exact diagnostic shows only lambda versus composition/Prod.map presentation.",
    ),
    Rule(
        "selected_high_embedding_pin_action_homeomorph",
        "  simpa only [selectedHighPoint, Function.comp_def] using\n"
        "    (Homeomorph.smul (gammaTwoCosetRep q)).isOpenEmbedding.comp\n"
        "      horizontalHighPoint_isOpenEmbedding\n",
        "  change IsOpenEmbedding\n"
        "    ((Homeomorph.smul (gammaTwoCosetRep q) : ℍ ≃ₜ ℍ) ∘\n"
        "      horizontalHighPoint)\n"
        "  exact\n"
        "    (Homeomorph.smul (gammaTwoCosetRep q) : ℍ ≃ₜ ℍ).isOpenEmbedding.comp\n"
        "      horizontalHighPoint_isOpenEmbedding\n",
        (
            Header(46182, 2, "Type mismatch: After simplification"),
            Header(46183, 5, "failed to synthesize instance of type class", "lean.synthInstanceFailed"),
        ),
        "Expose the composition and pin the upper-half-plane action homeomorphism before instance search.",
        "The earlier exact P10 action-homeomorphism uses compile at lines 35117, 38361, and 39073.",
    ),
    Rule(
        "cylinder_quotient_map_expose_typed_product",
        "  simpa only [cylinderQuotientMap] using\n"
        "    (QuotientAddGroup.isOpenQuotientMap_mk.prodMap\n"
        "      IsOpenQuotientMap.id :\n"
        "        IsOpenQuotientMap\n"
        "          (Prod.map\n"
        "            (QuotientAddGroup.mk'\n"
        "              (AddSubgroup.zmultiples (2 : ℝ)))\n"
        "            (id : HighHeight → HighHeight)))\n",
        "  change IsOpenQuotientMap\n"
        "    (Prod.map\n"
        "      (QuotientAddGroup.mk' (AddSubgroup.zmultiples (2 : ℝ)))\n"
        "      (id : HighHeight → HighHeight))\n"
        "  exact QuotientAddGroup.isOpenQuotientMap_mk.prodMap\n"
        "    IsOpenQuotientMap.id\n",
        (Header(46255, 2, "Type mismatch: After simplification"),),
        "Expose the already type-ascribed product quotient map and apply the product producer directly.",
        "The exact diagnostic differs only by the specialized WidthTwoCircle alias and mk coercion presentation.",
    ),
    Rule(
        "band_to_high_cylinder_expose_product_map",
        "  simpa only [bandToHighCylinder, Prod.map_apply, id_eq] using\n"
        "    IsOpenEmbedding.id.prodMap hHeight\n",
        "  change IsOpenEmbedding\n"
        "    (Prod.map\n"
        "      (id : QYM.FullCertification.P2SmoothQuotientAtlasExtension.WidthTwoCircle →\n"
        "        QYM.FullCertification.P2SmoothQuotientAtlasExtension.WidthTwoCircle)\n"
        "      (fun h : CuspBand Y =>\n"
        "        (⟨h.1, cuspBand_height_gt_one hY h⟩ : HighHeight)))\n"
        "  exact IsOpenEmbedding.id.prodMap hHeight\n",
        (Header(46574, 2, "Type mismatch: After simplification"),),
        "Expose the product-map constructor returned by IsOpenEmbedding.prodMap.",
        "The exact diagnostic shows only bandToHighCylinder versus its already-proved product-map expansion.",
    ),
    Rule(
        "negative_horocycle_derivative_beta_reduce_composition",
        "  have h := (selectedHorocycleCoordinate_hasDerivAt q Y (-t)).scomp t\n"
        "    (hasDerivAt_neg t)\n"
        "  simpa [selectedHorocycleBoundaryVelocity] using h\n",
        "  have h := (selectedHorocycleCoordinate_hasDerivAt q Y (-t)).scomp t\n"
        "    (hasDerivAt_neg t)\n"
        "  change HasDerivAt\n"
        "    (fun s => selectedHorocycleCoordinate q Y (-s))\n"
        "    (-explicitSelectedHorocycleVelocity q Y (-t)) t at h\n"
        "  simpa only [selectedHorocycleBoundaryVelocity] using h\n",
        (Header(46996, 2, "Type mismatch: After simplification"),),
        "Beta-reduce the composition produced by scomp before unfolding the named negative velocity.",
        "The exact diagnostic shows identical derivative values and only composition-versus-lambda function shape.",
    ),
)


FOREIGN_HELPERS: tuple[tuple[str, str, str], ...] = (
    ("probe10_earlytail", "qym-probe10-earlytail-static/qym_probe10_earlytail_static.py", "5d7c848db8b8ec238bbdaad29bc5532ae0020f134846d16be064a78372c58434"),
    ("probe10_midlate", "qym-probe10-midlate-static/qym_probe10_midlate_static.py", "42d8f76c68b19aac520d15659c71d02db2e1beb397cfe0865bcdaf436e885be0"),
    ("probe10_late", "qym-probe10-late-static/qym_probe10_late_static.py", "d1c9aef94af3efac77ab5b9b87b2851adbc3eac3fcf7f18e5cc9695a61b7bccd"),
    ("probe10_extendofnorm", "qym-probe10-extendofnorm-instances/qym_probe10_extendofnorm_instances.py", "b7942ba8d0ae94dd2827f5a59560a81a291482880c8716df299cc13dbac246bb"),
    ("probe11_mid_p10", "qym-probe11-mid-p10-authority/qym_probe11_mid_p10_authority.py", "f2adebd8803e40df538a8b85401ea5a26af4585aefe521135c77dde8576a1fc6"),
    ("probe11_tail_p10", "qym-probe11-tail-p10-conditional/qym_probe11_tail_p10_conditional.py", "e76d0830315918d8d51c5063048b0f85ad9f4a68c8dffa2dbab19da25a9aae49"),
    ("probe11_early_frontier_p10", "qym-probe11-early-frontier-static/qym_probe11_early_frontier_static.py", "9177e4fd6aa03215aec4728415d095e7e099594f6bc12facbf5a2fd879175b9a"),
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
    return {"sha256": INPUT_SHA256, "git_blob": INPUT_GIT_BLOB,
            "bytes": INPUT_BYTES, "lf": INPUT_LF, "cr": False, "nul": False,
            "bom": False, "terminal_lf": True}


def output_expected() -> dict[str, object]:
    return {"sha256": OUTPUT_SHA256, "git_blob": OUTPUT_GIT_BLOB,
            "bytes": OUTPUT_BYTES, "lf": OUTPUT_LF, "cr": False, "nul": False,
            "bom": False, "terminal_lf": True}


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
            raise RuntimeError(f"Probe10 {label} identity mismatch: {actual}")
    header_lines = header_raw.decode("utf-8", errors="strict").splitlines()
    rows = [json.loads(line) for line in diagnostics_raw.decode("utf-8", errors="strict").splitlines()]
    if len(header_lines) != 255:
        raise RuntimeError(f"expected 255 exact error headers, got {len(header_lines)}")
    if sum(row.get("severity") == "error" for row in rows) != 255:
        raise RuntimeError("diagnostic error count is not 255")
    if sum(row.get("severity") == "warning" for row in rows) != 343:
        raise RuntimeError("diagnostic warning count is not 343")
    mapped: list[dict[str, object]] = []
    for rule in RULES:
        for header in rule.headers:
            code = f"\\({re.escape(header.code)}\\)" if header.code else ""
            pattern = re.compile(
                rf"^PrimalitySheafVerification/QYM\.lean:{header.line}:{header.column}: "
                rf"error{code}: {re.escape(header.message)}"
            )
            hm = [line for line in header_lines if pattern.match(line)]
            dm = [row for row in rows if row.get("severity") == "error"
                  and row.get("line") == header.line and row.get("column") == header.column
                  and row.get("code") == header.code
                  and str(row.get("message", "")).startswith(header.message)]
            if len(hm) != 1 or len(dm) != 1:
                raise RuntimeError(f"{rule.label}: authority mapping mismatch at {header.line}:{header.column}")
            mapped.append({"rule": rule.label, **header.__dict__, "kind": "independent_direct_root"})
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
        raise RuntimeError(f"foreign helper identity mismatch: {name}")
    module_name = "_qym_40k_foreign_" + name
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
            if not 40000 <= line <= 51999 or line >= 50000:
                raise RuntimeError(f"{rule.label}: scope violation at line {line}")
            own.append((start, end, rule.label))
    equalities: list[dict[str, str]] = []
    overlaps: list[dict[str, object]] = []
    foreign_active_spans = 0
    identities: dict[str, str] = {}
    for name, relative, expected_sha in FOREIGN_HELPERS:
        module = load_foreign(name, relative, expected_sha)
        identities[name] = expected_sha
        for foreign in module.RULES:
            for variant, anchor in (("old", foreign.old), ("new", foreign.new)):
                found = spans(text, anchor)
                foreign_active_spans += len(found)
                for own_rule in RULES:
                    for own_variant, own_anchor in (("old", own_rule.old), ("new", own_rule.new)):
                        if own_anchor == anchor:
                            equalities.append({"own": own_rule.label, "own_variant": own_variant,
                                               "foreign": f"{name}:{foreign.label}", "foreign_variant": variant})
                for fstart, fend in found:
                    for ostart, oend, own_label in own:
                        if max(fstart, ostart) < min(fend, oend):
                            overlaps.append({"own": own_label, "foreign": f"{name}:{foreign.label}",
                                             "foreign_variant": variant,
                                             "own_span": [ostart, oend], "foreign_span": [fstart, fend]})
    if equalities or overlaps:
        raise RuntimeError(f"foreign collision: equalities={equalities}, overlaps={overlaps}")
    return {"foreign_helper_sha256": identities, "own_spans_checked": len(own),
            "foreign_active_spans_checked": foreign_active_spans,
            "exact_anchor_equalities": equalities, "span_overlaps": overlaps}


def apply_rules(text: str, inverse: bool = False) -> tuple[str, list[dict[str, object]]]:
    audits: list[dict[str, object]] = []
    ordered = tuple(reversed(RULES)) if inverse else RULES
    for rule in ordered:
        old, new = (rule.new, rule.old) if inverse else (rule.old, rule.new)
        count = text.count(old)
        if count != rule.occurrences:
            raise RuntimeError(f"{rule.label}: exact anchor count {count}, expected {rule.occurrences}")
        text = text.replace(old, new)
        audits.append({"label": rule.label, "direction": "inverse" if inverse else "forward",
                       "occurrences": count, "headers": [h.__dict__ for h in rule.headers],
                       "rationale": rule.rationale, "precedent": rule.precedent})
    return text, audits


transform = apply_rules


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--probe10-log", type=Path, required=True)
    parser.add_argument("--probe10-error-headers", type=Path, required=True)
    parser.add_argument("--probe10-diagnostics", type=Path, required=True)
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
    check_shape(source_shape, output_expected() if inverse else input_expected(),
                unsealed=args.bootstrap_seal and inverse)
    mapped = verify_authority(args.probe10_log.read_bytes(),
                              args.probe10_error_headers.read_bytes(),
                              args.probe10_diagnostics.read_bytes())
    source_text = source.decode("utf-8", errors="strict")
    collision = audit_collisions(source_text, inverse=inverse)
    before_trust = trust(source_text)
    result_text, rule_audit = apply_rules(source_text, inverse=inverse)
    result = result_text.encode("utf-8")
    result_shape = shape(result)
    check_shape(result_shape, input_expected() if inverse else output_expected(),
                unsealed=args.bootstrap_seal and not inverse)
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
        "status": "STATIC_PASS_EXACT_TERMINAL_PROBE10_NOT_LEAN_EXECUTED",
        "activation": False,
        "promotion": False,
        "mode": args.mode,
        "authority": {"candidate_sha256": INPUT_SHA256, "candidate_git_blob": INPUT_GIT_BLOB,
                      "log_sha256": LOG_SHA256, "error_headers_sha256": HEADERS_SHA256,
                      "diagnostics_sha256": DIAGNOSTICS_SHA256,
                      "errors": 255, "warnings": 343, "panic": 0, "exit": 1},
        "scope": {"candidate_lines": [40000, 51999], "selected_below_line": 50000,
                  "independent_direct_roots_only": True,
                  "structural_50000_51837_cluster_excluded": True,
                  "foreign_helper_span_overlap": False,
                  "cascade_diagnostics_selected": False},
        "source": source_shape,
        "result": result_shape,
        "repair_families": len(RULES),
        "repair_occurrences": sum(item["occurrences"] for item in rule_audit),
        "direct_diagnostics": len(mapped),
        "selected_exact_probe10_lines": sorted({h.line for r in RULES for h in r.headers}),
        "diagnostic_map": mapped,
        "rules": rule_audit,
        "collision_audit": collision,
        "inverse_byte_equal": True,
        "trust": after_trust,
        "execution": {"lean": False, "lake": False, "git": False, "network": False,
                      "remote": False, "repository_source_mutation": False},
    }
    args.output.write_bytes(result)
    args.audit.write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(json.dumps(record, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
