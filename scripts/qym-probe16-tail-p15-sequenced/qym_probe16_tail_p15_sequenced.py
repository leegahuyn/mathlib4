#!/usr/bin/env python3
"""Activation-disabled exact-Probe15 tail refinements for QYM.

Eight exact-counted reversible rules own nine direct Probe15 diagnostics in
lines 55,722--59,213. The broad quotient bridge and uncertain Hamiltonian
transport/simp roots are deliberately excluded. No Lean/Lake/Git/network
action is performed.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import re
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from types import ModuleType

sys.dont_write_bytecode = True

SCHEMA = "qym-probe16-tail-exact-p15-sequenced-v2"
ACTIVATION = False
INSTALL_TARGET = "scripts/qym-probe16-tail-p15-sequenced/qym_probe16_tail_p15_sequenced.py"

INPUT_SHA256 = "9cd10544c82d5871d1cb336b1816b80c310e8413f051284db0261efcd676c7b6"
INPUT_GIT_BLOB = "c604421ed340e71fe3e24d3a7d391115990882ec"
INPUT_BYTES = 2_941_554
INPUT_LF = 62_190
OUTPUT_SHA256 = "ce8fc72801741ae7a4a8c203f972e65aca2c53beb3b75b72dfdd7cc0feef6e67"
OUTPUT_GIT_BLOB = "1ab924ef0363bdfe2de652fc7121b06c13a1c075"
OUTPUT_BYTES = 2_941_876
OUTPUT_LF = 62_198

RUN_ID = 31992267418
JOB_ID = 95277790400
ARTIFACT_ID = 9275890870
TRIGGER_SHA = "1679e9e9f916e95d5a4fe10f9e59502471c84191"
ZIP_SHA256 = "b6f435c38aa5e712b32511025ab95720f8e7e0a34b0b0cccc5ef021bbcdddc07"
RESULT_SHA256 = "0254b92c4ce85a80a10f42f6038bf4fd6787411f84bae20a0abc0af638584853"
LOG_SHA256 = "8722d57acddee9696debb88d34a586ba4b28adbf9d2f64ca8b0500198a0db511"
HEADERS_SHA256 = "1c7ad5d2a165913802412602a9e4b37e719ce69bc1da8c0a1b74ad5e5df98381"
DIAGNOSTICS_SHA256 = "54e83aa0f8f792efc92b1a509729001e0049a87bb8ae5705b48792086bf6df58"
EXPECTED_ERRORS = 100
EXPECTED_WARNINGS = 350


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
    consumed_owner: str | None = None
    consumed_rule: str | None = None
    relation: str | None = None
    occurrences: int = 1


RULES: tuple[Rule, ...] = (
    Rule(
        "rank_one_conj_mul_transport_ofreal_pow",
        """  exact Complex.conj_mul' _
""",
        """  simpa only [Complex.ofReal_pow] using
    (Complex.conj_mul'
      (inner ℂ (actualInverseEtaTestVector Y) u))
""",
        (Header(55722, 2, "Type mismatch"),),
        "Transport the real norm square through the real-to-complex ring homomorphism.",
        "p15_tail7",
        "inverse_eta_rank_one_use_direct_conj_mul",
        "own_old_equals_consumed_new",
    ),
    Rule(
        "natural_stage_monotone_pin_real_cast",
        """  have hcast := add_le_add_right (Nat.cast_le.mpr hmn) 2
  simpa only [add_comm] using hcast
""",
        """  exact add_le_add_right
    (Nat.cast_le.mpr hmn : (m : ℝ) ≤ (n : ℝ)) 2
""",
        (Header(57211, 2, "Type mismatch: After simplification, term"),),
        "Pin Nat.cast_le to the real cutoff codomain before adding two.",
        "p15_tail7",
        "natural_stage_cast_add_comm_orientation",
        "own_old_equals_consumed_new",
    ),
    Rule(
        "global_projection_add_delay_coe_sum_rewrite",
        """  rw [hsum, hout, Pi.add_apply, hu, hv, huv]
  by_cases hx : x ∈ naturalStageSet n
  · simp only [globalStageProjectionRepresentative, hx,
      Set.indicator_of_mem]
  · simp only [globalStageProjectionRepresentative, hx,
      Set.indicator_of_notMem, add_zero]
""",
        """  rw [hsum, hout, Pi.add_apply, hu, hv]
  by_cases hx : x ∈ naturalStageSet n
  · simp only [globalStageProjectionRepresentative, hx,
      Set.indicator_of_mem, huv]
  · simp only [globalStageProjectionRepresentative, hx,
      Set.indicator_of_notMem, add_zero]
""",
        (Header(57344, 40, "Tactic `rewrite` failed: Did not find an occurrence of the pattern"),),
        "Apply the Lp representative rewrites first and consume huv only after the indicator is exposed.",
        "p15_tail7",
        "global_projection_add_expose_pi_application",
        "own_old_contains_consumed_new",
    ),
    Rule(
        "global_projection_smul_delay_coe_smul_rewrite",
        """  rw [hleft, hright, Pi.smul_apply, hu, hcu]
  by_cases hx : x ∈ naturalStageSet n
  · simp only [globalStageProjectionRepresentative, hx,
      Set.indicator_of_mem]
  · simp only [globalStageProjectionRepresentative, hx,
      Set.indicator_of_notMem, smul_zero]
""",
        """  rw [hleft, hright, Pi.smul_apply, hu]
  by_cases hx : x ∈ naturalStageSet n
  · simp only [globalStageProjectionRepresentative, hx,
      Set.indicator_of_mem, hcu]
  · simp only [globalStageProjectionRepresentative, hx,
      Set.indicator_of_notMem, smul_zero]
""",
        (Header(57363, 40, "Tactic `rewrite` failed: Did not find an occurrence of the pattern"),),
        "Apply the Lp representative rewrites first and consume hcu only after the indicator is exposed.",
        "p15_tail7",
        "global_projection_smul_expose_pi_application",
        "own_old_contains_consumed_new",
    ),
    Rule(
        "projection_error_density_preserve_natural_stage_set",
        """  by_cases hx : x ∈ naturalStageSet n
  · simp [globalStageProjectionErrorDensity,
      globalL2DominatingDensity, naturalStageSet,
      globalStageProjectionRepresentative, hx]
  · simp [globalStageProjectionErrorDensity,
      globalL2DominatingDensity, naturalStageSet,
      globalStageProjectionRepresentative, hx]
""",
        """  by_cases hx : x ∈ naturalStageSet n
  · simp [globalStageProjectionErrorDensity,
      globalL2DominatingDensity,
      globalStageProjectionRepresentative, hx]
  · simp [globalStageProjectionErrorDensity,
      globalL2DominatingDensity,
      globalStageProjectionRepresentative, hx]
""",
        (
            Header(57691, 2, "unsolved goals"),
            Header(57694, 2, "unsolved goals"),
        ),
        "Keep naturalStageSet opaque so the branch hypothesis matches the indicator set before simplification.",
    ),
    Rule(
        "eventually_zero_preserve_natural_stage_set",
        """  simp [globalStageProjectionErrorDensity, naturalStageSet,
    globalStageProjectionRepresentative, hn]
""",
        """  simp [globalStageProjectionErrorDensity,
    globalStageProjectionRepresentative, hn]
""",
        (Header(57716, 66, "unsolved goals"),),
        "Keep naturalStageSet opaque so hn directly reduces the indicator to its value.",
    ),
    Rule(
        "tendsto_pointwise_preserve_natural_stage_set",
        """  simp [globalStageProjectionErrorDensity, naturalStageSet,
    globalStageProjectionRepresentative, hx]
""",
        """  simp [globalStageProjectionErrorDensity,
    globalStageProjectionRepresentative, hx]
""",
        (Header(57725, 21, "unsolved goals"),),
        "Keep naturalStageSet opaque so the monotonicity-produced hx directly reduces the indicator.",
    ),
    Rule(
        "compact_resolvent_pin_inner_product_normed_space",
        """  simpa using
    QYM.RCLikeCoerciveFormFriedrichsExtension.realization_hasCompactResolventAt_negShift
      coordinateHamiltonianForm coordinateFormEmbedding
      coordinateFormEmbedding_injective coordinateFormEmbedding_denseRange
      1 1 coordinateHamiltonianForm_positiveShift
      coordinateFormEmbedding_isCompact
""",
        """  change
    @QYM.UnboundedResolventDataExtension.HasCompactResolventAt
      ℂ CoordinateL2 Complex.instRCLike
      (PiLp.normedAddCommGroup 2 fun _ : Fin 2 => ℂ)
      (PiLp.innerProductSpace fun _ : Fin 2 => ℂ).toNormedSpace
      coordinateFriedrichsHamiltonian (-1)
  simpa only [coordinateFriedrichsHamiltonian] using
    QYM.RCLikeCoerciveFormFriedrichsExtension.realization_hasCompactResolventAt_negShift
      coordinateHamiltonianForm coordinateFormEmbedding
      coordinateFormEmbedding_injective coordinateFormEmbedding_denseRange
      1 1 coordinateHamiltonianForm_positiveShift
      coordinateFormEmbedding_isCompact
""",
        (Header(59213, 2, "Type mismatch: After simplification, term"),),
        "Expose the exact PiLp inner-product-derived NormedSpace carried by the generic Friedrichs theorem.",
    ),
)

FOREIGN_HELPERS: tuple[tuple[str, str, str], ...] = (
    ("p15_frontier", "qym_probe15_frontier_producer_p14.py",
     "65f869c7740b741a2536cc92efb2b27c6cac532013bc028995accfb8165b71fb"),
    ("p15_contdiff", "qym-probe15-contdiff-p14-reanchored/qym_probe15_contdiff_p14_reanchored.py",
     "ebcf53a6049532ca4d970fab504dca977d433642e53ca16c05d1270f9f0c9e03"),
    ("p15_tail7", "qym-probe15-tail7-p14-sequenced/qym_probe15_tail7_p14_sequenced.py",
     "c072aa5bda929b4c28a94cb4072d78dfafd778248ef622db5ba504a9553cedd8"),
    ("p15_cusp", "qym-probe15-cusp-radicand-p14-sequenced/qym_probe15_cusp_radicand_p14_sequenced.py",
     "2d7f38cb13a264206d716ac0b16113f50c749e6db80d4ab904dabf84ea367daa"),
    ("p15_prior6", "qym-probe15-prior671f-refinements-p14-static/qym_probe15_prior671f_refinements_p14_static.py",
     "0804abaa20320f713f922843c758d4e297a6b0722bae6be48216a084e891e7b3"),
)


def sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def git_blob(raw: bytes) -> str:
    return hashlib.sha1(f"blob {len(raw)}\0".encode("ascii") + raw).hexdigest()


def shape(raw: bytes) -> dict[str, object]:
    raw.decode("utf-8", errors="strict")
    return {
        "sha256": sha256(raw),
        "git_blob": git_blob(raw),
        "bytes": len(raw),
        "lf": raw.count(b"\n"),
        "cr": raw.count(b"\r"),
        "nul": raw.count(b"\0"),
        "terminal_lf": raw.endswith(b"\n"),
    }


def expected_shape(output: bool) -> dict[str, object]:
    if output:
        return {
            "sha256": OUTPUT_SHA256, "git_blob": OUTPUT_GIT_BLOB,
            "bytes": OUTPUT_BYTES, "lf": OUTPUT_LF,
            "cr": 0, "nul": 0, "terminal_lf": True,
        }
    return {
        "sha256": INPUT_SHA256, "git_blob": INPUT_GIT_BLOB,
        "bytes": INPUT_BYTES, "lf": INPUT_LF,
        "cr": 0, "nul": 0, "terminal_lf": True,
    }


def trust(text: str) -> dict[str, int]:
    return {
        "sorry": len(re.findall(r"\bsorry\b", text)),
        "admit": len(re.findall(r"\badmit\b", text)),
        "native_decide": len(re.findall(r"\bnative_decide\b", text)),
        "Lean.ofReduceBool": text.count("Lean.ofReduceBool"),
        "axiom": len(re.findall(r"(?m)^\s*axiom\s+", text)),
        "unsafe": len(re.findall(r"(?m)^\s*unsafe\s+", text)),
        "maxHeartbeats_zero": len(re.findall(r"set_option\s+maxHeartbeats\s+0\b", text)),
    }


def spans(text: str, needle: str) -> list[tuple[int, int]]:
    found: list[tuple[int, int]] = []
    start = 0
    while True:
        pos = text.find(needle, start)
        if pos < 0:
            return found
        found.append((pos, pos + len(needle)))
        start = pos + 1


def transform(text: str, inverse: bool = False) -> tuple[str, list[dict[str, object]]]:
    records: list[dict[str, object]] = []
    ordered = tuple(reversed(RULES)) if inverse else RULES
    for rule in ordered:
        old, new = (rule.new, rule.old) if inverse else (rule.old, rule.new)
        count = text.count(old)
        if count != rule.occurrences:
            raise RuntimeError(f"anchor count {rule.label}: {count}")
        text = text.replace(old, new)
        records.append({
            "label": rule.label,
            "direction": "inverse" if inverse else "forward",
            "occurrences": count,
            "headers": [asdict(header) for header in rule.headers],
            "rationale": rule.rationale,
        })
    return text, records


apply_rules = transform


def load_foreign(name: str, relative: str, expected_sha: str) -> ModuleType:
    path = Path(__file__).resolve().parents[1] / relative
    raw = path.read_bytes()
    if sha256(raw) != expected_sha:
        raise RuntimeError(f"foreign helper drift: {name}")
    module_name = "_qym_probe16_tail_" + name
    spec = importlib.util.spec_from_file_location(module_name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot import foreign helper: {name}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[module_name] = module
    spec.loader.exec_module(module)
    return module


def normalize_foreign_rule(
    owner: str, index: int, foreign: object
) -> tuple[str, str, str, int]:
    if isinstance(foreign, dict):
        label = foreign.get("label")
        old = foreign.get("old")
        new = foreign.get("new")
        occurrences = int(foreign.get("occurrences", 1))
    elif all(hasattr(foreign, key) for key in ("label", "old", "new")):
        label = getattr(foreign, "label")
        old = getattr(foreign, "old")
        new = getattr(foreign, "new")
        occurrences = int(getattr(foreign, "occurrences", 1))
    elif isinstance(foreign, (tuple, list)) and len(foreign) >= 3:
        label, old, new = foreign[:3]
        occurrences = 1
    else:
        raise RuntimeError(f"malformed foreign rule: {owner}[{index}]")
    if (
        not isinstance(label, str)
        or not isinstance(old, str)
        or not isinstance(new, str)
        or not label
        or not old
        or not new
        or old == new
        or occurrences != 1
    ):
        raise RuntimeError(f"invalid foreign rule: {owner}[{index}]")
    return label, old, new, occurrences


def collision_audit(authority_text: str) -> dict[str, object]:
    own: list[tuple[int, int, Rule]] = []
    for rule in RULES:
        found = spans(authority_text, rule.old)
        if len(found) != rule.occurrences:
            raise RuntimeError(f"own authority anchor drift: {rule.label}")
        for start, end in found:
            line = authority_text.count("\n", 0, start) + 1
            if not 52_000 <= line <= 59_999:
                raise RuntimeError(f"scope violation {rule.label}: {line}")
            own.append((start, end, rule))
    own_sorted = sorted(own, key=lambda item: item[0])
    if any(left[1] > right[0] for left, right in zip(own_sorted, own_sorted[1:])):
        raise RuntimeError("own source-span collision")

    overlaps: list[dict[str, object]] = []
    identities: dict[str, str] = {}
    for name, relative, expected_sha in FOREIGN_HELPERS:
        module = load_foreign(name, relative, expected_sha)
        identities[name] = expected_sha
        raw_rules = tuple(getattr(module, "RULES", ()))
        if not raw_rules:
            raise RuntimeError(f"foreign helper has no rules: {name}")
        for index, foreign in enumerate(raw_rules):
            foreign_label, _, foreign_new, foreign_occurrences = (
                normalize_foreign_rule(name, index, foreign)
            )
            found = spans(authority_text, foreign_new)
            if len(found) != foreign_occurrences:
                raise RuntimeError(
                    f"foreign applied-anchor drift: {name}:{foreign_label}"
                )
            for fstart, fend in found:
                for ostart, oend, own_rule in own:
                    if max(fstart, ostart) >= min(fend, oend):
                        continue
                    if (
                        own_rule.consumed_owner != name
                        or own_rule.consumed_rule != foreign_label
                        or own_rule.relation is None
                    ):
                        raise RuntimeError(
                            f"undeclared foreign overlap: {own_rule.label} / "
                            f"{name}:{foreign_label}"
                        )
                    if own_rule.relation == "own_old_equals_consumed_new":
                        if own_rule.old != foreign_new:
                            raise RuntimeError(
                                f"declared equality drift: {own_rule.label}"
                            )
                    elif own_rule.relation == "own_old_contains_consumed_new":
                        if foreign_new not in own_rule.old:
                            raise RuntimeError(
                                f"declared containment drift: {own_rule.label}"
                            )
                    else:
                        raise RuntimeError(f"unknown relation: {own_rule.relation}")
                    overlaps.append({
                        "own_rule": own_rule.label,
                        "foreign_owner": name,
                        "foreign_rule": foreign_label,
                        "relation": own_rule.relation,
                    })
    if len(overlaps) != 4:
        raise RuntimeError(f"declared overlap count drift: {overlaps}")
    return {
        "foreign_helper_sha256": identities,
        "own_spans": len(own),
        "own_overlaps": 0,
        "declared_consumed_new_overlaps": overlaps,
        "undeclared_overlaps": 0,
    }


def verify_authority(
    result_raw: bytes,
    log_raw: bytes,
    headers_raw: bytes,
    diagnostics_raw: bytes,
    exit_raw: bytes,
    panic_raw: bytes,
) -> dict[str, object]:
    for label, raw, expected in (
        ("result", result_raw, RESULT_SHA256),
        ("log", log_raw, LOG_SHA256),
        ("headers", headers_raw, HEADERS_SHA256),
        ("diagnostics", diagnostics_raw, DIAGNOSTICS_SHA256),
    ):
        if sha256(raw) != expected:
            raise RuntimeError(f"exact Probe15 {label} sidecar gate failed")
    if exit_raw.strip() != b"1" or panic_raw:
        raise RuntimeError("exact Probe15 exit/panic gate failed")
    result = json.loads(result_raw)
    required = {
        "github_sha": TRIGGER_SHA,
        "candidate_qym_sha256": INPUT_SHA256,
        "candidate_qym_blob": INPUT_GIT_BLOB,
        "log_sha256": LOG_SHA256,
        "exit": 1,
        "error_headers": EXPECTED_ERRORS,
        "warning_headers": EXPECTED_WARNINGS,
        "panic_lines": 0,
        "semantic_pass": False,
    }
    for key, expected in required.items():
        if result.get(key) != expected:
            raise RuntimeError(f"Probe15 result field mismatch: {key}")
    header_lines = headers_raw.decode("utf-8").splitlines()
    diagnostics = [
        json.loads(line)
        for line in diagnostics_raw.decode("utf-8").splitlines()
        if line
    ]
    errors = [row for row in diagnostics if row.get("severity") == "error"]
    warnings = [row for row in diagnostics if row.get("severity") == "warning"]
    if (len(header_lines), len(errors), len(warnings)) != (
        EXPECTED_ERRORS, EXPECTED_ERRORS, EXPECTED_WARNINGS
    ):
        raise RuntimeError("Probe15 diagnostic totals mismatch")

    mapped: list[dict[str, object]] = []
    for rule in RULES:
        for header in rule.headers:
            prefix = (
                f"PrimalitySheafVerification/QYM.lean:{header.line}:{header.column}: error"
                + (f"({header.code})" if header.code else "")
                + f": {header.message}"
            )
            hm = [line for line in header_lines if line.startswith(prefix)]
            dm = [
                row for row in errors
                if row.get("line") == header.line
                and row.get("column") == header.column
                and row.get("code") == header.code
                and str(row.get("message", "")).startswith(header.message)
            ]
            if len(hm) != 1 or len(dm) != 1:
                raise RuntimeError(f"diagnostic mismatch: {rule.label}")
            mapped.append({"rule": rule.label, **asdict(header)})
    return {
        "run_id": RUN_ID,
        "job_id": JOB_ID,
        "artifact_id": ARTIFACT_ID,
        "trigger_sha": TRIGGER_SHA,
        "zip_sha256": ZIP_SHA256,
        "result_sha256": RESULT_SHA256,
        "log_sha256": LOG_SHA256,
        "headers_sha256": HEADERS_SHA256,
        "diagnostics_sha256": DIAGNOSTICS_SHA256,
        "errors": len(errors),
        "warnings": len(warnings),
        "selected_direct_diagnostics": mapped,
        "exit": 1,
        "panic": 0,
    }


def preflight(paths: tuple[Path, ...]) -> None:
    resolved = tuple(path.resolve() for path in paths)
    if len(set(resolved)) != len(resolved):
        raise RuntimeError("output and audit paths must be distinct")
    for path in resolved:
        if path.exists():
            raise RuntimeError(f"refusing overwrite: {path}")
        if not path.parent.is_dir() or path.parent.is_symlink():
            raise RuntimeError(f"destination parent must be an existing real directory: {path}")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--audit", type=Path, required=True)
    parser.add_argument("--inverse", action="store_true")
    parser.add_argument("--probe15-result", type=Path, required=True)
    parser.add_argument("--probe15-log", type=Path, required=True)
    parser.add_argument("--probe15-error-headers", type=Path, required=True)
    parser.add_argument("--probe15-diagnostics", type=Path, required=True)
    parser.add_argument("--probe15-exit", type=Path, required=True)
    parser.add_argument("--probe15-panic-lines", type=Path, required=True)
    args = parser.parse_args()

    preflight((args.output, args.audit))
    authority = verify_authority(
        args.probe15_result.read_bytes(),
        args.probe15_log.read_bytes(),
        args.probe15_error_headers.read_bytes(),
        args.probe15_diagnostics.read_bytes(),
        args.probe15_exit.read_bytes(),
        args.probe15_panic_lines.read_bytes(),
    )
    source_raw = args.input.read_bytes()
    source_shape = shape(source_raw)
    if source_shape != expected_shape(args.inverse):
        raise RuntimeError("exact Probe15 tail input identity mismatch")
    source = source_raw.decode("utf-8", errors="strict")
    authority_text = transform(source, True)[0] if args.inverse else source
    collisions = collision_audit(authority_text)
    before = trust(source)
    if any(before.values()):
        raise RuntimeError(f"source trust0 failure: {before}")
    result, records = transform(source, args.inverse)
    result_raw = result.encode("utf-8")
    if shape(result_raw) != expected_shape(not args.inverse):
        raise RuntimeError("exact Probe15 tail output identity mismatch")
    after = trust(result)
    if before != after or any(after.values()):
        raise RuntimeError(f"trust drift: {before} -> {after}")
    restored, _ = transform(result, not args.inverse)
    if restored.encode("utf-8") != source_raw:
        raise RuntimeError("opposite transform is not byte exact")

    record = {
        "schema": SCHEMA,
        "status": "STATIC_PASS_EXACT_TERMINAL_PROBE15_NOT_LEAN_EXECUTED",
        "activation": ACTIVATION,
        "promotion": False,
        "mode": "inverse" if args.inverse else "forward",
        "authority": authority,
        "source": source_shape,
        "result": shape(result_raw),
        "repair_families": len(RULES),
        "repair_occurrences": sum(rule.occurrences for rule in RULES),
        "direct_diagnostics": sum(len(rule.headers) for rule in RULES),
        "selected_lines": sorted(
            {header.line for rule in RULES for header in rule.headers}
        ),
        "excluded_lines": {
            "structural_bridge": [52191],
            "mathematical_transport": [59088],
            "uncertain_post_simp": [59113],
        },
        "rules": records,
        "collision_audit": collisions,
        "inverse_byte_equal": True,
        "trust": after,
        "execution": {
            "lean": False,
            "lake": False,
            "git": False,
            "network": False,
            "remote": False,
            "canonical_source_mutation": False,
        },
    }
    args.output.write_bytes(result_raw)
    args.audit.write_text(
        json.dumps(record, ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
        newline="\n",
    )
    print(json.dumps({
        "result": record["result"],
        "rules": record["repair_families"],
        "diagnostics": record["direct_diagnostics"],
        "inverse_exact": True,
    }, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
