#!/usr/bin/env python3
"""Conditional, reversible Probe-5 repairs for the QYM 40000+ frontier.

This transformer is intentionally static.  It accepts only the exact sealed
Probe-4 projection, performs exact occurrence-counted replacements, and never
invokes Lean, Lake, Git, or the network.  Promotion remains false until the
Probe-4 authority artifact proves that this projection was the executed input.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from dataclasses import dataclass
from pathlib import Path


SCHEMA = "qym-probe5-late-conditional-transform-v1"
EXPECTED_INPUT_SHA256 = "fb9d451c88d55e71398f3e3a4b38b3cc9ff5e0a37273115579fc2351d1fdad9c"
EXPECTED_INPUT_GIT_BLOB = "b08d7bb621d8acc8338f3afa3f12ac2ff2c7e6d1"
EXPECTED_INPUT_BYTES = 2_910_229
EXPECTED_INPUT_LF = 61_523
AUTHORITY_PROBE3_LOG_SHA256 = "501029e514ba6bc875527e1bc96fb9f571afda222e53e633078736dccaa71f56"
PROBE4_LATE_ANALYSIS_SHA256 = "5a05d06679a8e672df7fae04bffd785acd5ac0c170be84a6412ea3bddf149a96"

# Sealed after an independent first materialization, then enforced strictly.
EXPECTED_OUTPUT_SHA256 = "c01a80c2e3b49a19ecc8fcba6aa78b5154072e0fc667cacfa01679c2f0ce86ea"
EXPECTED_OUTPUT_GIT_BLOB = "b7aecdc408c685aa0f195e482b58d8b0e2749bea"
EXPECTED_OUTPUT_BYTES = 2_911_120
EXPECTED_OUTPUT_LF = 61_543


@dataclass(frozen=True)
class Repair:
    label: str
    probe3_error_lines: tuple[int, ...]
    old: str
    new: str
    occurrences: int = 1
    kind: str = "direct"


REPAIRS = (
    Repair(
        "nnreal_parser_reanchor",
        (40520, 40579, 40601),
        "    (tau : ℝ → ℂ) (f : ℝ → ℂ) (K : ℝ≥0)\n",
        "    (tau : ℝ → ℂ) (f : ℝ → ℂ) (K : NNReal)\n",
        occurrences=3,
    ),
    Repair(
        "lp_add_coercion_is_bundled_before_function_coercion",
        (40669, 40722, 40771),
        "    widthTwoTwistedDifferenceQuotient tau (f + g) =ᵐ[\n",
        "    widthTwoTwistedDifferenceQuotient tau ((↑(f + g) : ℝ → ℂ)) =ᵐ[\n",
    ),
    Repair(
        "lp_smul_coercion_is_bundled_before_function_coercion",
        (40681, 40727, 40786),
        "    widthTwoTwistedDifferenceQuotient tau (c • f) =ᵐ[\n",
        "    widthTwoTwistedDifferenceQuotient tau ((↑(c • f) : ℝ → ℂ)) =ᵐ[\n",
    ),
    Repair(
        "horocycle_add_two_close_commutative_residue",
        (41018,),
        "  simp [actualFixedPhaseHorizontalHorocyclePoint,\n    UpperHalfPlane.coe_vadd]\n",
        "  simp [actualFixedPhaseHorizontalHorocyclePoint,\n    UpperHalfPlane.coe_vadd]\n  ring\n",
    ),
    Repair(
        "reexpose_existing_line_quotient_topology_and_measurability",
        (47520, 47675, 47689, 47702, 47717, 47759, 47764, 47765, 47776, 49821),
        "noncomputable abbrev InverseEtaTotal := QYM.FullCertification.Mock2EtaPeterssonCarrierExtension.EtaAutomorphicLineBundle.Total\n",
        """noncomputable abbrev InverseEtaTotal := QYM.FullCertification.Mock2EtaPeterssonCarrierExtension.EtaAutomorphicLineBundle.Total

/-- Re-expose the topology already carried by the concrete orbit quotient.
This does not choose a new topology: it unfolds the stored bundle carrier to
the exact `Quotient (lineOrbitRel inverseEtaMultiplier)` representation and
uses Mathlib's existing quotient instance. -/
noncomputable instance inverseEtaTotalTopologicalSpace :
    TopologicalSpace InverseEtaTotal := by
  change TopologicalSpace
    (Quotient (Mock2.Definition15Geometry.lineOrbitRel inverseEtaMultiplier))
  infer_instance

/-- The same exact re-exposure for the quotient measurable structure. -/
noncomputable instance inverseEtaTotalMeasurableSpace :
    MeasurableSpace InverseEtaTotal := by
  change MeasurableSpace
    (Quotient (Mock2.Definition15Geometry.lineOrbitRel inverseEtaMultiplier))
  infer_instance
""",
        kind="foundation",
    ),
    Repair(
        "explicit_raw_base_orbit_setoid",
        (47658,),
        "    (Quotient.mk' : H -> Quotient (MulAction.orbitRel Gamma2 H))\n",
        "    (@Quotient.mk' H (MulAction.orbitRel Gamma2 H))\n",
        kind="foundation",
    ),
    Repair(
        "inverse_eta_fibre_self_inner_explicit_scalar",
        (47903,),
        "  exact inner_self_eq_norm_sq _\n",
        "  unfold inverseEtaFibreHermitian\n  exact inner_self_eq_norm_sq (𝕜 := ℂ) _\n",
    ),
    Repair(
        "inverse_eta_fibre_positive_inner_unfold",
        (47909,),
        "  rw [inverseEtaFibreHermitian, re_inner_self_pos]\n",
        "  unfold inverseEtaFibreHermitian\n  rw [re_inner_self_pos (𝕜 := ℂ)]\n",
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
    prefix = f"blob {len(raw)}\0".encode("ascii")
    return hashlib.sha1(prefix + raw).hexdigest()


def hygiene(raw: bytes, label: str) -> dict[str, object]:
    if raw.startswith(b"\xef\xbb\xbf"):
        raise AssertionError(f"{label}: BOM forbidden")
    if b"\r" in raw:
        raise AssertionError(f"{label}: CR forbidden")
    if b"\x00" in raw:
        raise AssertionError(f"{label}: NUL forbidden")
    if not raw.endswith(b"\n"):
        raise AssertionError(f"{label}: terminal LF required")
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


def trust_counts(text: str) -> dict[str, int]:
    return {name: len(pattern.findall(text)) for name, pattern in TRUST_PATTERNS.items()}


def assert_identity(
    identity: dict[str, object], *, expected_sha: str, expected_blob: str,
    expected_bytes: int, expected_lf: int, label: str, allow_unsealed: bool
) -> None:
    if allow_unsealed and expected_sha == "TO_BE_SEALED":
        return
    expected = {
        "sha256": expected_sha,
        "git_blob": expected_blob,
        "bytes": expected_bytes,
        "lf": expected_lf,
    }
    actual = {key: identity[key] for key in expected}
    if actual != expected:
        raise AssertionError(f"{label}: identity mismatch: {actual} != {expected}")


def transform(text: str, *, inverse: bool) -> tuple[str, list[dict[str, object]]]:
    ordered = tuple(reversed(REPAIRS)) if inverse else REPAIRS
    audit: list[dict[str, object]] = []
    for repair in ordered:
        source = repair.new if inverse else repair.old
        target = repair.old if inverse else repair.new
        found = text.count(source)
        if found != repair.occurrences:
            raise AssertionError(
                f"{repair.label}: expected {repair.occurrences} source occurrences, found {found}"
            )
        text = text.replace(source, target)
        audit.append({
            "label": repair.label,
            "kind": repair.kind,
            "probe3_error_lines": list(repair.probe3_error_lines),
            "occurrences": repair.occurrences,
            "inverse": inverse,
        })
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
    before = hygiene(raw, "input")
    if args.inverse:
        assert_identity(
            before,
            expected_sha=EXPECTED_OUTPUT_SHA256,
            expected_blob=EXPECTED_OUTPUT_GIT_BLOB,
            expected_bytes=EXPECTED_OUTPUT_BYTES,
            expected_lf=EXPECTED_OUTPUT_LF,
            label="inverse input",
            allow_unsealed=args.allow_unsealed,
        )
    else:
        assert_identity(
            before,
            expected_sha=EXPECTED_INPUT_SHA256,
            expected_blob=EXPECTED_INPUT_GIT_BLOB,
            expected_bytes=EXPECTED_INPUT_BYTES,
            expected_lf=EXPECTED_INPUT_LF,
            label="forward input",
            allow_unsealed=False,
        )

    text = raw.decode("utf-8")
    before_trust = trust_counts(text)
    transformed, repairs = transform(text, inverse=args.inverse)
    after_trust = trust_counts(transformed)
    if before_trust != after_trust:
        raise AssertionError(f"trust counts changed: {before_trust} -> {after_trust}")
    out_raw = transformed.encode("utf-8")
    after = hygiene(out_raw, "output")
    if args.inverse:
        assert_identity(
            after,
            expected_sha=EXPECTED_INPUT_SHA256,
            expected_blob=EXPECTED_INPUT_GIT_BLOB,
            expected_bytes=EXPECTED_INPUT_BYTES,
            expected_lf=EXPECTED_INPUT_LF,
            label="inverse output",
            allow_unsealed=False,
        )
    else:
        assert_identity(
            after,
            expected_sha=EXPECTED_OUTPUT_SHA256,
            expected_blob=EXPECTED_OUTPUT_GIT_BLOB,
            expected_bytes=EXPECTED_OUTPUT_BYTES,
            expected_lf=EXPECTED_OUTPUT_LF,
            label="forward output",
            allow_unsealed=args.allow_unsealed,
        )

    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.audit.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_bytes(out_raw)
    payload = {
        "schema": SCHEMA,
        "direction": "inverse" if args.inverse else "forward",
        "conditional": True,
        "promotion": False,
        "promotion_gate": "Probe4 authority artifact must match exact candidate SHA and identify remaining diagnostics",
        "authority_probe3_log_sha256": AUTHORITY_PROBE3_LOG_SHA256,
        "probe4_late_analysis_sha256": PROBE4_LATE_ANALYSIS_SHA256,
        "input": before,
        "output": after,
        "repairs": repairs,
        "trust_before": before_trust,
        "trust_after": after_trust,
        "trust_delta": {key: after_trust[key] - before_trust[key] for key in before_trust},
        "execution": {"lean": False, "lake": False, "remote": False, "source_mutation": False},
    }
    args.audit.write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8", newline="\n"
    )
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
