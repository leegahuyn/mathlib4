#!/usr/bin/env python3
"""Activation-disabled exact-Probe16 tail producer refinements for QYM.

Three reversible rules own the exact direct Probe16 diagnostics at lines 57220,
59098, and 59123. The Hamiltonian rule first exposes coerced continuous-linear
map applications and then preserves both existing idempotence rewrites. Broad
structural, density, projection, and line-59229 repairs are excluded.
"""

from __future__ import annotations

import hashlib
import importlib.util
import json
import re
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from types import ModuleType
from typing import Iterable

sys.dont_write_bytecode = True

SCHEMA = "qym-probe17-tail-refinements-exact-p16-v1"
ACTIVATION = False
PROMOTION = False
INSTALL_TARGET = (
    "scripts/qym-probe17-tail-refinements-p16-static/"
    "qym_probe17_tail_refinements_p16_static.py"
)

RUN_ID = 31996603368
JOB_ID = 95289278009
ARTIFACT_ID = 9277193984
TRIGGER_SHA = "51ff9610af6858e740d18af171e72ffb2b858012"
ZIP_SHA256 = "d8745c0ae8cf0ed77f3a62ab2b5d9e46b2f7f4cccc66d92fab09d989dcdee07e"
RESULT_SHA256 = "d1e5f9ce3f015efb897f833fc8fd2be542b3644a1b3cddcdfdd5941dc818ad28"
LOG_SHA256 = "e431025fc146210a46b57a7110628669ddeeba44851bd08554434349ede8ed7d"
HEADERS_SHA256 = "599242fc95fa6881c49f1ac896713aebb2a02f9a5ba702953b69805c22158e65"
DIAGNOSTICS_SHA256 = "8e8acac443ac100091b8a59fbc608bcc2155f0036d7f70563eab2542f6e02a4c"
EXPECTED_ERRORS = 98
EXPECTED_WARNINGS = 357
EXPECTED_EXIT = 1
EXPECTED_PANIC = 0

INPUT_SHA256 = "19e68721a055a4131d7873fe37ee02509565bb4e0f202c74b646cba2275aba74"
INPUT_GIT_BLOB = "5d8def67719cdb3a7471c33aa320fafbf44ff186"
INPUT_BYTES = 2_942_215
INPUT_LF = 62_206
OUTPUT_SHA256 = "58700503b546b63857ca76da7330274ce0b0fe33d3d288a6ed92c37085262b1f"
OUTPUT_GIT_BLOB = "14c6ba8a1b2bcbaa7dba35e367e6ddd494863f23"
OUTPUT_BYTES = 2_942_507
OUTPUT_LF = 62_210


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
        "natural_stage_monotone_restore_add_comm_orientation",
        """  exact add_le_add_right
    (Nat.cast_le.mpr hmn : (m : ℝ) ≤ (n : ℝ)) 2
""",
        """  have hcast := add_le_add_right
    (Nat.cast_le.mpr hmn : (m : ℝ) ≤ (n : ℝ)) 2
  simpa only [add_comm] using hcast
""",
        (Header(57220, 2, "Type mismatch"),),
        "Name the real-cast inequality and normalize only the commuted addition orientation.",
        "p16_tail",
        "natural_stage_monotone_pin_real_cast",
        "own_old_equals_consumed_new",
    ),
    Rule(
        "coordinate_hamiltonian_expose_clm_apply_before_idempotence",
        """  have hDerivative :=
    (covariantDerivative_isSymmetric (covariantDerivative u) v).symm
  rw [covariantDerivative_apply_apply] at hDerivative
  have hProjection :=
    (groundProjection_isSymmetric (groundProjection u) v).symm
  rw [groundProjection_apply_apply] at hProjection
""",
        """  have hDerivative :=
    (covariantDerivative_isSymmetric (covariantDerivative u) v).symm
  change inner ℂ (covariantDerivative u) (covariantDerivative v) =
    inner ℂ (covariantDerivative (covariantDerivative u)) v at hDerivative
  rw [covariantDerivative_apply_apply] at hDerivative
  have hProjection :=
    (groundProjection_isSymmetric (groundProjection u) v).symm
  change inner ℂ (groundProjection u) (groundProjection v) =
    inner ℂ (groundProjection (groundProjection u)) v at hProjection
  rw [groundProjection_apply_apply] at hProjection
""",
        (
            Header(
                59098,
                6,
                "Tactic `rewrite` failed: Did not find an occurrence of the pattern",
            ),
        ),
        "Expose both coerced operator applications before reusing the certified idempotence rewrites.",
    ),
    Rule(
        "coordinate_hamiltonian_re_drop_redundant_post_simp",
        """  rw [coordinateHamiltonianForm_apply,
    inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
  simp
  simp only [Complex.ofReal_re]
""",
        """  rw [coordinateHamiltonianForm_apply,
    inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
  simp
""",
        (Header(59123, 2, "`simp` made no progress"),),
        "Delete the redundant simp after the preceding simp has already closed the real-part goal.",
    ),
)

FOREIGN_HELPERS: tuple[tuple[str, str, str], ...] = (
    (
        "p16_mid",
        "qym-probe16-mid37k49k-p15-static/qym_probe16_mid37k49k_p15_static.py",
        "5723983fb113915956363e8189299b51368e6ab5b3b2e7cc046de12668110473",
    ),
    (
        "p16_ambient",
        "qym-probe16-ambient-zero-extension-p15-static/qym_probe16_ambient_zero_extension_p15_static.py",
        "8594fdd90e811b7e04fad3a17d67b034e26a7b69b76672c78e2a278bd114e1e4",
    ),
    (
        "p16_tail",
        "qym-probe16-tail-p15-sequenced/qym_probe16_tail_p15_sequenced.py",
        "1fa1af220902c3c54bbb504987c9fb8cf82b0a92db4fc4f8dc5286afbaa8772e",
    ),
)


def sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def git_blob(raw: bytes) -> str:
    return hashlib.sha1(
        b"blob " + str(len(raw)).encode("ascii") + bytes((0,)) + raw
    ).hexdigest()


def shape(raw: bytes) -> dict[str, object]:
    raw.decode("utf-8", errors="strict")
    return {
        "sha256": sha256(raw),
        "git_blob": git_blob(raw),
        "bytes": len(raw),
        "lf": raw.count(b"\n"),
        "cr": raw.count(b"\r"),
        "nul": raw.count(bytes((0,))),
        "bom": raw.startswith(bytes((0xEF, 0xBB, 0xBF))),
        "terminal_lf": raw.endswith(b"\n"),
    }


def expected_shape(output: bool) -> dict[str, object]:
    if output:
        return {
            "sha256": OUTPUT_SHA256,
            "git_blob": OUTPUT_GIT_BLOB,
            "bytes": OUTPUT_BYTES,
            "lf": OUTPUT_LF,
            "cr": 0,
            "nul": 0,
            "bom": False,
            "terminal_lf": True,
        }
    return {
        "sha256": INPUT_SHA256,
        "git_blob": INPUT_GIT_BLOB,
        "bytes": INPUT_BYTES,
        "lf": INPUT_LF,
        "cr": 0,
        "nul": 0,
        "bom": False,
        "terminal_lf": True,
    }


def trust(text: str) -> dict[str, int]:
    return {
        "sorry": len(re.findall(r"\bsorry\b", text)),
        "admit": len(re.findall(r"\badmit\b", text)),
        "native_decide": len(re.findall(r"\bnative_decide\b", text)),
        "Lean.ofReduceBool": text.count("Lean.ofReduceBool"),
        "axiom": len(re.findall(r"(?m)^\s*axiom\s+", text)),
        "unsafe": len(re.findall(r"(?m)^\s*unsafe\s+", text)),
        "maxHeartbeats_zero": len(
            re.findall(r"set_option\s+maxHeartbeats\s+0\b", text)
        ),
    }


def _ordered_rules(order: Iterable[int] | None) -> tuple[Rule, ...]:
    if order is None:
        return RULES
    indices = tuple(order)
    if sorted(indices) != list(range(len(RULES))):
        raise RuntimeError(f"invalid rule order: {indices}")
    return tuple(RULES[index] for index in indices)


def transform(
    text: str,
    inverse: bool = False,
    order: Iterable[int] | None = None,
) -> tuple[str, list[dict[str, object]]]:
    selected = _ordered_rules(order)
    ordered = tuple(reversed(selected)) if inverse else selected
    records: list[dict[str, object]] = []
    for rule in ordered:
        old, new = (rule.new, rule.old) if inverse else (rule.old, rule.new)
        count = text.count(old)
        if count != rule.occurrences:
            raise RuntimeError(f"anchor count {rule.label}: {count}")
        text = text.replace(old, new, rule.occurrences)
        records.append(
            {
                "label": rule.label,
                "direction": "inverse" if inverse else "forward",
                "occurrences": count,
                "headers": [asdict(header) for header in rule.headers],
                "rationale": rule.rationale,
            }
        )
    return text, records


def apply_rules(
    raw: bytes,
    order: Iterable[int] | None = None,
) -> bytes:
    if shape(raw) != expected_shape(False):
        raise RuntimeError("exact Probe16 input identity mismatch")
    result, _ = transform(raw.decode("utf-8", errors="strict"), False, order)
    result_raw = result.encode("utf-8")
    if shape(result_raw) != expected_shape(True):
        raise RuntimeError("exact Probe17 output identity mismatch")
    return result_raw


def inverse_rules(
    raw: bytes,
    order: Iterable[int] | None = None,
) -> bytes:
    if shape(raw) != expected_shape(True):
        raise RuntimeError("exact Probe17 input identity mismatch")
    result, _ = transform(raw.decode("utf-8", errors="strict"), True, order)
    result_raw = result.encode("utf-8")
    if shape(result_raw) != expected_shape(False):
        raise RuntimeError("exact Probe16 inverse identity mismatch")
    return result_raw


def spans(text: str, needle: str) -> list[tuple[int, int]]:
    found: list[tuple[int, int]] = []
    start = 0
    while True:
        pos = text.find(needle, start)
        if pos < 0:
            return found
        found.append((pos, pos + len(needle)))
        start = pos + 1


def load_foreign(name: str, relative: str, expected_sha: str) -> ModuleType:
    path = Path(__file__).resolve().parents[1] / relative
    raw = path.read_bytes()
    if sha256(raw) != expected_sha:
        raise RuntimeError(f"foreign helper drift: {name}")
    module_name = "_qym_probe17_tail_" + name
    spec = importlib.util.spec_from_file_location(module_name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot import foreign helper: {name}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[module_name] = module
    spec.loader.exec_module(module)
    return module


def normalize_foreign_rule(
    owner: str,
    index: int,
    foreign: object,
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
                    if (
                        own_rule.relation == "own_old_equals_consumed_new"
                        and own_rule.old != foreign_new
                    ):
                        raise RuntimeError(
                            f"declared equality drift: {own_rule.label}"
                        )
                    if own_rule.relation != "own_old_equals_consumed_new":
                        raise RuntimeError(f"unknown relation: {own_rule.relation}")
                    overlaps.append(
                        {
                            "own_rule": own_rule.label,
                            "foreign_owner": name,
                            "foreign_rule": foreign_label,
                            "relation": own_rule.relation,
                        }
                    )
    if len(overlaps) != 1:
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
            raise RuntimeError(f"exact Probe16 {label} sidecar gate failed")
    if exit_raw.strip() != b"1" or panic_raw:
        raise RuntimeError("exact Probe16 exit/panic gate failed")
    result = json.loads(result_raw)
    required = {
        "github_sha": TRIGGER_SHA,
        "candidate_qym_sha256": INPUT_SHA256,
        "candidate_qym_blob": INPUT_GIT_BLOB,
        "log_sha256": LOG_SHA256,
        "exit": EXPECTED_EXIT,
        "error_headers": EXPECTED_ERRORS,
        "warning_headers": EXPECTED_WARNINGS,
        "panic_lines": EXPECTED_PANIC,
        "semantic_pass": False,
    }
    for key, expected in required.items():
        if result.get(key) != expected:
            raise RuntimeError(f"Probe16 result field mismatch: {key}")
    header_lines = headers_raw.decode("utf-8", errors="strict").splitlines()
    diagnostics = [
        json.loads(line)
        for line in diagnostics_raw.decode("utf-8", errors="strict").splitlines()
        if line
    ]
    errors = [row for row in diagnostics if row.get("severity") == "error"]
    warnings = [row for row in diagnostics if row.get("severity") == "warning"]
    if (len(header_lines), len(errors), len(warnings)) != (
        EXPECTED_ERRORS,
        EXPECTED_ERRORS,
        EXPECTED_WARNINGS,
    ):
        raise RuntimeError("Probe16 diagnostic totals mismatch")
    selected: list[dict[str, object]] = []
    for rule in RULES:
        for header in rule.headers:
            hm = [
                line
                for line in header_lines
                if line.startswith(
                    "PrimalitySheafVerification/QYM.lean:"
                    f"{header.line}:{header.column}: error"
                )
                and header.message in line
            ]
            dm = [
                row
                for row in errors
                if row.get("line") == header.line
                and row.get("column") == header.column
                and row.get("code") == header.code
                and str(row.get("message", "")).startswith(header.message)
            ]
            if len(hm) != 1 or len(dm) != 1:
                raise RuntimeError(f"diagnostic mismatch: {rule.label}")
            selected.append({"rule": rule.label, **asdict(header)})
    return {
        "run_id": RUN_ID,
        "job_id": JOB_ID,
        "artifact_id": ARTIFACT_ID,
        "zip_sha256": ZIP_SHA256,
        "errors": len(errors),
        "warnings": len(warnings),
        "exit": EXPECTED_EXIT,
        "panic": EXPECTED_PANIC,
        "selected_direct_diagnostics": selected,
    }


def static_audit() -> dict[str, object]:
    if ACTIVATION or PROMOTION:
        raise RuntimeError("helper must remain activation-disabled")
    if len(RULES) != 3 or sum(rule.occurrences for rule in RULES) != 3:
        raise RuntimeError("rule count drift")
    headers = tuple(header for rule in RULES for header in rule.headers)
    if len(headers) != 3:
        raise RuntimeError("header count drift")
    labels = [rule.label for rule in RULES]
    if len(labels) != len(set(labels)):
        raise RuntimeError("duplicate labels")
    if any(rule.old == rule.new for rule in RULES):
        raise RuntimeError("no-op rule")
    trust_tokens = ("sorry", "admit", "axiom", "unsafe")
    hits = [
        (rule.label, token)
        for rule in RULES
        for token in trust_tokens
        if token in rule.new.lower()
    ]
    if hits:
        raise RuntimeError(f"rule trust-token hits: {hits}")
    return {
        "schema": SCHEMA,
        "activation": ACTIVATION,
        "promotion": PROMOTION,
        "rules": 3,
        "occurrences": 3,
        "direct_diagnostics": 3,
        "declared_overlaps": 1,
        "undeclared_overlaps": 0,
        "trust_hits": 0,
    }


def manifest() -> dict[str, object]:
    return {
        **static_audit(),
        "install_target": INSTALL_TARGET,
        "authority": {
            "run_id": RUN_ID,
            "job_id": JOB_ID,
            "artifact_id": ARTIFACT_ID,
            "trigger_sha": TRIGGER_SHA,
            "zip_sha256": ZIP_SHA256,
            "result_sha256": RESULT_SHA256,
            "log_sha256": LOG_SHA256,
            "headers_sha256": HEADERS_SHA256,
            "diagnostics_sha256": DIAGNOSTICS_SHA256,
            "errors": EXPECTED_ERRORS,
            "warnings": EXPECTED_WARNINGS,
            "exit": EXPECTED_EXIT,
            "panic": EXPECTED_PANIC,
        },
        "input": expected_shape(False),
        "output": expected_shape(True),
        "dependencies": [
            {"owner": name, "path": path, "sha256": digest}
            for name, path, digest in FOREIGN_HELPERS
        ],
        "rule_labels": [rule.label for rule in RULES],
        "headers": [asdict(header) for rule in RULES for header in rule.headers],
        "excluded": {
            "structural_bridge": [52191],
            "density_projection_clusters": [57691, 57694, 57716, 57725],
            "mathematical_or_instance_uncertain": [59229],
        },
    }


if __name__ == "__main__":
    print(json.dumps(manifest(), ensure_ascii=False, sort_keys=True, indent=2))
