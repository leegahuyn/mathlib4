#!/usr/bin/env python3
"""Fail-closed exact-Probe16 integrator for two frozen Probe17 components.

The edge-derivative and tail-refinement helpers are pinned by SHA-256, standard
Git blob, bytes, and LF count before import. The three active Probe16 helpers
are separately pinned to validate four declared consumed-NEW overlaps against
the exact Probe16 candidate. Both component orders and matching inverses are
replayed. This program never invokes Lean, Lake, Git, or any network service.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import itertools
import json
import re
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from types import ModuleType

sys.dont_write_bytecode = True

SCHEMA = "qym-probe17-integrated-exact-terminal-p16-v1"
ACTIVATION = False
PROMOTION = False
PACKAGE_DIR = Path(__file__).resolve().parent

INPUT_SHA256 = "19e68721a055a4131d7873fe37ee02509565bb4e0f202c74b646cba2275aba74"
INPUT_GIT_BLOB = "5d8def67719cdb3a7471c33aa320fafbf44ff186"
INPUT_BYTES = 2_942_215
INPUT_LF = 62_206
OUTPUT_SHA256 = "971d9fd6c1cba701f6404b6303668b61d3de9f4b5d71281ab7b88f1530009bf7"
OUTPUT_GIT_BLOB = "061345d55ea0ce66c01911454df3c6f2c509fa91"
OUTPUT_BYTES = 2_943_828
OUTPUT_LF = 62_238

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


@dataclass(frozen=True)
class Component:
    label: str
    relative_path: str
    helper_sha256: str
    helper_git_blob: str
    helper_bytes: int
    helper_lf: int
    expected_rules: int
    expected_occurrences: int
    expected_owned_diagnostics: int
    expected_direct_diagnostics: int
    standalone_sha256: str
    standalone_git_blob: str
    standalone_bytes: int
    standalone_lf: int


COMPONENTS: tuple[Component, ...] = (
    Component(
        "edge_derivatives",
        "qym-probe17-edge-derivatives-p16-static/"
        "qym_probe17_edge_derivatives_p16_static.py",
        "428f1e9d63734e51b5c9b14794c2886d4ce636bc12a6c7a5d121106011999ebd",
        "1fa4f34ce4f7c7b16581fc1fb0a2bd509ba9f219",
        19_374,
        508,
        7,
        7,
        7,
        7,
        "9ae9dcf39c7e50f4d87d007f652a962e04e7ea0782e0564be345e72babed7e91",
        "48d2307329ea1ff03e7ff80f532775652d49b99f",
        2_943_536,
        62_234,
    ),
    Component(
        "tail_refinements",
        "qym-probe17-tail-refinements-p16-static/"
        "qym_probe17_tail_refinements_p16_static.py",
        "6f01a3308a166d83edf57fd1d7620565627b9622014ce464a1001f088001fbc3",
        "b7d8464ab37940b06e818da855f44834bbae884b",
        20_073,
        567,
        3,
        3,
        3,
        3,
        "58700503b546b63857ca76da7330274ce0b0fe33d3d288a6ed92c37085262b1f",
        "14c6ba8a1b2bcbaa7dba35e367e6ddd494863f23",
        2_942_507,
        62_210,
    ),
)


@dataclass(frozen=True)
class Baseline:
    owner: str
    relative_path: str
    helper_sha256: str
    helper_git_blob: str
    helper_bytes: int
    helper_lf: int


BASELINE_HELPERS: tuple[Baseline, ...] = (
    Baseline(
        "probe16_mid37k49k",
        "qym-probe16-mid37k49k-p15-static/"
        "qym_probe16_mid37k49k_p15_static.py",
        "5723983fb113915956363e8189299b51368e6ab5b3b2e7cc046de12668110473",
        "c130e0d8b76330c441b13ee737587aec177c3c24",
        16_562,
        426,
    ),
    Baseline(
        "p16_ambient",
        "qym-probe16-ambient-zero-extension-p15-static/"
        "qym_probe16_ambient_zero_extension_p15_static.py",
        "8594fdd90e811b7e04fad3a17d67b034e26a7b69b76672c78e2a278bd114e1e4",
        "798bdfa6446bb21435c9540718cad5b89412eeaa",
        15_691,
        455,
    ),
    Baseline(
        "p16_tail",
        "qym-probe16-tail-p15-sequenced/"
        "qym_probe16_tail_p15_sequenced.py",
        "1fa1af220902c3c54bbb504987c9fb8cf82b0a92db4fc4f8dc5286afbaa8772e",
        "e401024361837a62c8a8575a8d4d0cc86d053eb8",
        24_175,
        619,
    ),
)

EXPECTED_RULES = 10
EXPECTED_OCCURRENCES = 10
EXPECTED_OWNED_DIAGNOSTICS = 10
EXPECTED_DIRECT_DIAGNOSTICS = 10
EXPECTED_DECLARED_HISTORICAL_OVERLAPS = 4


@dataclass(frozen=True)
class RuleView:
    label: str
    old: str
    new: str
    occurrences: int
    source: object


@dataclass(frozen=True)
class Loaded:
    component: Component
    path: Path
    module: ModuleType
    rules: tuple[RuleView, ...]


@dataclass(frozen=True)
class LoadedBaseline:
    baseline: Baseline
    path: Path
    module: ModuleType
    rules: tuple[RuleView, ...]


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
        "lf": raw.count(bytes((10,))),
        "cr": raw.count(bytes((13,))),
        "nul": raw.count(bytes((0,))),
        "bom": raw.startswith(bytes((0xEF, 0xBB, 0xBF))),
        "terminal_lf": raw.endswith(bytes((10,))),
    }


def exact_shape(
    digest: str,
    blob: str,
    byte_count: int,
    lf_count: int,
) -> dict[str, object]:
    return {
        "sha256": digest,
        "git_blob": blob,
        "bytes": byte_count,
        "lf": lf_count,
        "cr": 0,
        "nul": 0,
        "bom": False,
        "terminal_lf": True,
    }


def expected_shape(inverse: bool) -> dict[str, object]:
    if inverse:
        return exact_shape(
            OUTPUT_SHA256,
            OUTPUT_GIT_BLOB,
            OUTPUT_BYTES,
            OUTPUT_LF,
        )
    return exact_shape(
        INPUT_SHA256,
        INPUT_GIT_BLOB,
        INPUT_BYTES,
        INPUT_LF,
    )


def helper_shape(component: Component) -> dict[str, object]:
    return exact_shape(
        component.helper_sha256,
        component.helper_git_blob,
        component.helper_bytes,
        component.helper_lf,
    )


def standalone_shape(component: Component) -> dict[str, object]:
    return exact_shape(
        component.standalone_sha256,
        component.standalone_git_blob,
        component.standalone_bytes,
        component.standalone_lf,
    )


def baseline_shape(baseline: Baseline) -> dict[str, object]:
    return exact_shape(
        baseline.helper_sha256,
        baseline.helper_git_blob,
        baseline.helper_bytes,
        baseline.helper_lf,
    )


def trust(text: str) -> dict[str, int]:
    patterns = {
        "sorry": r"\bsorry\b",
        "admit": r"\badmit\b",
        "native_decide": r"\bnative_decide\b",
        "Lean.ofReduceBool": r"\bLean\.ofReduceBool\b",
        "axiom": r"(?m)^\s*axiom\s+",
        "unsafe": r"(?m)^\s*unsafe\s+(?:def|theorem|opaque|abbrev|instance)\s+",
        "maxHeartbeats_zero": r"set_option\s+maxHeartbeats\s+0\b",
    }
    return {
        name: len(re.findall(pattern, text))
        for name, pattern in patterns.items()
    }


def path_candidates(relative: str) -> tuple[Path, ...]:
    rel = Path(relative)
    candidates = (
        PACKAGE_DIR / rel,
        PACKAGE_DIR.parent / rel,
        PACKAGE_DIR.parent / "scripts" / rel,
    )
    unique: list[Path] = []
    for candidate in candidates:
        resolved = candidate.resolve()
        if resolved not in unique:
            unique.append(resolved)
    return tuple(unique)


def resolve_exact(relative: str, expected: dict[str, object], label: str) -> Path:
    observed: dict[str, object] = {}
    matches: list[Path] = []
    for path in path_candidates(relative):
        if not path.is_file():
            continue
        actual = shape(path.read_bytes())
        observed[str(path)] = actual
        if actual == expected:
            matches.append(path)
    if len(matches) != 1:
        raise RuntimeError(f"{label}: exact path resolution failed: {observed}")
    return matches[0]


def import_exact(
    name: str,
    path: Path,
    expected: dict[str, object],
) -> ModuleType:
    before = path.read_bytes()
    if shape(before) != expected:
        raise RuntimeError(f"{name}: helper changed before import")
    module_name = "_qym_probe17_integrated_" + name
    spec = importlib.util.spec_from_file_location(module_name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"{name}: import spec unavailable")
    module = importlib.util.module_from_spec(spec)
    sys.modules[module_name] = module
    spec.loader.exec_module(module)
    if shape(path.read_bytes()) != expected:
        raise RuntimeError(f"{name}: helper changed during import")
    if getattr(module, "ACTIVATION", False) is not False:
        raise RuntimeError(f"{name}: activation must be false")
    return module


def normalize_rule(owner: str, index: int, rule: object) -> RuleView:
    if isinstance(rule, dict):
        label = rule.get("label")
        old = rule.get("old")
        new = rule.get("new")
        occurrences = int(rule.get("occurrences", 1))
    elif all(hasattr(rule, key) for key in ("label", "old", "new")):
        label = getattr(rule, "label")
        old = getattr(rule, "old")
        new = getattr(rule, "new")
        occurrences = int(getattr(rule, "occurrences", 1))
    elif isinstance(rule, (tuple, list)) and len(rule) >= 3:
        label, old, new = rule[:3]
        occurrences = 1
    else:
        raise RuntimeError(f"{owner}: malformed rule {index}")
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
        raise RuntimeError(f"{owner}: invalid rule {index}")
    return RuleView(label, old, new, occurrences, rule)


def normalized_rules(owner: str, module: ModuleType) -> tuple[RuleView, ...]:
    raw_rules = tuple(getattr(module, "RULES", ()))
    if not raw_rules:
        raise RuntimeError(f"{owner}: no RULES")
    return tuple(
        normalize_rule(owner, index, rule)
        for index, rule in enumerate(raw_rules)
    )


def header_multiplicity(header: object) -> int:
    if isinstance(header, dict):
        return int(header.get("multiplicity", 1))
    if isinstance(header, (tuple, list)):
        if len(header) > 4 and isinstance(header[4], int):
            return int(header[4])
        return 1
    return int(getattr(header, "multiplicity", 1))


def header_kind(header: object) -> str:
    if isinstance(header, dict):
        return str(header.get("kind", "direct"))
    if isinstance(header, (tuple, list)):
        return str(header[5]) if len(header) > 5 else "direct"
    return str(getattr(header, "kind", "direct"))


def diagnostic_counts(module: ModuleType) -> tuple[int, int]:
    values: list[object] = []
    global_headers = getattr(module, "HEADERS", None)
    if global_headers is not None:
        values.extend(tuple(global_headers))
    else:
        for rule in tuple(getattr(module, "RULES", ())):
            plural = getattr(rule, "headers", None)
            singular = getattr(rule, "header", None)
            if plural is not None:
                values.extend(tuple(plural))
            elif singular is not None:
                values.append(singular)
            elif isinstance(rule, (tuple, list)) and len(rule) > 3:
                values.append(rule[3])
    owned = sum(header_multiplicity(header) for header in values)
    direct = sum(
        header_multiplicity(header)
        for header in values
        if header_kind(header) != "cascade"
    )
    return owned, direct


def load_components() -> tuple[Loaded, ...]:
    loaded: list[Loaded] = []
    for component in COMPONENTS:
        path = resolve_exact(
            component.relative_path,
            helper_shape(component),
            component.label,
        )
        module = import_exact(
            component.label,
            path,
            helper_shape(component),
        )
        rules = normalized_rules(component.label, module)
        if (
            len(rules) != component.expected_rules
            or sum(rule.occurrences for rule in rules)
            != component.expected_occurrences
        ):
            raise RuntimeError(f"{component.label}: rule totals drifted")
        if diagnostic_counts(module) != (
            component.expected_owned_diagnostics,
            component.expected_direct_diagnostics,
        ):
            raise RuntimeError(f"{component.label}: diagnostic totals drifted")
        loaded.append(Loaded(component, path, module, rules))
    if (
        sum(len(item.rules) for item in loaded) != EXPECTED_RULES
        or sum(
            rule.occurrences
            for item in loaded
            for rule in item.rules
        ) != EXPECTED_OCCURRENCES
        or sum(
            item.component.expected_owned_diagnostics
            for item in loaded
        ) != EXPECTED_OWNED_DIAGNOSTICS
        or sum(
            item.component.expected_direct_diagnostics
            for item in loaded
        ) != EXPECTED_DIRECT_DIAGNOSTICS
    ):
        raise RuntimeError("integrated totals drifted")
    return tuple(loaded)


def load_baselines() -> tuple[LoadedBaseline, ...]:
    loaded: list[LoadedBaseline] = []
    for baseline in BASELINE_HELPERS:
        path = resolve_exact(
            baseline.relative_path,
            baseline_shape(baseline),
            baseline.owner,
        )
        module = import_exact(
            "baseline_" + baseline.owner,
            path,
            baseline_shape(baseline),
        )
        rules = normalized_rules(baseline.owner, module)
        loaded.append(LoadedBaseline(baseline, path, module, rules))
    return tuple(loaded)


def apply_rule_set(
    text: str,
    item: Loaded,
    inverse: bool,
) -> tuple[str, list[dict[str, object]]]:
    rules = tuple(reversed(item.rules)) if inverse else item.rules
    records: list[dict[str, object]] = []
    for rule in rules:
        source, target = (
            (rule.new, rule.old) if inverse else (rule.old, rule.new)
        )
        count = text.count(source)
        if count != rule.occurrences:
            raise RuntimeError(
                f"{item.component.label}:{rule.label}: "
                f"anchor count {count}"
            )
        text = text.replace(source, target, rule.occurrences)
        records.append(
            {
                "component": item.component.label,
                "label": rule.label,
                "inverse": inverse,
                "occurrences": count,
            }
        )
    return text, records


def apply_order(
    text: str,
    loaded: tuple[Loaded, ...],
    order: tuple[int, ...],
    inverse: bool,
) -> tuple[str, list[dict[str, object]]]:
    result = text
    records: list[dict[str, object]] = []
    indices = tuple(reversed(order)) if inverse else order
    for index in indices:
        result, rows = apply_rule_set(result, loaded[index], inverse)
        records.extend(rows)
    return result, records


def spans(text: str, needle: str) -> list[tuple[int, int]]:
    found: list[tuple[int, int]] = []
    start = 0
    while True:
        position = text.find(needle, start)
        if position < 0:
            return found
        found.append((position, position + len(needle)))
        start = position + 1


def component_declarations(loaded: tuple[Loaded, ...]) -> list[dict[str, str]]:
    declarations: list[dict[str, str]] = []
    for item in loaded:
        if item.component.label == "edge_derivatives":
            raw = tuple(
                getattr(item.module, "DECLARED_CONSUMED_NEW_OVERLAPS", ())
            )
            for record in raw:
                declarations.append(
                    {
                        "component": item.component.label,
                        "own_rule": str(record["own_rule"]),
                        "foreign_owner": str(record["foreign_owner"]),
                        "foreign_rule": str(record["foreign_rule"]),
                        "relation": str(record["relation"]),
                    }
                )
        elif item.component.label == "tail_refinements":
            for rule in item.rules:
                source = rule.source
                relation = getattr(source, "relation", None)
                if relation is None:
                    continue
                declarations.append(
                    {
                        "component": item.component.label,
                        "own_rule": rule.label,
                        "foreign_owner": str(
                            getattr(source, "consumed_owner")
                        ),
                        "foreign_rule": str(
                            getattr(source, "consumed_rule")
                        ),
                        "relation": str(relation),
                    }
                )
        else:
            raise RuntimeError(
                f"unknown component declaration contract: "
                f"{item.component.label}"
            )
    if len(declarations) != EXPECTED_DECLARED_HISTORICAL_OVERLAPS:
        raise RuntimeError("declared historical overlap count drift")
    return declarations


def verify_spans_and_overlaps(
    source: str,
    loaded: tuple[Loaded, ...],
    baselines: tuple[LoadedBaseline, ...],
) -> dict[str, object]:
    own_spans: list[tuple[int, int, str, RuleView]] = []
    standalone: dict[str, object] = {}
    for item in loaded:
        output, _ = apply_rule_set(source, item, False)
        output_raw = output.encode("utf-8")
        if shape(output_raw) != standalone_shape(item.component):
            raise RuntimeError(
                f"{item.component.label}: standalone output drift"
            )
        standalone[item.component.label] = shape(output_raw)
        for rule in item.rules:
            found = spans(source, rule.old)
            if len(found) != rule.occurrences:
                raise RuntimeError(
                    f"{item.component.label}:{rule.label}: "
                    "authority anchor drift"
                )
            own_spans.extend(
                (start, end, item.component.label, rule)
                for start, end in found
            )

    own_sorted = sorted(own_spans, key=lambda row: row[0])
    cross: list[object] = []
    for left, right in itertools.combinations(own_sorted, 2):
        if (
            left[2] != right[2]
            and max(left[0], right[0]) < min(left[1], right[1])
        ):
            cross.append((left[2], left[3].label, right[2], right[3].label))
    if cross:
        raise RuntimeError(f"cross-component source-span overlap: {cross}")

    declarations = component_declarations(loaded)
    declaration_map = {
        (
            row["component"],
            row["own_rule"],
            row["foreign_owner"],
            row["foreign_rule"],
        ): row["relation"]
        for row in declarations
    }
    if len(declaration_map) != len(declarations):
        raise RuntimeError("duplicate overlap declaration")

    actual: list[dict[str, str]] = []
    baseline_identities: dict[str, dict[str, object]] = {}
    for baseline in baselines:
        baseline_identities[baseline.baseline.owner] = baseline_shape(
            baseline.baseline
        )
        for foreign_rule in baseline.rules:
            found = spans(source, foreign_rule.new)
            if len(found) != foreign_rule.occurrences:
                raise RuntimeError(
                    f"{baseline.baseline.owner}:{foreign_rule.label}: "
                    "applied anchor drift"
                )
            for fstart, fend in found:
                for ostart, oend, component, own_rule in own_spans:
                    if max(fstart, ostart) >= min(fend, oend):
                        continue
                    key = (
                        component,
                        own_rule.label,
                        baseline.baseline.owner,
                        foreign_rule.label,
                    )
                    relation = declaration_map.get(key)
                    if relation is None:
                        raise RuntimeError(
                            f"undeclared historical overlap: {key}"
                        )
                    if relation == "own_old_contains_consumed_new":
                        if foreign_rule.new not in own_rule.old:
                            raise RuntimeError(
                                f"containment declaration drift: {key}"
                            )
                    elif relation == "own_old_equals_consumed_new":
                        if own_rule.old != foreign_rule.new:
                            raise RuntimeError(
                                f"equality declaration drift: {key}"
                            )
                    else:
                        raise RuntimeError(
                            f"unknown historical relation: {relation}"
                        )
                    actual.append(
                        {
                            "component": component,
                            "own_rule": own_rule.label,
                            "foreign_owner": baseline.baseline.owner,
                            "foreign_rule": foreign_rule.label,
                            "relation": relation,
                        }
                    )

    actual_map = {
        (
            row["component"],
            row["own_rule"],
            row["foreign_owner"],
            row["foreign_rule"],
        ): row["relation"]
        for row in actual
    }
    if actual_map != declaration_map:
        raise RuntimeError(
            f"historical overlap set drift: {actual_map} != "
            f"{declaration_map}"
        )
    return {
        "standalone_outputs": standalone,
        "source_spans": len(own_spans),
        "cross_component_overlaps": 0,
        "declared_historical_overlaps": actual,
        "undeclared_historical_overlaps": 0,
        "baseline_helper_identities": baseline_identities,
    }


def audit_all_orders(
    source: str,
    loaded: tuple[Loaded, ...],
) -> dict[str, object]:
    hashes: set[str] = set()
    count = 0
    for order in itertools.permutations(range(len(loaded))):
        forward, _ = apply_order(source, loaded, order, False)
        forward_raw = forward.encode("utf-8")
        if shape(forward_raw) != expected_shape(True):
            raise RuntimeError(f"component-order output drift: {order}")
        if any(trust(forward).values()):
            raise RuntimeError(f"component-order trust drift: {order}")
        hashes.add(sha256(forward_raw))
        restored, _ = apply_order(forward, loaded, order, True)
        if restored != source:
            raise RuntimeError(f"component-order inverse drift: {order}")
        count += 1
    if count != 2 or hashes != {OUTPUT_SHA256}:
        raise RuntimeError("all-order audit failed")
    return {
        "orders": count,
        "unique_outputs": len(hashes),
        "output_sha256": OUTPUT_SHA256,
        "output_git_blob": OUTPUT_GIT_BLOB,
        "matching_reverse_inverses_exact": True,
        "trust0": True,
    }


def transform(
    text: str,
    loaded: tuple[Loaded, ...],
    inverse: bool,
) -> tuple[str, list[dict[str, object]]]:
    if shape(text.encode("utf-8")) != expected_shape(inverse):
        raise RuntimeError("exact integrated input candidate gate failed")
    before = trust(text)
    if any(before.values()):
        raise RuntimeError(f"source trust0 failure: {before}")
    result, records = apply_order(
        text,
        loaded,
        tuple(range(len(loaded))),
        inverse,
    )
    if shape(result.encode("utf-8")) != expected_shape(not inverse):
        raise RuntimeError("integrated output identity mismatch")
    after = trust(result)
    if before != after or any(after.values()):
        raise RuntimeError(f"integrated trust drift: {before} -> {after}")
    return result, records


def verify_authority(
    result_raw: bytes,
    log_raw: bytes,
    headers_raw: bytes,
    diagnostics_raw: bytes,
    exit_raw: bytes,
    panic_raw: bytes,
) -> dict[str, object]:
    for name, raw, expected in (
        ("result", result_raw, RESULT_SHA256),
        ("log", log_raw, LOG_SHA256),
        ("headers", headers_raw, HEADERS_SHA256),
        ("diagnostics", diagnostics_raw, DIAGNOSTICS_SHA256),
    ):
        if sha256(raw) != expected:
            raise RuntimeError(
                f"exact Probe16 {name} sidecar gate failed"
            )
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
            raise RuntimeError(
                f"Probe16 result field mismatch: {key}"
            )
    headers = headers_raw.decode("utf-8", errors="strict").splitlines()
    diagnostics = [
        json.loads(line)
        for line in diagnostics_raw.decode(
            "utf-8",
            errors="strict",
        ).splitlines()
        if line
    ]
    errors = sum(row.get("severity") == "error" for row in diagnostics)
    warnings = sum(
        row.get("severity") == "warning" for row in diagnostics
    )
    if (len(headers), errors, warnings) != (
        EXPECTED_ERRORS,
        EXPECTED_ERRORS,
        EXPECTED_WARNINGS,
    ):
        raise RuntimeError("Probe16 diagnostic totals mismatch")
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
        "errors": errors,
        "warnings": warnings,
        "panic": EXPECTED_PANIC,
        "exit": EXPECTED_EXIT,
    }


def preflight(paths: tuple[Path, ...]) -> None:
    resolved = tuple(path.resolve() for path in paths)
    if len(set(resolved)) != len(resolved):
        raise RuntimeError("output and audit destinations must be distinct")
    for path in resolved:
        if path.exists():
            raise RuntimeError(f"refusing overwrite: {path}")
        if not path.parent.is_dir() or path.parent.is_symlink():
            raise RuntimeError(
                f"destination parent must be an existing real directory: "
                f"{path}"
            )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--audit", type=Path, required=True)
    parser.add_argument("--inverse", action="store_true")
    parser.add_argument("--probe16-result", type=Path, required=True)
    parser.add_argument("--probe16-log", type=Path, required=True)
    parser.add_argument("--probe16-error-headers", type=Path, required=True)
    parser.add_argument("--probe16-diagnostics", type=Path, required=True)
    parser.add_argument("--probe16-exit", type=Path, required=True)
    parser.add_argument("--probe16-panic-lines", type=Path, required=True)
    args = parser.parse_args()

    preflight((args.output, args.audit))
    authority = verify_authority(
        args.probe16_result.read_bytes(),
        args.probe16_log.read_bytes(),
        args.probe16_error_headers.read_bytes(),
        args.probe16_diagnostics.read_bytes(),
        args.probe16_exit.read_bytes(),
        args.probe16_panic_lines.read_bytes(),
    )
    loaded = load_components()
    baselines = load_baselines()
    source_raw = args.input.read_bytes()
    source = source_raw.decode("utf-8", errors="strict")
    authority_source = source
    if args.inverse:
        authority_source, _ = transform(source, loaded, True)
    span_audit = verify_spans_and_overlaps(
        authority_source,
        loaded,
        baselines,
    )
    order_audit = audit_all_orders(authority_source, loaded)
    result, records = transform(source, loaded, args.inverse)
    restored, inverse_records = transform(
        result,
        loaded,
        not args.inverse,
    )
    if restored.encode("utf-8") != source_raw:
        raise RuntimeError("canonical inverse is not byte exact")

    record = {
        "schema": SCHEMA,
        "status": "STATIC_PASS_EXACT_COMPOSITION_NOT_LEAN_EXECUTED",
        "activation": ACTIVATION,
        "promotion": PROMOTION,
        "mode": "inverse" if args.inverse else "forward",
        "authority": authority,
        "source": shape(source_raw),
        "result": shape(result.encode("utf-8")),
        "components": [asdict(component) for component in COMPONENTS],
        "baseline_helpers": [
            asdict(baseline) for baseline in BASELINE_HELPERS
        ],
        "repair_families": EXPECTED_RULES,
        "repair_occurrences": EXPECTED_OCCURRENCES,
        "owned_diagnostics": EXPECTED_OWNED_DIAGNOSTICS,
        "direct_diagnostics": EXPECTED_DIRECT_DIAGNOSTICS,
        "cascade_diagnostics": (
            EXPECTED_OWNED_DIAGNOSTICS
            - EXPECTED_DIRECT_DIAGNOSTICS
        ),
        "rules": records,
        "matching_inverse_rules": inverse_records,
        "inverse_byte_equal": True,
        "span_audit": span_audit,
        "all_order_audit": order_audit,
        "trust": trust(result),
        "execution": {
            "lean": False,
            "lake": False,
            "git": False,
            "network": False,
            "remote": False,
            "install": False,
            "canonical_source_mutation": False,
        },
    }
    result_raw = result.encode("utf-8")
    audit_raw = (
        json.dumps(record, ensure_ascii=False, indent=2) + "\n"
    ).encode("utf-8")
    args.output.write_bytes(result_raw)
    args.audit.write_bytes(audit_raw)
    print(
        json.dumps(
            {
                "result": record["result"],
                "orders": order_audit["orders"],
                "declared_historical_overlaps": (
                    len(
                        span_audit[
                            "declared_historical_overlaps"
                        ]
                    )
                ),
                "inverse_exact": True,
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
