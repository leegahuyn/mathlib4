#!/usr/bin/env python3
"""Materialize one fail-closed cumulative Mock2 FA candidate.

This preparer starts from the exact d0a3 source extracted from the completed
maxErrors=2000 artifact.  It composes four independently audited inputs:

1. the early fragment library (including idx3640),
2. one global canonical-instance environment edit,
3. the selected idx2974--3002 environment/proof package, with its duplicate
   local-instance command deliberately reduced to the two narrow opens, and
4. a later exact-literal root library supplied by the downstream analyzer.

No Lean, Lake, git, or GitHub operation is performed here.  Every edit is
literal, source-locked, inventory-root-gated, and included in an immutable
marker skeleton.  Missing evidence or any PENDING identity is an error.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import os
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any


SOURCE_SHA256 = "d0a3decee1c0a7a781d14fdf122e235d71d8f210bb65a894dc4e518821bf03ec"
SOURCE_BYTES = 2_702_252
SOURCE_LINES = 60_573
SOURCE_DECLARATIONS = 4_397
SOURCE_DECLARATION_SEQUENCE_SHA256 = (
    "a33d2a1e132e47c9c6b31924ed1b8a04a50de709ed2149a9f9abfb0b052b25eb"
)
CHECKED_OUT_SOURCE_SHA256 = (
    "b51c2ddcdfec8b98a89734575ef57b681f47eefba8b879028a3233439b70906a"
)

INVENTORY_SHA256 = (
    "3692fd155f6029ad30678668ff83fd5f092facebd9e35829cd680b1644d59648"
)
VALIDATOR_SHA256 = (
    "4804d0d73a01ca1600080f892bbd391bffd092b5a2b529ac302e06fd82079a76"
)
EARLY_LIBRARY_SHA256 = (
    "c503ca6383d74537a058280410a013d77691b0812e57be360afd38ea20fb8da0"
)
SELECTED_ENVIRONMENT_LIBRARY_SHA256 = (
    "3b22e7cff8ba4c502852b17f074bb22a431b17e4b93fd8b8af6f6a5da4a61243"
)
GLOBAL_INSTANCE_LIBRARY_SHA256 = (
    "4c90fa27cfa482dfc9ffc9588a4d3742ccc32b77519f0510715feeb2b94d6e23"
)
FINRANK_LIBRARY_SHA256 = (
    "847133cc01d9d6551f289a80f107821aba3072e2488468ce231002496c8be3e0"
)

BASE_RUN_ID = 31_495_034_235
BASE_JOB_ID = 93_790_488_049
BASE_HEAD_SHA = "989132c0ac49fdfd7ff637a5b77c45b73e02f32f"
BASE_ARTIFACT_ID = 9_103_368_138
BASE_ARTIFACT_NAME = (
    "codex-fa506r2-full-diagnostic-d0a3-"
    "989132c0ac49fdfd7ff637a5b77c45b73e02f32f"
)
BASE_ARTIFACT_SIZE = 1_446_570
BASE_ARTIFACT_DIGEST = (
    "sha256:eb21e1d4fe0c0652e6d8463592fd4c550005f29bcb9611f18c8533ba888bd6f4"
)

EXPECTED_INVENTORY_SUMMARY = {
    "actual_semantic_or_resource_errors": 1_157,
    "affected_declarations": 608,
    "cap_sentinels": 0,
    "log_error_headers": 1_157,
    "resource_limit_roots": 24,
    "root_affected_declarations": 608,
    "root_candidate_errors": 987,
    "suspected_cascade_errors": 170,
    "unowned_actual_errors": 0,
}

LOCAL_INSTANCE_BLOCK = """

attribute [local instance]
  DefinitionOneSobolev.FixedPhaseGraphCompletion.fixedPhaseGraphCoreModule
  DefinitionOneSobolev.FixedPhaseGraphCompletion.fixedPhaseGraphCoreAddCommGroup"""

SUPERSEDED_EARLY_FRAGMENT = {
    "declaration_index": 2_977,
    "old_sha256": "338cc2c5ca7b1c77984c98d0bfaf4588e842bedba828d17ac5c5c8443338c910",
    "new_sha256": "900334e0864290c9353c2948a764baba4afe733653384bfda8e89e6c6ecd152f",
    "reason": (
        "selected environment package supplies the stronger explicit change-to-real-norm "
        "repair; retain only the independent maxHeartbeats fragment from the early library"
    ),
}

# These legacy source-global late edits crossed declaration-header boundaries.
# The revised locked library must not contain them: CLM resolution is supplied
# by a separate six-scope bounded overlay, while the three measure edits would
# change public claims and remain permanently staged.
FORBIDDEN_LATE_HEADER_EDIT_IDS = {
    "qualify_clm_lsmul_real",
    "qualify_clm_lsmul_complex",
    "qualify_clm_mul_parenthesized",
    "qualify_clm_mul_convolution",
    "measure_ae_chosen_multiline",
    "measure_ae_generic_mu",
    "measure_ae_volume",
}


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_text(text: str) -> str:
    return sha256_bytes(text.encode("utf-8"))


def json_bytes(value: Any) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode("utf-8")


def decode_lf(path: Path) -> str:
    data = path.read_bytes()
    if data.startswith(b"\xef\xbb\xbf"):
        raise RuntimeError(f"UTF-8 BOM is forbidden: {path}")
    if b"\r" in data:
        raise RuntimeError(f"CR bytes are forbidden in Lean/JSON authority: {path}")
    return data.decode("utf-8")


def require_sha64_env(name: str) -> str:
    value = os.environ.get(name, "")
    if (
        value.startswith("PENDING")
        or value == "0" * 64
        or re.fullmatch(r"[0-9a-f]{64}", value) is None
    ):
        raise RuntimeError(f"{name} must be a hydrated lowercase SHA256, got {value!r}")
    return value


def require_decimal_env(name: str) -> int:
    value = os.environ.get(name, "")
    if value.startswith("PENDING") or re.fullmatch(r"[1-9][0-9]*", value) is None:
        raise RuntimeError(f"{name} must be a hydrated positive decimal, got {value!r}")
    return int(value)


def load_json_locked(path: Path, expected_sha256: str, label: str) -> dict[str, Any]:
    if expected_sha256.startswith("PENDING"):
        raise RuntimeError(f"{label} SHA is still PENDING")
    data = path.read_bytes()
    actual = sha256_bytes(data)
    if actual != expected_sha256:
        raise RuntimeError(f"{label} SHA drift: {actual}; expected {expected_sha256}")
    if b"\r" in data:
        raise RuntimeError(f"{label} must be canonical LF JSON")
    payload = json.loads(data.decode("utf-8"))
    if not isinstance(payload, dict):
        raise RuntimeError(f"{label} is not a JSON object")
    return payload


def load_validator(path: Path):
    data = path.read_bytes()
    actual = sha256_bytes(data)
    if actual != VALIDATOR_SHA256:
        raise RuntimeError(
            f"full inventory validator SHA drift: {actual}; expected {VALIDATOR_SHA256}"
        )
    spec = importlib.util.spec_from_file_location("fa_full_inventory_locked", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot import locked validator {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def validate_inventory(payload: dict[str, Any]) -> dict[str, dict[str, Any]]:
    if payload.get("schema") != "fa-full-compile-error-inventory-v1":
        raise RuntimeError("full inventory schema drift")
    if payload.get("status") != "COMPLETE":
        raise RuntimeError("full inventory is not COMPLETE")
    if payload.get("summary") != EXPECTED_INVENTORY_SUMMARY:
        raise RuntimeError("full inventory summary drift")
    complete = payload.get("completeness") or {}
    if (
        complete.get("complete_full_diagnostic_inventory") is not True
        or complete.get("diagnostic_cap_reached") is not False
        or complete.get("cap_sentinel_error_ids") != []
    ):
        raise RuntimeError("full inventory completeness/cap contract drift")
    collector = payload.get("full_diagnostics_collector_contract") or {}
    if (
        collector.get("all_checks_passed") is not True
        or collector.get("schema") != "fa506r2-full-diagnostics-v1"
        or (collector.get("collector_severity_counts") or {}).get("error") != 1_157
        or (collector.get("collector_severity_counts") or {}).get("warning") != 659
    ):
        raise RuntimeError("corrected optional-code collector authority drift")
    source = payload.get("source") or {}
    expected_source = {
        "sha256": SOURCE_SHA256,
        "bytes": SOURCE_BYTES,
        "lines": SOURCE_LINES,
        "declaration_count": SOURCE_DECLARATIONS,
        "declaration_sequence_sha256": SOURCE_DECLARATION_SEQUENCE_SHA256,
    }
    for key, value in expected_source.items():
        if source.get(key) != value:
            raise RuntimeError(f"full inventory source {key} drift")
    diagnostics: dict[str, dict[str, Any]] = {}
    for row in payload.get("all_diagnostics", []):
        identifier = row.get("id")
        if not isinstance(identifier, str) or identifier in diagnostics:
            raise RuntimeError("full inventory diagnostic ID drift")
        diagnostics[identifier] = row
    if len([row for row in diagnostics.values() if not row.get("is_cap_sentinel")]) != 1_157:
        raise RuntimeError("full inventory diagnostic cardinality drift")
    return diagnostics


def validate_root_ids(
    diagnostics: dict[str, dict[str, Any]],
    identifiers: list[str],
    *,
    owner_index: int | None = None,
) -> None:
    retained_roots = 0
    for identifier in identifiers:
        row = diagnostics.get(identifier)
        if row is None:
            raise RuntimeError(f"unknown full-inventory selector {identifier}")
        classification = row.get("classification")
        if classification not in {
            "root_candidate",
            "resource_limit_root",
            "suspected_cascade",
        }:
            raise RuntimeError(f"selector {identifier} is not a semantic inventory error")
        if classification in {"root_candidate", "resource_limit_root"}:
            retained_roots += 1
        if owner_index is not None and row.get("declaration_index") != owner_index:
            raise RuntimeError(f"selector {identifier} owner drift")
    if identifiers and retained_roots == 0:
        owner_has_root = owner_index is not None and any(
            row.get("declaration_index") == owner_index
            and row.get("classification") in {"root_candidate", "resource_limit_root"}
            for row in diagnostics.values()
        )
        if not owner_has_root:
            raise RuntimeError("selector group has no retained root anchor")


def validate_source_identity(text: str, validator: Any) -> tuple[list[dict[str, Any]], dict[str, Any]]:
    rows = validator.declarations(text)
    identity = validator.source_static_identity(text, rows)
    expected = {
        "sha256": SOURCE_SHA256,
        "bytes": SOURCE_BYTES,
        "lines": SOURCE_LINES,
        "declaration_count": SOURCE_DECLARATIONS,
        "declaration_sequence_sha256": SOURCE_DECLARATION_SEQUENCE_SHA256,
    }
    for key, value in expected.items():
        if identity.get(key) != value:
            raise RuntimeError(f"d0a3 source {key} drift: {identity.get(key)!r}")
    if any(identity["executable_forbidden_counts"].values()):
        raise RuntimeError("d0a3 executable forbidden-six is nonzero")
    return rows, identity


def validate_attestation(path: Path, base_source: Path) -> dict[str, Any]:
    expected_sha = require_sha64_env("FA_FULL_BASE_ATTESTATION_SHA256")
    payload = load_json_locked(path, expected_sha, "base artifact live attestation")
    exact = {
        "schema": "fa-full-base-artifact-attestation-v1",
        "repository": "leegahuyn/mathlib4",
        "target_branch": "codex/fa-qym-cleanbuild-final-20260811-fast",
        "run_id": BASE_RUN_ID,
        "job_id": BASE_JOB_ID,
        "head_sha": BASE_HEAD_SHA,
        "artifact_id": BASE_ARTIFACT_ID,
        "artifact_name": BASE_ARTIFACT_NAME,
        "artifact_size": BASE_ARTIFACT_SIZE,
        "artifact_digest": BASE_ARTIFACT_DIGEST,
        "all_checks_passed": True,
    }
    for key, value in exact.items():
        if payload.get(key) != value:
            raise RuntimeError(f"base artifact attestation {key} drift")
    checks = payload.get("checks") or {}
    if not checks or not all(value is True for value in checks.values()):
        raise RuntimeError("base artifact attestation checks did not all pass")
    source = payload.get("source") or {}
    expected_source = {
        "sha256": SOURCE_SHA256,
        "bytes": SOURCE_BYTES,
        "lines": SOURCE_LINES,
    }
    for key, value in expected_source.items():
        if source.get(key) != value:
            raise RuntimeError(f"attested base source {key} drift")
    if Path(str(source.get("path", ""))).resolve() != base_source.resolve():
        raise RuntimeError("attested base source path drift")
    return payload


@dataclass(frozen=True)
class Edit:
    identifier: str
    library: str
    scope: str
    mode: str
    old: str
    new: str
    expected_old: int
    expected_new_before: int
    declaration_index: int | None = None
    declaration_name: str | None = None
    header_sha256: str | None = None
    diagnostic_ids: tuple[str, ...] = ()
    enforce_global_counts: bool = True


def check_fragment_metadata(fragment: dict[str, Any], label: str) -> tuple[str, str]:
    old = fragment.get("old_fragment")
    new = fragment.get("new_fragment")
    if not isinstance(old, str) or not isinstance(new, str) or old == new:
        raise RuntimeError(f"{label}: invalid literal fragments")
    expected = {
        "old_sha256": sha256_text(old),
        "new_sha256": sha256_text(new),
        "old_bytes": len(old.encode("utf-8")),
        "new_bytes": len(new.encode("utf-8")),
    }
    for key, value in expected.items():
        if key in fragment and fragment.get(key) != value:
            raise RuntimeError(f"{label}: {key} drift")
    return old, new


def standard_repairs(
    payload: dict[str, Any],
    library: str,
    diagnostics: dict[str, dict[str, Any]],
    *,
    skip_superseded: bool = False,
) -> tuple[list[Edit], list[dict[str, Any]]]:
    edits: list[Edit] = []
    superseded: list[dict[str, Any]] = []
    for repair in payload.get("repairs", []):
        index = repair.get("declaration_index")
        name = repair.get("declaration_name")
        header_sha = repair.get("header_sha256")
        if not isinstance(index, int) or not isinstance(name, str):
            raise RuntimeError(f"{library}: invalid standard repair owner")
        root_ids = repair.get("root_selector_ids") or repair.get("diagnostic_ids")
        if root_ids is None:
            root_ids = (repair.get("evidence") or {}).get("diagnostic_ids", [])
        root_ids = list(root_ids)
        validate_root_ids(diagnostics, root_ids, owner_index=index)
        for position, fragment in enumerate(repair.get("replacements", [])):
            old, new = check_fragment_metadata(
                fragment, f"{library}:idx{index}:fragment{position}"
            )
            if skip_superseded and (
                index == SUPERSEDED_EARLY_FRAGMENT["declaration_index"]
                and sha256_text(old) == SUPERSEDED_EARLY_FRAGMENT["old_sha256"]
                and sha256_text(new) == SUPERSEDED_EARLY_FRAGMENT["new_sha256"]
            ):
                superseded.append(
                    {
                        **SUPERSEDED_EARLY_FRAGMENT,
                        "library": library,
                        "old_fragment": old,
                        "new_fragment": new,
                    }
                )
                continue
            edits.append(
                Edit(
                    iden×]÷îÚ$z{-®éÜj×7WÆVÖVçFÅöVF—G2€¢7WÆVÖVçFÅö–æFW‚Â7WÆVÖVçFÅö–æFW…÷F‚ÂF–væ÷7F–70¢¢F÷vç7G&VÒÒÆFUöVF—G2†ÆFRÂF–væ÷7F–72¢ÆFUöÆÂÒ¶VF—Bf÷"VF—B–âF÷vç7G&VÒ–bVF—BæÖöFRÓÒ&Æ—FW&ÅöÆÂ%Ð ¢FVbÆFUö6÷fW"†VF—C¢VF—B’ÓâVF—BÂæöæS ¢–bVF—BæÖöFRÒ&Æ—FW&ÅöW†7B# ¢&WGW&âæöæP¢f÷"'&öB–âÆFUöÆÃ ¢–b†VF—BæöÆBÂVF—BææWr’ÓÒ†'&öBæöÆBÂ'&öBææWr“ ¢&WGW&â'&ö@¢–b€¢VF—BæFV6Æ&F–öåö–æFW‚–â³5ó3‚Â5ó3—Ð¢æB'&öBæöÆB–âVF—BæöÆ@¢æB'&öBææWr–âVF—BææWp¢“ ¢&WGW&â'&ö@¢&WGW&âæöæP ¢FVGWÆ–6FVBÒ¶VF—Bf÷"VF—B–â7WÆVÖVçFÂ–bÆFUö6÷fW"†VF—B’—2æ÷BæöæUÐ¢7WÆVÖVçFÂÒ¶VF—Bf÷"VF—B–â7WÆVÖVçFÂ–bVF—Bæ÷B–âFVGWÆ–6FVEÐ¢FVGWöVF—BÒ°¢°¢&–B#¢VF—Bæ–FVçF–f–W"À¢&FV6Æ&F–öåö–æFW‚#¢VF—BæFV6Æ&F–öåö–æFW‚À¢&FV6Æ&F–öåöæÖR#¢VF—BæFV6Æ&F–öåöæÖRÀ¢&öÆE÷6†#Sb#¢6†#Se÷FW‡B†VF—BæöÆB’À¢&æWu÷6†#Sb#¢6†#Se÷FW‡B†VF—BææWr’À¢&6÷fW&–æuöÆFUöVF—Eö–B#¢ÆFUö6÷fW"†VF—B’æ–FVçF–f–W"À¢'&V6öâ#¢&6÷fW&VBW†7FÇ’öæ6R'’F†RÆFRÆ–'&'’w26÷W&6RÖvÆö&ÂÆ—FW&ÅöÆÂVF—B"À¢Ð¢f÷"VF—B–âFVGWÆ–6FV@¢Ð¢FVGWö–æF–6W2Ò6÷'FVB€¢VF—BæFV6Æ&F–öåö–æFW€¢f÷"VF—B–âFVGWÆ–6FV@¢–bVF—BæFV6Æ&F–öåö–æFW‚—2æ÷BæöæP¢¢–bFVGWö–æF–6W3 ¢&—6R'VçF–ÖTW'&÷"€¢b'VæW‡V7FVB&öÖ÷FVBÆFRÆ—FW&ÂÖÆÂ÷fW&Æ6WB¶FVGWö–æF–6W7Ò ¢¢&÷VæFVEö÷fW&Æ•÷&÷w2Ò°¢&÷p¢f÷"&÷r–â7WÆVÖVçFÅöVF—@¢–b&÷u²&&6VæÖR%Ð¢ÓÒ&föC5ö&÷VæFVEö6öçF–çV÷W5öÆ–æV%öÖöVçf—&öæÖVçEö÷fW&Æ’æ§6öâ ¢Ð¢–bÆVâ†&÷VæFVEö÷fW&Æ•÷&÷w2’Ò÷"&÷VæFVEö÷fW&Æ•÷&÷w5³Õ²&VF—Eö6÷VçB%ÒÒc ¢&—6R'VçF–ÖTW'&÷"‚&WF†÷&—FF—fR6—‚×66÷R4ÄÒ÷fW&Æ’—2æ÷B6VÆV7FVBöæ6R"¢&÷VæFVEö6ÆÕö–æF–6W2Ò³5ó3‚Â5ó3’Â5óCCÂ5ócÂ5ócSÐ ¢FVb&÷VæFVEö6ÆÕö6÷fW"†VF—C¢VF—B’Óâ&ööÃ ¢&WGW&â€¢VF—BæÖöFRÓÒ&Æ—FW&ÅöW†7B ¢æBVF—BæFV6Æ&F–öåö–æFW‚–â&÷VæFVEö6ÆÕö–æF–6W0¢æB&Ç6×VÂ"–âVF—BæöÆ@¢æB$6öçF–çV÷W4Æ–æV$ÖæÇ6×VÂ"–âVF—BææWp¢ ¢&÷VæFVEöFVGWÆ–6FVBÒ¶VF—Bf÷"VF—B–â7WÆVÖVçFÂ–b&÷VæFVEö6ÆÕö6÷fW"†VF—B•Ð¢&÷VæFVEöFVGWö–æF–6W2Ò6÷'FVB€¢VF—BæFV6Æ&F–öåö–æFW€¢f÷"VF—B–â&÷VæFVEöFVGWÆ–6FV@¢–bVF—BæFV6Æ&F–öåö–æFW‚—2æ÷BæöæP¢¢–b&÷VæFVEöFVGWö–æF–6W2Ò6÷'FVB†&÷VæFVEö6ÆÕö–æF–6W2“ ¢&—6R'VçF–ÖTW'&÷"€¢&&÷VæFVB4ÄÒ7WW'6W76–öâ6WBG&–gC¢ ¢b'¶&÷VæFVEöFVGWö–æF–6W7Ó²W‡V7FVB·6÷'FVB†&÷VæFVEö6ÆÕö–æF–6W2—Ò ¢¢7WÆVÖVçFÂÒ°¢VF—Bf÷"VF—B–â7WÆVÖVçFÂ–bVF—Bæ÷B–â&÷VæFVEöFVGWÆ–6FV@¢Ð¢&÷VæFVEöFVGWöVF—BÒ°¢°¢&–B#¢VF—Bæ–FVçF–f–W"À¢&FV6Æ&F–öåö–æFW‚#¢VF—BæFV6Æ&F–öåö–æFW‚À¢&FV6Æ&F–öåöæÖR#¢VF—BæFV6Æ&F–öåöæÖRÀ¢&öÆE÷6†#Sb#¢6†#Se÷FW‡B†VF—BæöÆB’À¢&æWu÷6†#Sb#¢6†#Se÷FW‡B†VF—BææWr’À¢'&V6öâ#¢€¢'7WW'6VFVB'’æÖW76RÖ&÷VæFVB÷Vâ6öçF–çV÷W4Æ–æV$Ö ¢'F†B&W6W'fW2&ööbæBFV6Æ&F–öâÖ†VFW"'—FW2 ¢’À¢Ð¢f÷"VF—B–â&÷VæFVEöFVGWÆ–6FV@¢Ð¢VF—G2Ò€¢Vçf—&öæÖVç@¢²6VÆV7FVE÷&W—'0¢²V&Ç•÷&W—'0¢²f–ç&æµ÷&W—'0¢²7WÆVÖVçFÀ¢²F÷vç7G&VÐ¢¢–FVçF–f–W'2Ò¶VF—Bæ–FVçF–f–W"f÷"VF—B–âVF—G5Ð¢–bÆVâ†–FVçF–f–W'2’ÒÆVâ‡6WB†–FVçF–f–W'2’“ ¢&—6R'VçF–ÖTW'&÷"‚&6ö×÷6VBVF—B”G2&Ræ÷BVæ—VR" ¢6æF–FFRÂVF—EöVF—BÂ6¶VÆWFöâÒÇ•öVF—G2‡6÷W&6RÂVF—G2ÂfÆ–FF÷"¢gFW%÷&÷w2ÒfÆ–FF÷"æFV6Æ&F–öç2†6æF–FFR¢gFW%ö–FVçF—G’ÒfÆ–FF÷"ç6÷W&6U÷7FF–5ö–FVçF—G’†6æF–FFRÂgFW%÷&÷w2¢–b·&÷u²&æÖR%Òf÷"&÷r–â6÷W&6U÷&÷w5ÒÒ·&÷u²&æÖR%Òf÷"&÷r–âgFW%÷&÷w5Ó ¢&—6R'VçF–ÖTW'&÷"‚&FV6Æ&F–öâ6WVVæ6R6†ævVB"¢–b·&÷u²&†VFW%÷6†#Sb%Òf÷"&÷r–â6÷W&6U÷&÷w5ÒÒ°¢&÷u²&†VFW%÷6†#Sb%Òf÷"&÷r–âgFW%÷&÷w0¢Ó ¢&—6R'VçF–ÖTW'&÷"‚&öæR÷"Ö÷&RFV6Æ&F–öâ†VFW'2ö6Æ–×26†ævVB"¢–bfÆ–FF÷"æ6öÖÖVçEöÆW†VÖW2‡6÷W&6R’ÒfÆ–FF÷"æ6öÖÖVçEöÆW†VÖW2†6æF–FFR“ ¢&—6R'VçF–ÖTW'&÷"‚&Fö7VÖVçFF–öâö6öÖÖVçBÆW†VÖW26†ævVB"¢–bfÆ–FF÷"æGG&–'WFUöÆW†VÖW2‡6÷W&6R’ÒfÆ–FF÷"æGG&–'WFUöÆW†VÖW2†6æF–FFR“ ¢&—6R'VçF–ÖTW'&÷"‚&W†—7F–ær¶GG&–'WFUÒÆW†VÖW26†ævVB"¢6öFUö&Vf÷&RÒfÆ–FF÷"æf÷&&–FFVåö6öFUö6÷VçG2‡6÷W&6R¢6öFUögFW"ÒfÆ–FF÷"æf÷&&–FFVåö6öFUö6÷VçG2†6æF–FFR¢¦W&òÒ¶æÖS¢f÷"æÖR–âfÆ–FF÷"ädõ$$”DDTçÐ¢–b6öFUö&Vf÷&RÒ¦W&ò÷"6öFUögFW"Ò¦W&ó ¢&—6R'VçF–ÖTW'&÷"€¢b&W†V7WF&ÆRf÷&&–FFVâ×6—‚æöç¦W&ó¢&Vf÷&S×¶6öFUö&Vf÷&WÒÂgFW#×¶6öFUögFW'Ò ¢¢&uö&Vf÷&RÒfÆ–FF÷"ç&uöf÷&&–FFVåö6÷VçG2‡6÷W&6R¢&uögFW"ÒfÆ–FF÷"ç&uöf÷&&–FFVåö6÷VçG2†6æF–FFR¢–b&uö&Vf÷&RÒ&uögFW# ¢&—6R'VçF–ÖTW'&÷"‚'&ræöâÖ6öFRf÷&&–FFVâÖVçF–öâÆVFvW"6†ævVB" ¢Æö6ÅöGG&–'WFUö&Vf÷&RÒ6÷W&6Ræ6÷VçB‚&GG&–'WFR¶Æö6Â–ç7Fæ6UÒ"¢Æö6ÅöGG&–'WFUögFW"Ò6æF–FFRæ6÷VçB‚&GG&–'WFR¶Æö6Â–ç7Fæ6UÒ"¢–bÆö6ÅöGG&–'WFUögFW"ÒÆö6ÅöGG&–'WFUö&Vf÷&R² ¢&—6R'VçF–ÖTW'&÷"‚&WF†÷&—¦VBÆö6ÂÖ–ç7Fæ6R6öÖÖæBFVÇF—2æ÷BW†7FÇ’öæR"¢gVÆÇ•÷VÆ–f–VEö–ç7Fæ6RÒ€¢&GG&–'WFR¶Æö6Â–ç7Fæ6UÕÆâ ¢"Öö6³$dåW$6÷'&V7F–öç2äWFöÖ÷'†–56ö&öÆWbäFVf–æ—F–öäöæU6ö&öÆWbâ ¢$f—†VE†6Tw&„6ö×ÆWF–öâæf—†VE†6Tw&„6÷&TÖöGVÆUÆâ ¢"Öö6³$dåW$6÷'&V7F–öç2äWFöÖ÷'†–56ö&öÆWbäFVf–æ—F–öäöæU6ö&öÆWbâ ¢$f—†VE†6Tw&„6ö×ÆWF–öâæf—†VE†6Tw&„6÷&TFD6öÖÔw&÷W ¢¢–b6÷W&6Ræ6÷VçB†gVÆÇ•÷VÆ–f–VEö–ç7Fæ6R’Ò÷"6æF–FFRæ6÷VçB†gVÆÇ•÷VÆ–f–VEö–ç7Fæ6R’Ò ¢&—6R'VçF–ÖTW'&÷"‚&vÆö&Â6æöæ–6Â–ç7Fæ6R&Vv—7G&F–öâ6&F–æÆ—G’G&–gB"¢–b6æF–FFRæ6÷VçB„Äô4Åô”å5Dä4Uô$Äô4²æÇ7G&—‚%Æâ"’’Ò ¢&—6R'VçF–ÖTW'&÷"‚&GWÆ–6FRæÖW76RÖÆö6Â6æöæ–6Â–ç7Fæ6R&Vv—7G&F–öâ&VÖ–ç2"¢6ÆÕö÷Våö&Vf÷&RÒ6÷W&6Ræ6÷VçB‚&÷Vâ6öçF–çV÷W4Æ–æV$Ö"¢6ÆÕö÷VåögFW"Ò6æF–FFRæ6÷VçB‚&÷Vâ6öçF–çV÷W4Æ–æV$Ö"¢–b6ÆÕö÷VåögFW"Ò6ÆÕö÷Våö&Vf÷&R²c ¢&—6R'VçF–ÖTW'&÷"‚&æÖW76RÖ&÷VæFVB6öçF–çV÷W4Æ–æV$Ö÷VâFVÇF—2æ÷B6—‚" ¢6†ævVEö–æF–6W2Ò°¢–æFW€¢f÷"–æFW‚Â†&Vf÷&RÂgFW"’–âVçVÖW&FR‡¦—‡6÷W&6U÷&÷w2ÂgFW%÷&÷w2Â7G&–7CÕG'VR’¢–b&Vf÷&U²'&Vv–öå÷6†#Sb%ÒÒgFW%²'&Vv–öå÷6†#Sb%Ð¢Ð¢6æF–FFUö–FVçF—G’Ò°¢'6†#Sb#¢6†#Se÷FW‡B†6æF–FFR’À¢&'—FW2#¢ÆVâ†6æF–FFRæVæ6öFR‚'WFbÓ‚"’’À¢&Æ–æW2#¢ÆVâ†6æF–FFRç7Æ—FÆ–æW2‚’’À¢&FV6Æ&F–öåö6÷VçB#¢ÆVâ†gFW%÷&÷w2’À¢&FV6Æ&F–öå÷6WVVæ6U÷6†#Sb#¢6†#Se÷FW‡B€¢%Æâ"æ¦ö–â‡&÷u²&æÖR%Òf÷"&÷r–âgFW%÷&÷w2¢’À¢Ð¢W‡V7FVEö6æF–FFRÒ°¢'6†#Sb#¢&WV—&U÷6†cEöVçb‚$dôeTÄÅôU…T5DTEõ4„#Sb"’À¢&'—FW2#¢&WV—&UöFV6–ÖÅöVçb‚$dôeTÄÅôU…T5DTEô%•DU2"’À¢&Æ–æW2#¢&WV—&UöFV6–ÖÅöVçb‚$dôeTÄÅôU…T5DTEôÄ”äU2"’À¢Ð¢f÷"¶W’ÂfÇVR–âW‡V7FVEö6æF–FFRæ—FV×2‚“ ¢–b6æF–FFUö–FVçF—G•¶¶W•ÒÒfÇVS ¢&—6R'VçF–ÖTW'&÷"€¢b&7V×VÆF—fR6æF–FFR¶¶W—Ò¶6æF–FFUö–FVçF—G•¶¶W•Ò'Ó²W‡V7FVB·fÇVR'Ò ¢ ¢VF—BÒ°¢'66†VÖ#¢&fÖgVÆÂÖ7V×VÆF—fR×&W&F–öâ×c"À¢&ÆÅö6†V6·5÷76VB#¢G'VRÀ¢'7FGW2#¢%5DD”4ÄÅ•ôÔDU$”Ä•¤TEõTäD”äuôD•$T5EôÄTâ"À¢'6÷W&6R#¢6÷W&6Uö–FVçF—G’À¢&6æF–FFR#¢6æF–FFUö–FVçF—G’À¢&–çfVçF÷'•öWF†÷&—G’#¢°¢'6†#Sb#¢”ådTåDõ%•õ4„#SbÀ¢'7VÖÖ'’#¢U…T5DTEô”ådTåDõ%•õ5TÔÔ%’À¢&6ö×ÆWFUöæõö6#¢G'VRÀ¢&6÷'&V7FVEö÷F–öæÅö6öFUö6öÆÆV7F÷"#¢G'VRÀ¢ÒÀ¢&Æ–'&&–W2#¢°¢&V&Ç’#¢T$Å•ôÄ”%$%•õ4„#SbÀ¢'6VÆV7FVEöVçf—&öæÖVçB#¢4TÄT5DTEôTåd•$ôäÔTåEôÄ”%$%•õ4„#SbÀ¢&vÆö&Åö–ç7Fæ6R#¢tÄô$Åô”å5Dä4UôÄ”%$%•õ4„#SbÀ¢&f–ç&æµ÷&VÅö6ö×ÆW‚#¢d”å$äµôÄ”%$%•õ4„#SbÀ¢'7WÆVÖVçFÅö–æFW‚#¢&WV—&U÷6†cEöVçb€¢$dôeTÄÅõ5UÄTÔTåDÅô”äDU…õ4„#Sb ¢’À¢'7WÆVÖVçFÅöÆ–'&&–W2#¢7WÆVÖVçFÅöVF—BÀ¢&ÆFR#¢&WV—&U÷6†cEöVçb‚$dôeTÄÅôÄDUôÄ”%$%•õ4„#Sb"’À¢&ÆFUöf÷&&–FFVåö†VFW%öVF—Eö–G2#¢6÷'FVB€¢dõ$$”DDTåôÄDUô„TDU%ôTD•Eô”E0¢’À¢ÒÀ¢&6ö×÷6—F–öâ#¢6ö×÷6—F–öâÀ¢'7WW'6VFVEög&vÖVçG2#¢7WW'6VFVBÀ¢&FVGWÆ–6FVEöÆFUöÆ—FW&ÅöÆÅög&vÖVçG2#¢FVGWöVF—BÀ¢&FVGWÆ–6FVEö'•ö&÷VæFVEö6öçF–çV÷W5öÆ–æV%öÖö÷fW&Æ’#¢€¢&÷VæFVEöFVGWöVF—@¢’À¢&VF—Eö6÷VçB#¢ÆVâ†VF—G2’À¢&VF—EöVF—B#¢VF—EöVF—BÀ¢&6†ævVEöFV6Æ&F–öå÷&Vv–öåö–æF–6W2#¢6†ævVEö–æF–6W2À¢&6†ævVEöFV6Æ&F–öå÷&Vv–öåöæÖW2#¢·6÷W&6U÷&÷w5¶•Õ²&æÖR%Òf÷"’–â6†ævVEö–æF–6W5ÒÀ¢&–Ö×WF&ÆUöÖ&¶W%÷6¶VÆWFöå÷6†#Sb#¢6†#Se÷FW‡B‡6¶VÆWFöâ’À¢&–Ö×WF&ÆUöÖ&¶W%÷6¶VÆWFöåö'—FW2#¢ÆVâ‡6¶VÆWFöâæVæ6öFR‚'WFbÓ‚"’’À¢&–Ö×WF&ÆUöÖ&¶W%÷6¶VÆWFöå÷&W6W'fVB#¢G'VRÀ¢&FV6Æ&F–öå÷6WVVæ6U÷&W6W'fVB#¢G'VRÀ¢&ÆÅöFV6Æ&F–öåö†VFW'5öæEö6Æ–×5÷&W6W'fVB#¢G'VRÀ¢&ÆÅöW†—7F–æuöFö7VÖVçFF–öåö6öÖÖVçG5÷&W6W'fVB#¢G'VRÀ¢&ÆÅöW†—7F–æuöEöGG&–'WFW5÷&W6W'fVB#¢G'VRÀ¢&WF†÷&—¦VEöÆö6Åö–ç7Fæ6Uö6öÖÖæEöFVÇF#¢À¢&vÆö&Åö6æöæ–6Åö–ç7Fæ6U÷&Vv—7G&F–öåö6÷VçB#¢À¢&GWÆ–6FUöæÖW76UöÆö6Åö–ç7Fæ6U÷&Vv—7G&F–öåö6÷VçB#¢À¢'6÷W&6UövÆö&Åö6öçF–çV÷W5öÆ–æV%öÖö÷Våö–çG&öGV6VB#¢fÇ6RÀ¢&æÖW76Uö&÷VæFVEö6öçF–çV÷W5öÆ–æV%öÖö÷VåöFVÇF#¢bÀ¢'&uöf÷&&–FFVåöÖVçF–öç5ö&Vf÷&R#¢&uö&Vf÷&RÀ¢'&uöf÷&&–FFVåöÖVçF–öç5ögFW"#¢&uögFW"À¢'&uöÖVçF–öç5ö&Uöæöåö6öFUöÆVFvW%ööæÇ’#¢G'VRÀ¢&W†V7WF&ÆUöf÷&&–FFVåö6÷VçG5ö&Vf÷&R#¢6öFUö&Vf÷&RÀ¢&W†V7WF&ÆUöf÷&&–FFVåö6÷VçG5ögFW"#¢6öFUögFW"À¢&W†V7WF&ÆUöf÷&&–FFVå÷6—…÷¦W&ò#¢G'VRÀ¢&F—&V7EöÆVå÷fW&–f–VB#¢fÇ6RÀ¢&ÆVåöW†V7WFVEö'•÷&W&W"#¢fÇ6RÀ¢&Æ¶UöW†V7WFVEö'•÷&W&W"#¢fÇ6RÀ¢&v—EöW†V7WFVEö'•÷&W&W"#¢fÇ6RÀ¢&v—F‡V%÷w&—GFVåö'•÷&W&W"#¢fÇ6RÀ¢Ð¢&WGW&â6æF–FFRÂVF—@  ¦FVb'6W"‚’Óâ&w'6Rä&wVÖVçE'6W# ¢&W7VÇBÒ&w'6Rä&wVÖVçE'6W"†FW67&—F–öãÕõöFö5õò¢&W7VÇBæFEö&wVÖVçB‚"ÒÖ&6R×6÷W&6R"ÂG—SÕF‚Â&WV—&VCÕG'VR¢&W7VÇBæFEö&wVÖVçB‚"Ò×F&vWB"ÂG—SÕF‚Â&WV—&VCÕG'VR¢&W7VÇBæFEö&wVÖVçB‚"ÒÖVF—BÖ÷WB"ÂG—SÕF‚Â&WV—&VCÕG'VR¢&W7VÇBæFEö&wVÖVçB€¢"Ò×fÆ–FF÷""ÂG—SÕF‚ÂFVfVÇCÕF‚‚'67&—G2öfögVÆÅö6ö×–ÆUö–çfVçF÷'’ç’"¢¢&W7VÇBæFEö&wVÖVçB€¢"ÒÖ–çfVçF÷'’"ÂG—SÕF‚ÂFVfVÇCÕF‚‚'67&—G2öfögVÆÅö6ö×–ÆUöW'&÷%ö–çfVçF÷'’æ§6öâ"¢¢&W7VÇBæFEö&wVÖVçB€¢"ÒÖV&Ç’ÖÆ–'&'’"À¢G—SÕF‚À¢FVfVÇCÕF‚‚'67&—G2öfögVÆÅö6ö×–ÆUö6öÖ&–æVEö¶æ÷våö÷fW'&–FW2æ§6öâ"’À¢¢&W7VÇBæFEö&wVÖVçB€¢"Ò×6VÆV7FVBÖVçf—&öæÖVçBÖÆ–'&'’"À¢G—SÕF‚À¢FVfVÇCÕF‚‚'67&—G2öföC5ö–Gƒ#“sEó3%ögVÆÅö–çfVçF÷'•övFVEö÷fW'&–FW2æ§6öâ"’À¢¢&W7VÇBæFEö&wVÖVçB€¢"ÒÖvÆö&ÂÖ–ç7Fæ6RÖÆ–'&'’"À¢G—SÕF‚À¢FVfVÇCÕF‚‚'67&—G2öfögVÆÅö6ö×–ÆUövÆö&Åö6÷&Uö–ç7Fæ6UöVçf—&öæÖVçEö÷fW'&–FRæ§6öâ"’À¢¢&W7VÇBæFEö&wVÖVçB€¢"ÒÖÆFRÖÆ–'&'’"À¢G—SÕF‚À¢FVfVÇCÕF‚‚'67&—G2öföC5÷#5÷#EöÆFU÷&ö÷EöÆ–'&'’æ§6öâ"’À¢¢&W7VÇBæFEö&wVÖVçB€¢"ÒÖf–ç&æ²ÖÆ–'&'’"À¢G—SÕF‚À¢FVfVÇCÕF‚‚'67&—G2öfögVÆÅö6ö×–ÆUöf–ç&æµ÷&VÅö6ö×ÆW…ö÷fW'&–FW2æ§6öâ"’À¢¢&W7VÇBæFEö&wVÖVçB€¢"Ò×7WÆVÖVçFÂÖ–æFW‚"À¢G—SÕF‚À¢FVfVÇCÕF‚‚'67&—G2öfögVÆÅö7V×VÆF—fU÷7FæF&EöÆ–'&'•ö–æFW‚æ§6öâ"’À¢¢&W7VÇBæFEö&wVÖVçB€¢"ÒÖGFW7FF–öâ"À¢G—SÕF‚À¢FVfVÇCÕF‚‚"÷F×öfÖgVÆÂÖ&6RÖ'F–f7BÖGFW7FF–öâæ§6öâ"’À¢¢&WGW&â&W7VÇ@  ¦FVbÖ–â‚’Óâ–çC ¢&w2Ò'6W"‚’ç'6Uö&w2‚¢G'“ ¢fÆ–FF÷"ÒÆöE÷fÆ–FF÷"†&w2çfÆ–FF÷"¢–çfVçF÷'’ÒÆöEö§6öåöÆö6¶VB†&w2æ–çfVçF÷'’Â”ådTåDõ%•õ4„#SbÂ&gVÆÂ–çfVçF÷'’"¢V&Ç’ÒÆöEö§6öåöÆö6¶VB†&w2æV&Ç•öÆ–'&'’ÂT$Å•ôÄ”%$%•õ4„#SbÂ&V&Ç’Æ–'&'’"¢6VÆV7FVBÒÆöEö§6öåöÆö6¶VB€¢&w2ç6VÆV7FVEöVçf—&öæÖVçEöÆ–'&'’À¢4TÄT5DTEôTåd•$ôäÔTåEôÄ”%$%•õ4„#SbÀ¢'6VÆV7FVBVçf—&öæÖVçBÆ–'&'’"À¢¢vÆö&Åö–ç7Fæ6RÒÆöEö§6öåöÆö6¶VB€¢&w2ævÆö&Åö–ç7Fæ6UöÆ–'&'’À¢tÄô$Åô”å5Dä4UôÄ”%$%•õ4„#SbÀ¢&vÆö&Â–ç7Fæ6RÆ–'&'’"À¢¢f–ç&æ²ÒÆöEö§6öåöÆö6¶VB€¢&w2æf–ç&æµöÆ–'&'’À¢d”å$äµôÄ”%$%•õ4„#SbÀ¢&f–ç&æ²&VÂö6ö×ÆW‚’Æ–'&'’"À¢¢7WÆVÖVçFÅö–æFW…÷6†Ò&WV—&U÷6†cEöVçb€¢$dôeTÄÅõ5UÄTÔTåDÅô”äDU…õ4„#Sb ¢¢7WÆVÖVçFÅö–æFW‚ÒÆöEö§6öåöÆö6¶VB€¢&w2ç7WÆVÖVçFÅö–æFW‚À¢7WÆVÖVçFÅö–æFW…÷6†À¢'7WÆVÖVçFÂ7FæF&BÆ–'&'’–æFW‚"À¢¢ÆFU÷6†Ò&WV—&U÷6†cEöVçb‚$dôeTÄÅôÄDUôÄ”%$%•õ4„#Sb"¢ÆFRÒÆöEö§6öåöÆö6¶VB†&w2æÆFUöÆ–'&'’ÂÆFU÷6†Â&ÆFR&ö÷BÆ–'&'’" ¢&6U÷FW‡BÒFV6öFUöÆb†&w2æ&6U÷6÷W&6R¢fÆ–FFUöGFW7FF–öâ†&w2æGFW7FF–öâÂ&w2æ&6U÷6÷W&6R¢fÆ–FFU÷6÷W&6Uö–FVçF—G’†&6U÷FW‡BÂfÆ–FF÷" ¢–bæ÷B&w2çF&vWBæ—5öf–ÆR‚’÷"&w2çF&vWBæ—5÷7–ÖÆ–æ²‚“ ¢&—6R'VçF–ÖTW'&÷"‚&6†V6¶VBÖ÷WBF&vWB×W7B&RöæR÷&F–æ'’W†—7F–ærf–ÆR"¢F&vWEö&Vf÷&RÒ&w2çF&vWBç&VEö'—FW2‚¢F&vWEö&Vf÷&U÷6†Ò6†#Seö'—FW2‡F&vWEö&Vf÷&R¢–bF&vWEö&Vf÷&U÷6†Ò4„T4´TEôõUEõ4õU$4Uõ4„#Sc ¢&—6R'VçF–ÖTW'&÷"€¢b&6†V6¶VBÖ÷WB6÷W&6R4„G&–gC¢·F&vWEö&Vf÷&U÷6†Ó² ¢b&W‡V7FVB´4„T4´TEôõUEõ4õU$4Uõ4„#SgÒ ¢¢6æF–FFRÂVF—BÒ'V–ÆEö6æF–FFR€¢&6U÷FW‡BÀ¢fÆ–FF÷"À¢–çfVçF÷'’À¢V&Ç’À¢6VÆV7FVBÀ¢vÆö&Åö–ç7Fæ6RÀ¢f–ç&æ²À¢7WÆVÖVçFÅö–æFW‚À¢&w2ç7WÆVÖVçFÅö–æFW‚À¢ÆFRÀ¢¢VF—E²&&6Uö'F–f7EöGFW7FF–öå÷6†#Sb%ÒÒ&WV—&U÷6†cEöVçb€¢$dôeTÄÅô$4UôEDU5DD”ôåõ4„#Sb ¢¢VF—E²&6†V6¶VEö÷WE÷6÷W&6Uö&Vf÷&U÷6†#Sb%ÒÒF&vWEö&Vf÷&U÷6†¢VF—E²&6†V6¶VEö÷WE÷6÷W&6U÷&WV—&VE÷6†#Sb%ÒÒ4„T4´TEôõUEõ4õU$4Uõ4„#S`¢VF—E²'F&vWE÷F‚%ÒÒ7G"†&w2çF&vWB ¢&w2çF&vWBçw&—FUö'—FW2†6æF–FFRæVæ6öFR‚'WFbÓ‚"’¢&w2æVF—Eö÷WBç&VçBæÖ¶F—"‡&VçG3ÕG'VRÂW†—7Eöö³ÕG'VR¢&w2æVF—Eö÷WBçw&—FUö'—FW2†§6öåö'—FW2†VF—B’¢&–çB†§6öâæGV×2†VF—BÂ–æFVçCÓ"Â6÷'Eö¶W—3ÕG'VR’¢&WGW&â ¢W†6WBW†6WF–öâ2W'&÷# ¢&–çB†b$dgVÆÂ7V×VÆF—fR&W&F–öâf–ÇW&S¢¶W'&÷'Ò"Âf–ÆS×7—2ç7FFW'"¢&WGW&âƒ`  ¦–bõöæÖUõòÓÒ%õöÖ–åõò# ¢7—2æW†—B†Ö–â‚’