#!/usr/bin/env python3
"""Build a fail-closed, declaration-indexed inventory from a full Lean FA run.

This script is intentionally independent of Lean and Lake.  It consumes the
source, direct Lean log, and METRIC.json already captured in a GitHub Actions
artifact.  It never treats the diagnostic cap as proof progress and never
drops a diagnostic across declaration boundaries.

The inventory command emits two JSON files:

* every actual error, with exact source ownership and conservative cascade
  classification; and
* a fragment-only cumulative repair-manifest skeleton, one entry per affected
  declaration.

The validate-manifest command applies only explicitly hydrated, globally
unique fragments and statically proves the declaration sequence, headers,
comments, attributes, non-target skeleton, and executable forbidden-six gate.
It does not invoke Lean, Lake, git, or GitHub.
"""

from __future__ import annotations

import argparse
import bisect
import hashlib
import json
import os
import re
import sys
import tempfile
import zipfile
from pathlib import Path
from typing import Any, Iterable


INVENTORY_SCHEMA = "fa-full-compile-error-inventory-v1"
MANIFEST_SCHEMA = "fa-cumulative-fragment-repair-manifest-v1"
VALIDATION_SCHEMA = "fa-cumulative-fragment-validation-v1"
SOURCE_BASENAME = "Mock2_FunctionalAnalysis.lean"
LOG_BASENAME = "Mock2_FunctionalAnalysis.log"
METRIC_BASENAME = "METRIC.json"
FULL_DIAGNOSTICS_BASENAME = "FULL_DIAGNOSTICS.json"
DEFAULT_EXPECTED_MAX_ERRORS = 2_000
EXPECTED_SOURCE_SHA256 = (
    "d0a3decee1c0a7a781d14fdf122e235d71d8f210bb65a894dc4e518821bf03ec"
)
EXPECTED_SOURCE_BYTES = 2_702_252
EXPECTED_SOURCE_LINES = 60_573
EXPECTED_DECLARATION_COUNT = 4_397
EXPECTED_DECLARATION_SEQUENCE_SHA256 = (
    "a33d2a1e132e47c9c6b31924ed1b8a04a50de709ed2149a9f9abfb0b052b25eb"
)

# This is the exact 4,397-declaration lexical authority used by FA465/FA507.
# Deliberately do not broaden it with `local` or multiple modifiers.
DECL_START = re.compile(
    r"(?m)^(?:protected\s+|private\s+|noncomputable\s+)?"
    r"(?:theorem|lemma|def|abbrev|instance|structure|class)\s+"
    r"(?P<name>[^\s(:]+)"
)

DIAGNOSTIC_HEADER = re.compile(
    r"(?m)^(?P<path>[^\r\n]*?\.lean):(?P<line>[0-9]+):"
    r"(?P<column>[0-9]+): (?P<severity>error|warning|info|information)"
    r"(?:\((?P<diagnostic_code>[^)]+)\))?:[ \t]?"
    r"(?P<first_line>[^\r\n]*)"
)

FORBIDDEN = {
    "sorry": re.compile(r"\bsorry\b"),
    "admit": re.compile(r"\badmit\b"),
    "new_global_axiom": re.compile(r"(?m)^\s*axiom\b"),
    "unsafe": re.compile(r"\bunsafe\b"),
    "native_decide": re.compile(r"\bnative_decide\b"),
    "Lean.ofReduceBool": re.compile(r"\bLean\.ofReduceBool\b"),
}

CAP_RE = re.compile(
    r"maximum number of errors \((?P<cap>[0-9]+); from option `maxErrors`\)"
)
METAVAR_RE = re.compile(r"\?(?:m|u)\.[0-9]+")
ANON_GOAL_RE = re.compile(r"(?:case|this|h|a|x|y|z)[â€ âœ]+")


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_text(text: str) -> str:
    return sha256_bytes(text.encode("utf-8"))


def canonical_json_bytes(payload: Any) -> bytes:
    return (
        json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":"))
        + "\n"
    ).encode("utf-8")


def json_bytes(payload: Any) -> bytes:
    return (json.dumps(payload, ensure_ascii=False, indent=2, sort_keys=True) + "\n").encode(
        "utf-8"
    )


def decode_utf8_lf(data: bytes, label: str) -> str:
    try:
        text = data.decode("utf-8")
    except UnicodeDecodeError as error:
        raise RuntimeError(f"{label} is not UTF-8: {error}") from error
    if "\r" in text:
        raise RuntimeError(f"{label} is not canonical Linux/LF text")
    return text


def decode_utf8_json_whitespace(data: bytes, label: str) -> tuple[str, str]:
    """Decode JSON while recording and normalizing an all-CRLF sidecar.

    Source and Lean logs remain byte-authoritative LF-only inputs.  A corrected
    collector sidecar may be regenerated on Windows, where JSON indentation
    whitespace is CRLF.  Accept only uniform CRLF (never lone CR or mixed
    newline styles), normalize it solely for JSON parsing, and expose the
    original style in artifact metadata.
    """

    try:
        text = data.decode("utf-8")
    except UnicodeDecodeError as error:
        raise RuntimeError(f"{label} is not UTF-8: {error}") from error
    if "\r" not in text:
        return text, "LF"
    if text.replace("\r\n", "").find("\r") >= 0:
        raise RuntimeError(f"{label} contains a lone CR")
    if text.count("\r\n") != text.count("\n"):
        raise RuntimeError(f"{label} has mixed LF/CRLF newlines")
    return text.replace("\r\n", "\n"), "CRLF_NORMALIZED_FOR_JSON_ONLY"


class ArtifactReader:
    """Read artifact members without mutating the artifact."""

    def __init__(self, artifact: Path):
        self.artifact = artifact.resolve()
        if self.artifact.is_dir():
            self.kind = "directory"
            self._members = {
                path.relative_to(self.artifact).as_posix(): path
                for path in self.artifact.rglob("*")
                if path.is_file()
            }
            self._zip: zipfile.ZipFile | None = None
        elif self.artifact.is_file() and zipfile.is_zipfile(self.artifact):
            self.kind = "zip"
            self._zip = zipfile.ZipFile(self.artifact)
            self._members = {
                name: name for name in self._zip.namelist() if not name.endswith("/")
            }
        else:
            raise RuntimeError(f"artifact is neither a directory nor a zip: {artifact}")
        if not self._members:
            raise RuntimeError("artifact contains no files")

    @property
    def names(self) -> list[str]:
        return sorted(self._members)

    def read(self, name: str) -> bytes:
        member = self._members[name]
        if self.kind == "directory":
            assert isinstance(member, Path)
            return member.read_bytes()
        assert self._zip is not None and isinstance(member, str)
        return self._zip.read(member)

    def select(
        self,
        label: str,
        explicit: str | None,
        predicate,
        *,
        allow_identical_duplicates: bool = True,
    ) -> tuple[str, bytes, list[str]]:
        if explicit:
            exact = [name for name in self.names if name == explicit]
            suffix = [name for name in self.names if name.endswith(explicit)]
            hits = exact or suffix
        else:
            hits = [name for name in self.names if predicate(name)]
        if not hits:
            raise RuntimeError(f"artifact has no {label}; members={len(self.names)}")
        payloads = [(name, self.read(name)) for name in hits]
        identities = {sha256_bytes(data) for _name, data in payloads}
        if len(payloads) > 1 and (not allow_identical_duplicates or len(identities) != 1):
            raise RuntimeError(
                f"artifact has ambiguous {label} members: {[name for name, _ in payloads]}"
            )
        payloads.sort(key=lambda item: (item[0].count("/"), len(item[0]), item[0]))
        selected_name, selected_data = payloads[0]
        return selected_name, selected_data, [name for name, _data in payloads]

    def close(self) -> None:
        if self._zip is not None:
            self._zip.close()


def line_start_offsets(text: str) -> list[int]:
    offsets = [0]
    offsets.extend(match.end() for match in re.finditer("\n", text))
    return offsets


def offset_line(offsets: list[int], offset: int) -> int:
    return bisect.bisect_right(offsets, offset)


def declarations(text: str) -> list[dict[str, Any]]:
    offsets = line_start_offsets(text)
    starts = list(DECL_START.finditer(text))
    rows: list[dict[str, Any]] = []
    for index, match in enumerate(starts):
        start = match.start()
        end = starts[index + 1].start() if index + 1 < len(starts) else len(text)
        region = text[start:end]
        marker = region.find(":=")
        header = region[: marker + 2] if marker >= 0 else None
        rows.append(
            {
                "index": index,
                "name": match.group("name"),
                "start_offset": start,
                "end_offset": end,
                "start_line": offset_line(offsets, start),
                "end_line": offset_line(offsets, max(start, end - 1)),
                "region_sha256": sha256_text(region),
                "region_bytes": len(region.encode("utf-8")),
                "header_sha256": sha256_text(header) if header is not None else None,
                "header_bytes": len(header.encode("utf-8")) if header is not None else None,
                "has_colon_equals_header": header is not None,
            }
        )
    return rows


def owner_for_line(
    declaration_rows: list[dict[str, Any]], line: int
) -> dict[str, Any] | None:
    start_lines = [row["start_line"] for row in declaration_rows]
    index = bisect.bisect_right(start_lines, line) - 1
    if index < 0:
        return None
    owner = declaration_rows[index]
    if line > owner["end_line"]:
        return None
    return owner


def normalize_message(message: str) -> str:
    normalized = METAVAR_RE.sub("?META", message)
    normalized = ANON_GOAL_RE.sub("ANON_GOAL", normalized)
    normalized = re.sub(r"[ \t]+", " ", normalized)
    normalized = re.sub(r"\n{3,}", "\n\n", normalized)
    return normalized.strip()


def diagnostic_category(message: str) -> str:
    lowered = message.lower()
    if CAP_RE.search(message):
        return "diagnostic_cap_sentinel"
    if "maximum number of heartbeats" in lowered or "deterministic) timeout" in lowered:
        return "resource_limit"
    if lowered.startswith("type mismatch"):
        return "type_mismatch"
    if lowered.startswith("application type mismatch"):
        return "application_type_mismatch"
    if "tactic `rewrite` failed" in lowered or "rewrite tactic failed" in lowered:
        return "rewrite_pattern_miss"
    if lowered.startswith("unsolved goals") or "\nunsolved goals" in lowered:
        return "unsolved_goals"
    if lowered.startswith("no goals to be solved"):
        return "no_goals_to_be_solved"
    if "linarith failed" in lowered:
        return "arithmetic_tactic_failure"
    if "typeclass instance problem is stuck" in lowered:
        return "stuck_typeclass"
    if "failed to synthesize" in lowered:
        return "typeclass_synthesis"
    if lowered.startswith("unknown identifier"):
        return "unknown_identifier"
    if "unexpected token" in lowered or "unexpected end of input" in lowered:
        return "syntax_recovery"
    if "declaration has metavariables" in lowered:
        return "unresolved_metavariables"
    return "other"


def parse_diagnostics(log: str, source_basename: str) -> tuple[list[dict[str, Any]], int]:
    headers = list(DIAGNOSTIC_HEADER.finditer(log))
    errors: list[dict[str, Any]] = []
    for position, match in enumerate(headers):
        if match.group("severity") != "error":
            continue
        if Path(match.group("path")).name != source_basename:
            continue
        end = headers[position + 1].start() if position + 1 < len(headers) else len(log)
        continuation = log[match.end() : end]
        if continuation.startswith("\n"):
            continuation = continuation[1:]
        message = match.group("first_line")
        if continuation:
            message += "\n" + continuation.rstrip("\n")
        message = message.rstrip()
        cap_match = CAP_RE.search(message)
        errors.append(
            {
                "id": f"E{len(errors) + 1:04d}",
                "path": match.group("path"),
                "line": int(match.group("line")),
                "column": int(match.group("column")),
                "diagnostic_code": match.group("diagnostic_code"),
                "message": message,
                "message_sha256": sha256_text(message),
                "normalized_message_sha256": sha256_text(normalize_message(message)),
                "category": diagnostic_category(message),
                "is_cap_sentinel": cap_match is not None,
                "reported_cap": int(cap_match.group("cap")) if cap_match else None,
            }
        )
    return errors, sum(1 for match in headers if match.group("severity") == "error")


def classify_cascades(errors: list[dict[str, Any]]) -> None:
    """Conservatively mark only high-confidence within-declaration cascades.

    Cross-declaration filtering is forbidden.  Multiple distinct goals in one
    theorem remain roots unless a deterministic rule below supplies the exact
    predecessor diagnostic.
    """

    history: dict[int | None, list[dict[str, Any]]] = {}
    for error in errors:
        error["classification"] = "root_candidate"
        error["cascade_rule"] = None
        error["cascade_parent_id"] = None
        if error["is_cap_sentinel"]:
            error["classification"] = "cap_sentinel"
            continue
        key = error["declaration_index"]
        prior = history.setdefault(key, [])
        same_fingerprint = next(
            (
                row
                for row in prior
                if row["normalized_message_sha256"]
                == error["normalized_message_sha256"]
            ),
            None,
        )
        same_position = next(
            (
                row
                for row in prior
                if row["line"] == error["line"] and row["column"] == error["column"]
            ),
            None,
        )
        syntax_parent = next(
            (
                row
                for row in prior
                if row["category"] in {"syntax_recovery", "unknown_identifier"}
            ),
            None,
        )
        if same_fingerprint is not None:
            error["classification"] = "suspected_cascade"
            error["cascade_rule"] = "duplicate_normalized_message_same_declaration"
            error["cascade_parent_id"] = same_fingerprint["id"]
        elif same_position is not None:
            error["classification"] = "suspected_cascade"
            error["cascade_rule"] = "same_source_position_after_prior_error"
            error["cascade_parent_id"] = same_position["id"]
        elif error["category"] == "no_goals_to_be_solved" and prior:
            error["classification"] = "suspected_cascade"
            error["cascade_rule"] = "no_goals_after_prior_error_same_declaration"
            error["cascade_parent_id"] = prior[-1]["id"]
        elif syntax_parent is not None:
            error["classification"] = "suspected_cascade"
            error["cascade_rule"] = "parser_or_unknown_identifier_recovery_same_declaration"
            error["cascade_parent_id"] = syntax_parent["id"]
        elif error["category"] == "resource_limit":
            error["classification"] = "resource_limit_root"
        prior.append(error)


def metric_lookup(metric: dict[str, Any]×N:êÚ$z{-®éÜj×ÆÆ÷uö–FVçF–6ÅöGWÆ–6FW3ÔfÇ6RÀ¢¢W†6WB'VçF–ÖTW'&÷# ¢–bæ÷B&w2æÆÆ÷uöÖ—76–æuö6öÆÆV7F÷# ¢&—6P¢f–æÆÇ“ ¢&VFW"æ6Æ÷6R‚¢6÷W&6U÷FW‡BÒFV6öFU÷WFc…öÆb‡6÷W&6UöFFÂ6÷W&6UöæÖR¢Æöu÷FW‡BÒFV6öFU÷WFc…öÆb†ÆöuöFFÂÆöuöæÖR¢G'“ ¢ÖWG&–2Ò§6öâæÆöG2†FV6öFU÷WFc…öÆb†ÖWG&–5öFFÂÖWG&–5öæÖR’¢W†6WB§6öâä¥4ôäFV6öFTW'&÷"2W'&÷# ¢&—6R'VçF–ÖTW'&÷"†b&–çfÆ–BÔUE$”2æ§6öã¢¶W'&÷'Ò"’g&öÒW'&÷ ¢6öÆÆV7F÷#¢F–7E·7G"Âç•ÒÂæöæRÒæöæP¢6öÆÆV7F÷%öæWvÆ–æU÷7G–ÆS¢7G"ÂæöæRÒæöæP¢–b6öÆÆV7F÷%öæÖR—2æ÷BæöæRæB6öÆÆV7F÷%öFF—2æ÷BæöæS ¢G'“ ¢6öÆÆV7F÷%÷FW‡BÂ6öÆÆV7F÷%öæWvÆ–æU÷7G–ÆRÒFV6öFU÷WFc…ö§6öå÷v†—FW76R€¢6öÆÆV7F÷%öFFÂ6öÆÆV7F÷%öæÖP¢¢6öÆÆV7F÷"Ò§6öâæÆöG2†6öÆÆV7F÷%÷FW‡B¢W†6WB§6öâä¥4ôäFV6öFTW'&÷"2W'&÷# ¢&—6R'VçF–ÖTW'&÷"†b&–çfÆ–BeTÄÅôD”täõ5D”52æ§6öã¢¶W'&÷'Ò"’g&öÒW'&÷ ¢'F–f7E÷F‚ÒF‚†&w2æ'F–f7B’ç&W6öÇfR‚¢'F–f7Eö–æfòÒ°¢&–çWEö&6VæÖR#¢'F–f7E÷F‚ææÖRÀ¢&¶–æB#¢&F—&V7F÷'’"–b'F–f7E÷F‚æ—5öF—"‚’VÇ6R'¦—"À¢&&6†—fU÷6†#Sb#¢6†#Seö'—FW2†'F–f7E÷F‚ç&VEö'—FW2‚’¢–b'F–f7E÷F‚æ—5öf–ÆR‚¢VÇ6RæöæRÀ¢'6VÆV7FVE÷6÷W&6UöÖVÖ&W"#¢6÷W&6UöæÖRÀ¢'6VÆV7FVEöÆöuöÖVÖ&W"#¢ÆöuöæÖRÀ¢'6VÆV7FVEöÖWG&–5öÖVÖ&W"#¢ÖWG&–5öæÖRÀ¢'6VÆV7FVEögVÆÅöF–væ÷7F–75öÖVÖ&W"#¢6öÆÆV7F÷%öæÖRÀ¢'6VÆV7FVEögVÆÅöF–væ÷7F–75÷&u÷6†#Sb#¢6†#Seö'—FW2†6öÆÆV7F÷%öFF¢–b6öÆÆV7F÷%öFF—2æ÷BæöæP¢VÇ6RæöæRÀ¢'6VÆV7FVEögVÆÅöF–væ÷7F–75÷&uö'—FW2#¢ÆVâ†6öÆÆV7F÷%öFF¢–b6öÆÆV7F÷%öFF—2æ÷BæöæP¢VÇ6RæöæRÀ¢'6VÆV7FVEögVÆÅöF–væ÷7F–75öæWvÆ–æU÷7G–ÆR#¢6öÆÆV7F÷%öæWvÆ–æU÷7G–ÆRÀ¢&–FVçF–6Å÷6÷W&6UöÖVÖ&W'2#¢6÷W&6Uö†—G2À¢&–FVçF–6ÅöÆöuöÖVÖ&W'2#¢Æöuö†—G2À¢&ÖWG&–5öÖVÖ&W'2#¢ÖWG&–5ö†—G2À¢&gVÆÅöF–væ÷7F–75öÖVÖ&W'2#¢6öÆÆV7F÷%ö†—G2À¢Ğ¢&WGW&â6÷W&6U÷FW‡BÂÆöu÷FW‡BÂÖWG&–2Â6öÆÆV7F÷"Â'F–f7Eö–æfğ  ¦FVbFV6Æ&F–öå÷&Vv–öâ‡FW‡C¢7G"Â&÷w3¢Æ—7E¶F–7E·7G"Âç•ÕÒÂ–æFWƒ¢–çB’Óâ7G# ¢&÷rÒ&÷w5¶–æFW…Ğ¢&WGW&âFW‡E·&÷u²'7F'Eööfg6WB%Ò¢&÷u²&VæEööfg6WB%ÕĞ  ¦FVbfÆ–FFUög&vÖVçEöÖæ–fW7B€¢6÷W&6U÷FW‡C¢7G"ÂÖæ–fW7C¢F–7E·7G"Âç•Ğ¢’ÓâGWÆU·7G"ÂF–7E·7G"Âç•ÕÓ ¢–bÖæ–fW7BævWB‚'66†VÖ"’ÒÔä”dU5Eõ44„TÔ ¢&—6R'VçF–ÖTW'&÷"‚'&W—"Öæ–fW7B66†VÖÖ—6ÖF6‚"¢6÷W&6U÷&÷w2ÒFV6Æ&F–öç2‡6÷W&6U÷FW‡B¢6÷W&6Uö–FVçF—G’Ò6÷W&6U÷7FF–5ö–FVçF—G’‡6÷W&6U÷FW‡BÂ6÷W&6U÷&÷w2¢&WV—&VBÒÖæ–fW7BævWB‚'6÷W&6R"’÷"·Ğ¢f÷"f–VÆB–â€¢'6†#Sb"À¢&'—FW2"À¢&Æ–æW2"À¢&FV6Æ&F–öåö6÷VçB"À¢&FV6Æ&F–öå÷6WVVæ6U÷6†#Sb"À¢“ ¢–b&WV—&VBævWB†f–VÆB’Ò6÷W&6Uö–FVçF—G•¶f–VÆEÓ ¢&—6R'VçF–ÖTW'&÷"†b'&W—"Öæ–fW7B6÷W&6R¶f–VÆGÒÖ—6ÖF6‚"¢–bç’‡6÷W&6Uö–FVçF—G•²&W†V7WF&ÆUöf÷&&–FFVåö6÷VçG2%ÒçfÇVW2‚’“ ¢&—6R'VçF–ÖTW'&÷"‚&–çWBW†V7WF&ÆRf÷&&–FFVâ×6—‚—2æöç¦W&ò" ¢6æF–FFRÒ6÷W&6U÷FW‡@¢&Vf÷&U÷6¶VÆWFöâÒ6÷W&6U÷FW‡@¢&WÆ6VÖVçEöVF—C¢Æ—7E¶F–7E·7G"Âç•ÕÒÒµĞ¢6VÆV7FVEö–æF–6W3¢Æ—7E¶–çEÒÒµĞ¢Ö&¶W%öçVÖ&W"Ò ¢f÷"&W—"–âÖæ–fW7BævWB‚'&W—'2"ÂµÒ“ ¢–b&W—"ævWB‚'7FGW2"’Ò%$TE•ôe$tÔTåB# ¢&—6R'VçF–ÖTW'&÷"€¢b'&W—"·&W—"ævWB‚vFV6Æ&F–öåöæÖRr—Ò—2æ÷B$TE•ôe$tÔTåB ¢¢–æFW‚Ò&W—"ævWB‚&FV6Æ&F–öåö–æFW‚"¢æÖRÒ&W—"ævWB‚&FV6Æ&F–öåöæÖR"¢–bæ÷B—6–ç7Fæ6R†–æFW‚Â–çB’÷"æ÷BÃÒ–æFW‚ÂÆVâ‡6÷W&6U÷&÷w2“ ¢&—6R'VçF–ÖTW'&÷"‚'&W—"FV6Æ&F–öâ–æFW‚—2–çfÆ–B"¢–b6÷W&6U÷&÷w5¶–æFW…Õ²&æÖR%ÒÒæÖS ¢&—6R'VçF–ÖTW'&÷"†b'&W—"FV6Æ&F–öâö–æFW‚G&–gC¢¶æÖWÒ"¢–b6÷W&6U÷&÷w5¶–æFW…Õ²&†VFW%÷6†#Sb%ÒÒ&W—"ævWB‚&†VFW%÷6†#Sb"“ ¢&—6R'VçF–ÖTW'&÷"†b'&W—"†VFW"WF†÷&—G’G&–gC¢¶æÖWÒ"¢&WÆ6VÖVçG2Ò&W—"ævWB‚'&WÆ6VÖVçG2"¢–bæ÷B—6–ç7Fæ6R‡&WÆ6VÖVçG2ÂÆ—7B’÷"æ÷B&WÆ6VÖVçG3 ¢&—6R'VçF–ÖTW'&÷"†b'&W—"†2æòg&vÖVçG3¢¶æÖWÒ"¢6VÆV7FVEö–æF–6W2æVæB†–æFW‚¢f÷"&WÆ6VÖVçB–â&WÆ6VÖVçG3 ¢öÆBÒ&WÆ6VÖVçBævWB‚&öÆEög&vÖVçB"¢æWrÒ&WÆ6VÖVçBævWB‚&æWuög&vÖVçB"¢–bæ÷B—6–ç7Fæ6R†öÆBÂ7G"’÷"æ÷B—6–ç7Fæ6R†æWrÂ7G"’÷"öÆBÓÒæWs ¢&—6R'VçF–ÖTW'&÷"†b&–çfÆ–Bg&vÖVçB–ÆöC¢¶æÖWÒ"¢–b&WÆ6VÖVçBævWB‚&öÆE÷6†#Sb"’Ò6†#Se÷FW‡B†öÆB“ ¢&—6R'VçF–ÖTW'&÷"†b&öÆBg&vÖVçB4„Ö—6ÖF6ƒ¢¶æÖWÒ"¢–b&WÆ6VÖVçBævWB‚&æWu÷6†#Sb"’Ò6†#Se÷FW‡B†æWr“ ¢&—6R'VçF–ÖTW'&÷"†b&æWrg&vÖVçB4„Ö—6ÖF6ƒ¢¶æÖWÒ"¢–b&WÆ6VÖVçBævWB‚&öÆEö'—FW2"’ÒÆVâ†öÆBæVæ6öFR‚'WFbÓ‚"’“ ¢&—6R'VçF–ÖTW'&÷"†b&öÆBg&vÖVçB'—FR6÷VçBÖ—6ÖF6ƒ¢¶æÖWÒ"¢–b&WÆ6VÖVçBævWB‚&æWuö'—FW2"’ÒÆVâ†æWræVæ6öFR‚'WFbÓ‚"’“ ¢&—6R'VçF–ÖTW'&÷"†b&æWrg&vÖVçB'—FR6÷VçBÖ—6ÖF6ƒ¢¶æÖWÒ"¢7W'&VçE÷&÷w2ÒFV6Æ&F–öç2†6æF–FFR¢&Vv–öâÒFV6Æ&F–öå÷&Vv–öâ†6æF–FFRÂ7W'&VçE÷&÷w2Â–æFW‚¢6÷VçG2Ò‡&Vv–öâæ6÷VçB†öÆB’Â6æF–FFRæ6÷VçB†öÆB’Â&Vv–öâæ6÷VçB†æWr’Â6æF–FFRæ6÷VçB†æWr’¢–b6÷VçG2ÒƒÂÂÂ“ ¢&—6R'VçF–ÖTW'&÷"€¢b&g&vÖVçBVæ—VVæW72G&–gBf÷"¶æÖWÓ¢¶6÷VçG7Ó²W‡V7FVBƒÃÃÃ’ ¢¢&Vf÷&Uö†VFW"Ò7W'&VçE÷&÷w5¶–æFW…Õ²&†VFW%÷6†#Sb%Ğ¢7F'BÒ7W'&VçE÷&÷w5¶–æFW…Õ²'7F'Eööfg6WB%Ğ¢VæBÒ7W'&VçE÷&÷w5¶–æFW…Õ²&VæEööfg6WB%Ğ¢æWu÷&Vv–öâÒ&Vv–öâç&WÆ6R†öÆBÂæWrÂ¢6æF–FFRÒ6æF–FFU³§7F'EÒ²æWu÷&Vv–öâ²6æF–FFU¶VæC¥Ğ¢gFW%÷&÷w2ÒFV6Æ&F–öç2†6æF–FFR¢–bgFW%÷&÷w5¶–æFW…Õ²&†VFW%÷6†#Sb%ÒÒ&Vf÷&Uö†VFW# ¢&—6R'VçF–ÖTW'&÷"†b'V&Æ–2†VFW"6†ævVC¢¶æÖWÒ"¢Ö&¶W"Òb%ÇƒdôeTÄÅôe$tÔTåE÷¶Ö&¶W%öçVÖ&W#£FGÕÇƒ ¢Ö&¶W%öçVÖ&W"³Ò¢–b&Vf÷&U÷6¶VÆWFöâæ6÷VçB†öÆB’Ò ¢&—6R'VçF–ÖTW'&÷"†b&–çWB6¶VÆWFöâg&vÖVçBG&–gC¢¶æÖWÒ"¢&Vf÷&U÷6¶VÆWFöâÒ&Vf÷&U÷6¶VÆWFöâç&WÆ6R†öÆBÂÖ&¶W"Â¢&WÆ6VÖVçEöVF—BæVæB€¢°¢&FV6Æ&F–öåö–æFW‚#¢–æFW‚À¢&FV6Æ&F–öåöæÖR#¢æÖRÀ¢&öÆE÷6†#Sb#¢6†#Se÷FW‡B†öÆB’À¢&æWu÷6†#Sb#¢6†#Se÷FW‡B†æWr’À¢&öÆEö'—FW2#¢ÆVâ†öÆBæVæ6öFR‚'WFbÓ‚"’’À¢&æWuö'—FW2#¢ÆVâ†æWræVæ6öFR‚'WFbÓ‚"’’À¢&Ö&¶W"#¢Ö&¶W"À¢Ğ¢ ¢gFW%÷6¶VÆWFöâÒ6æF–FFP¢f÷"&÷r–â&WÆ6VÖVçEöVF—C ¢Öæ–fW7E÷&W—"ÒæW‡B€¢&W— ¢f÷"&W—"–âÖæ–fW7E²'&W—'2%Ğ¢–b&W—%²&FV6Æ&F–öåö–æFW‚%ÒÓÒ&÷u²&FV6Æ&F–öåö–æFW‚%Ğ¢¢&WÆ6VÖVçBÒæW‡B€¢—FVĞ¢f÷"—FVÒ–âÖæ–fW7E÷&W—%²'&WÆ6VÖVçG2%Ğ¢–b—FVÕ²&æWu÷6†#Sb%ÒÓÒ&÷u²&æWu÷6†#Sb%Ğ¢æB—FVÕ²&öÆE÷6†#Sb%ÒÓÒ&÷u²&öÆE÷6†#Sb%Ğ¢¢æWrÒ&WÆ6VÖVçE²&æWuög&vÖVçB%Ğ¢–bgFW%÷6¶VÆWFöâæ6÷VçB†æWr’Ò ¢&—6R'VçF–ÖTW'&÷"‚&6æF–FFR6¶VÆWFöâæWrg&vÖVçBG&–gB"¢gFW%÷6¶VÆWFöâÒgFW%÷6¶VÆWFöâç&WÆ6R†æWrÂ&÷u²&Ö&¶W"%ÒÂ¢–b&Vf÷&U÷6¶VÆWFöâÒgFW%÷6¶VÆWFöã ¢&—6R'VçF–ÖTW'&÷"‚&–Ö×WF&ÆRæöâ×F&vWB6÷W&6R6¶VÆWFöâ6†ævVB" ¢gFW%÷&÷w2ÒFV6Æ&F–öç2†6æF–FFR¢–b·&÷u²&æÖR%Òf÷"&÷r–â6÷W&6U÷&÷w5ÒÒ·&÷u²&æÖR%Òf÷"&÷r–âgFW%÷&÷w5Ó ¢&—6R'VçF–ÖTW'&÷"‚&FV6Æ&F–öâ6WVVæ6R6†ævVB"¢6†ævVEö–æF–6W2Ò°¢–æFW€¢f÷"–æFW‚Â†&Vf÷&RÂgFW"’–âVçVÖW&FR‡¦—‡6÷W&6U÷&÷w2ÂgFW%÷&÷w2Â7G&–7CÕG'VR’¢–b&Vf÷&U²'&Vv–öå÷6†#Sb%ÒÒgFW%²'&Vv–öå÷6†#Sb%Ğ¢Ğ¢–b6†ævVEö–æF–6W2Ò6÷'FVB‡6WB‡6VÆV7FVEö–æF–6W2’“ ¢&—6R'VçF–ÖTW'&÷"€¢b&6†ævVBFV6Æ&F–öç2¶6†ævVEö–æF–6W7Ó²6VÆV7FVB·6÷'FVB‡6WB‡6VÆV7FVEö–æF–6W2’—Ò ¢¢–b6öÖÖVçEöÆW†VÖW2‡6÷W&6U÷FW‡B’Ò6öÖÖVçEöÆW†VÖW2†6æF–FFR“ ¢&—6R'VçF–ÖTW'&÷"‚&Fö7VÖVçFF–öâö6öÖÖVçBÆW†VÖW26†ævVB"¢–bGG&–'WFUöÆW†VÖW2‡6÷W&6U÷FW‡B’ÒGG&–'WFUöÆW†VÖW2†6æF–FFR“ ¢&—6R'VçF–ÖTW'&÷"‚&GG&–'WFRÆW†VÖW26†ævVB"¢6öFUö&Vf÷&RÒf÷&&–FFVåö6öFUö6÷VçG2‡6÷W&6U÷FW‡B¢6öFUögFW"Òf÷&&–FFVåö6öFUö6÷VçG2†6æF–FFR¢¦W&òÒ¶æÖS¢f÷"æÖR–âdõ$$”DDTçĞ¢–b6öFUö&Vf÷&RÒ¦W&ò÷"6öFUögFW"Ò¦W&ó ¢&—6R'VçF–ÖTW'&÷"€¢b&W†V7WF&ÆRf÷&&–FFVâ×6—‚æöç¦W&ó¢&Vf÷&S×¶6öFUö&Vf÷&WÒÂgFW#×¶6öFUögFW'Ò ¢¢&uö&Vf÷&RÒ&uöf÷&&–FFVåö6÷VçG2‡6÷W&6U÷FW‡B¢&uögFW"Ò&uöf÷&&–FFVåö6÷VçG2†6æF–FFR¢–b&uö&Vf÷&RÒ&uögFW# ¢&—6R'VçF–ÖTW'&÷"‚'&ræöâÖ6öFRf÷&&–FFVâ×v÷&BÆVFvW"6†ævVB" ¢6æF–FFUö–FVçF—G’Ò°¢'6†#Sb#¢6†#Se÷FW‡B†6æF–FFR’À¢&'—FW2#¢ÆVâ†6æF–FFRæVæ6öFR‚'WFbÓ‚"’’À¢&Æ–æW2#¢ÆVâ†6æF–FFRç7Æ—FÆ–æW2‚’’À¢Ğ¢W‡V7FVEö6æF–FFRÒÖæ–fW7BævWB‚&6æF–FFR"’÷"·Ğ¢–bW‡V7FVEö6æF–FFRævWB‚'6†#Sb"’æ÷B–â€¢%TäD”äuôe$tÔTåEô…”E$D”ôâ"À¢6æF–FFUö–FVçF—G•²'6†#Sb%ÒÀ¢“ ¢&—6R'VçF–ÖTW'&÷"‚&W‡V7FVB6æF–FFR4„Ö—6ÖF6‚"¢–bW‡V7FVEö6æF–FFRævWB‚'6†#Sb"’Ò%TäD”äuôe$tÔTåEô…”E$D”ôâ# ¢–bW‡V7FVEö6æF–FFRævWB‚&'—FW2"’Ò6æF–FFUö–FVçF—G•²&'—FW2%Ó ¢&—6R'VçF–ÖTW'&÷"‚&W‡V7FVB6æF–FFR'—FR6÷VçBÖ—6ÖF6‚"¢–bW‡V7FVEö6æF–FFRævWB‚&Æ–æW2"’Ò6æF–FFUö–FVçF—G•²&Æ–æW2%Ó ¢&—6R'VçF–ÖTW'&÷"‚&W‡V7FVB6æF–FFRÆ–æR6÷VçBÖ—6ÖF6‚" ¢fÆ–FF–öâÒ°¢'66†VÖ#¢dÄ”DD”ôåõ44„TÔÀ¢'6÷W&6R#¢6÷W&6Uö–FVçF—G’À¢&6æF–FFR#¢6æF–FFUö–FVçF—G’À¢&6†ævVEöFV6Æ&F–öåö–æF–6W2#¢6†ævVEö–æF–6W2À¢&6†ævVEöFV6Æ&F–öåöæÖW2#¢·6÷W&6U÷&÷w5¶–æFW…Õ²&æÖR%Òf÷"–æFW‚–â6†ævVEö–æF–6W5ÒÀ¢'&WÆ6VÖVçEöVF—B#¢&WÆ6VÖVçEöVF—BÀ¢&–Ö×WF&ÆUöæöå÷F&vWE÷6¶VÆWFöå÷6†#Sb#¢6†#Se÷FW‡B†&Vf÷&U÷6¶VÆWFöâ’À¢&–Ö×WF&ÆUöæöå÷F&vWE÷6¶VÆWFöå÷&W6W'fVB#¢G'VRÀ¢&FV6Æ&F–öå÷6WVVæ6U÷&W6W'fVB#¢G'VRÀ¢'V&Æ–5ö†VFW'5÷&W6W'fVB#¢G'VRÀ¢&6öÖÖVçG5÷&W6W'fVB#¢G'VRÀ¢&GG&–'WFW5÷&W6W'fVB#¢G'VRÀ¢'&uöf÷&&–FFVåöÖVçF–öç5ö&Vf÷&R#¢&uö&Vf÷&RÀ¢'&uöf÷&&–FFVåöÖVçF–öç5ögFW"#¢&uögFW"À¢&W†V7WF&ÆUöf÷&&–FFVåö6÷VçG5ö&Vf÷&R#¢6öFUö&Vf÷&RÀ¢&W†V7WF&ÆUöf÷&&–FFVåö6÷VçG5ögFW"#¢6öFUögFW"À¢&W†V7WF&ÆUöf÷&&–FFVå÷6—…÷¦W&ò#¢G'VRÀ¢'7FF–5ööæÇ’#¢G'VRÀ¢&ÆVåöW†V7WFVB#¢fÇ6RÀ¢&Æ¶UöW†V7WFVB#¢fÇ6RÀ¢&v—EöW†V7WFVB#¢fÇ6RÀ¢&v—F‡V%÷w&—GFVâ#¢fÇ6RÀ¢Ğ¢&WGW&â6æF–FFRÂfÆ–FF–öà  ¦FVb–çfVçF÷'•ö6öÖÖæB†&w3¢&w'6RäæÖW76R’Óâ–çC ¢6÷W&6U÷FW‡BÂÆöu÷FW‡BÂÖWG&–2Â6öÆÆV7F÷"Â'F–f7Eö–æfòÒÆöEö'F–f7Eö–çWG2†&w2¢–çfVçF÷'’ÂÖæ–fW7BÒ'V–ÆEö–çfVçF÷'’€¢6÷W&6U÷FW‡BÀ¢Æöu÷FW‡BÀ¢ÖWG&–2À¢6öÆÆV7F÷"À¢'F–f7Eö–æfóÖ'F–f7Eö–æfòÀ¢W‡V7FVEöÖ…öW'&÷'3Ö&w2æW‡V7FVEöÖ…öW'&÷'2À¢W‡V7FVEöFV6Æ&F–öåö6÷VçCÖ&w2æW‡V7FVEöFV6Æ&F–öåö6÷VçBÀ¢&WV—&Uö6öÆÆV7F÷#Öæ÷B&w2æÆÆ÷uöÖ—76–æuö6öÆÆV7F÷"À¢¢–b&w2ç&W—%ö÷fW'&–FW3 ¢÷fW'&–FU÷F‚ÒF‚†&w2ç&W—%ö÷fW'&–FW2¢÷fW'&–FW2Ò§6öâæÆöG2€¢FV6öFU÷WFc…öÆb†÷fW'&–FU÷F‚ç&VEö'—FW2‚’Â7G"†÷fW'&–FU÷F‚’¢¢Öæ–fW7BÒÖW&vU÷&W—%ö÷fW'&–FW2†Öæ–fW7BÂ÷fW'&–FW2Â6÷W&6U÷FW‡B¢–çfVçF÷'•öFFÒ§6öåö'—FW2†–çfVçF÷'’¢Öæ–fW7EöFFÒ§6öåö'—FW2†Öæ–fW7B¢F‚†&w2æ–çfVçF÷'•ö÷WB’çw&—FUö'—FW2†–çfVçF÷'•öFF¢F‚†&w2æÖæ–fW7Eö÷WB’çw&—FUö'—FW2†Öæ–fW7EöFF¢&–çB€¢§6öâæGV×2€¢°¢&–çfVçF÷'’#¢7G"…F‚†&w2æ–çfVçF÷'•ö÷WB’ç&W6öÇfR‚’’À¢&–çfVçF÷'•öf–ÆU÷6†#Sb#¢6†#Seö'—FW2†–çfVçF÷'•öFF’À¢&–çfVçF÷'•ö6æöæ–6Å÷6†#Sb#¢Öæ–fW7E°¢&–çfVçF÷'•ö6æöæ–6Å÷6†#Sb ¢ÒÀ¢&Öæ–fW7B#¢7G"…F‚†&w2æÖæ–fW7Eö÷WB’ç&W6öÇfR‚’’À¢&Öæ–fW7E÷6†#Sb#¢6†#Seö'—FW2†Öæ–fW7EöFF’À¢'7FGW2#¢–çfVçF÷'•²'7FGW2%ÒÀ¢'7VÖÖ'’#¢–çfVçF÷'•²'7VÖÖ'’%ÒÀ¢ÒÀ¢–æFVçCÓ"À¢6÷'Eö¶W—3ÕG'VRÀ¢¢¢&WGW&â–b–çfVçF÷'•²&6ö×ÆWFVæW72%Õ²&6ö×ÆWFUögVÆÅöF–væ÷7F–5ö–çfVçF÷'’%ÒVÇ6R0  ¦FVbfÆ–FFUö6öÖÖæB†&w3¢&w'6RäæÖW76R’Óâ–çC ¢6÷W&6U÷F‚ÒF‚†&w2ç6÷W&6R¢6÷W&6U÷FW‡BÒFV6öFU÷WFc…öÆb‡6÷W&6U÷F‚ç&VEö'—FW2‚’Â7G"‡6÷W&6U÷F‚’¢Öæ–fW7E÷F‚ÒF‚†&w2æÖæ–fW7B¢Öæ–fW7BÒ§6öâæÆöG2†FV6öFU÷WFc…öÆb†Öæ–fW7E÷F‚ç&VEö'—FW2‚’Â7G"†Öæ–fW7E÷F‚’’¢6æF–FFRÂfÆ–FF–öâÒfÆ–FFUög&vÖVçEöÖæ–fW7B‡6÷W&6U÷FW‡BÂÖæ–fW7B¢–b&w2æ6æF–FFUö÷WC ¢F‚†&w2æ6æF–FFUö÷WB’çw&—FUö'—FW2†6æF–FFRæVæ6öFR‚'WFbÓ‚"’¢–b&w2çfÆ–FF–öåö÷WC ¢F‚†&w2çfÆ–FF–öåö÷WB’çw&—FUö'—FW2†§6öåö'—FW2‡fÆ–FF–öâ’¢&–çB†§6öâæGV×2‡fÆ–FF–öâÂ–æFVçCÓ"Â6÷'Eö¶W—3ÕG'VR’¢&WGW&â   ¦FVb'6W"‚’Óâ&w'6Rä&wVÖVçE'6W# ¢&ö÷BÒ&w'6Rä&wVÖVçE'6W"†FW67&—F–öãÕõöFö5õò¢7V''6W'2Ò&ö÷BæFE÷7V''6W'2†FW7CÒ&6öÖÖæB"Â&WV—&VCÕG'VR ¢–çfVçF÷'’Ò7V''6W'2æFE÷'6W"‚&–çfVçF÷'’"Â†VÇÒ&–çfVçF÷'’gVÆÂ×'Vâ'F–f7B"¢–çfVçF÷'’æFEö&wVÖVçB‚"ÒÖ'F–f7B"Â&WV—&VCÕG'VR¢–çfVçF÷'’æFEö&wVÖVçB‚"Ò×6÷W&6RÖÖVÖ&W""¢–çfVçF÷'’æFEö&wVÖVçB‚"ÒÖÆörÖÖVÖ&W""¢–çfVçF÷'’æFEö&wVÖVçB‚"ÒÖÖWG&–2ÖÖVÖ&W""¢–çfVçF÷'’æFEö&wVÖVçB‚"ÒÖgVÆÂÖF–væ÷7F–72ÖÖVÖ&W""¢–çfVçF÷'’æFEö&wVÖVçB€¢"ÒÖÆÆ÷rÖÖ—76–ærÖ6öÆÆV7F÷""À¢7F–öãÒ'7F÷&U÷G'VR"À¢†VÇÒ&ÆVv7’'6W"6Öö¶RöæÇ“²&öGV7F–öâÖ„W'&÷'3#'F–f7G2×W7Bæ÷BW6RF†—2"À¢¢–çfVçF÷'’æFEö&wVÖVçB€¢"ÒÖW‡V7FVBÖÖ‚ÖW'&÷'2"ÂG—SÖ–çBÂFVfVÇCÔDTdTÅEôU…T5DTEôÔ…ôU%$õ%0¢¢–çfVçF÷'’æFEö&wVÖVçB‚"ÒÖW‡V7FVBÖFV6Æ&F–öâÖ6÷VçB"ÂG—SÖ–çBÂFVfVÇCÓEó3“r¢–çfVçF÷'’æFEö&wVÖVçB‚"ÒÖ–çfVçF÷'’Ö÷WB"Â&WV—&VCÕG'VR¢–çfVçF÷'’æFEö&wVÖVçB‚"ÒÖÖæ–fW7BÖ÷WB"Â&WV—&VCÕG'VR¢–çfVçF÷'’æFEö&wVÖVçB€¢"Ò×&W—"Ö÷fW'&–FW2"À¢†VÇÒ&÷F–öæÂfÖg&vÖVçB×&W—"Ö÷fW'&–FW2×c¥4ôã²öæÇ’–çfVçF÷&–VB&ö÷G2Ö’ÖW&vR"À¢¢–çfVçF÷'’ç6WEöFVfVÇG2†gVæ3Ö–çfVçF÷'•ö6öÖÖæB ¢fÆ–FFRÒ7V''6W'2æFE÷'6W"€¢'fÆ–FFRÖÖæ–fW7B"Â†VÇÒ'7FF–6ÆÇ’Ç’‡–G&FVBg&vÖVçBÖæ–fW7B ¢¢fÆ–FFRæFEö&wVÖVçB‚"Ò×6÷W&6R"Â&WV—&VCÕG'VR¢fÆ–FFRæFEö&wVÖVçB‚"ÒÖÖæ–fW7B"Â&WV—&VCÕG'VR¢fÆ–FFRæFEö&wVÖVçB‚"ÒÖ6æF–FFRÖ÷WB"¢fÆ–FFRæFEö&wVÖVçB‚"Ò×fÆ–FF–öâÖ÷WB"¢fÆ–FFRç6WEöFVfVÇG2†gVæ3×fÆ–FFUö6öÖÖæB¢&WGW&â&ö÷@  ¦FVbÖ–â†&wc¢Æ—7E·7G%ÒÂæöæRÒæöæR’Óâ–çC ¢&w2Ò'6W"‚’ç'6Uö&w2†&wb¢G'“ ¢&WGW&â–çB†&w2ægVæ2†&w2’¢W†6WBW†6WF–öâ2W'&÷# ¢&–çB†b$dgVÆÂ–çfVçF÷'’f–ÇW&S¢¶W'&÷'Ò"Âf–ÆS×7—2ç7FFW'"¢&WGW&âƒ`  ¦–bõöæÖUõòÓÒ%õöÖ–åõò# ¢&—6R7—7FVÔW†—B†Ö–â‚’