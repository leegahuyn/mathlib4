#!/usr/bin/env python3
"""Fail-closed gate for one checked-in-source M2 -> M2A -> FA2000 run.

The locked v42 runner and collector are reused only as execution/diagnostic
machinery. The collector's historical v42 authority is validated exactly and
then explicitly classified as non-authoritative for v66. Current v66 authority
comes only from the checkout tree, worktree bytes, and GitHub run envelope.
"""

from __future__ import annotations

import argparse
import collections
import hashlib
import json
import os
import re
import shlex
import subprocess
import sys
from bisect import bisect_right
from pathlib import Path
from typing import Any


CONTRACT_EXIT = 86
SCHEMA = "fa-v66-checked-head-one-lane-final-gate-v1"
PROVENANCE_SCHEMA = "fa-v66-checked-head-checkout-provenance-v1"
ATTESTATION_SCHEMA = "fa-v66-checked-head-attestation-v1"
FIRST_ERROR_SCHEMA = "fa-v66-first-actual-error-v1"
ARTIFACT_CONTRACT_SCHEMA = "fa-v66-official-artifact-consumer-contract-v1"
REPOSITORY = "leegahuyn/mathlib4"
BRANCH_REF = "refs/heads/codex/fa-exclusive-focus-20260814"
SOURCE_PATH = "PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean"
OUT_RELATIVE = Path("build-logs/codex-fa-v66-checked-head/one-lane")
WORKFLOW_PATH = ".github/workflows/codex-fa-v66-timeout-structure-matrix.yml"
GATE_PATH = "scripts/fa_v66_checked_head_final_gate.py"
LEAN_VERSION = (
    "Lean (version 4.33.0-rc1, x86_64-unknown-linux-gnu, "
    "commit 62eed1db4d67327ec8120be05f1a1b0847d74561, Release)\n"
).encode("ascii")
LAKE_VERSION = b"Lake version 5.0.0-src+62eed1d (Lean version 4.33.0-rc1)\n"
ELAN_ASSET = {
    "release": "v4.2.3",
    "release_id": 335801161,
    "asset_id": 441516216,
    "draft": False,
    "prerelease": False,
    "annotated_tag_sha_prefix": "82ff3916",
    "resolved_commit_sha": "b6cec7e10fe4965a605aaf60d1cb4a5837f0462b",
    "tag_signed": False,
    "name": "elan-x86_64-unknown-linux-gnu.tar.gz",
    "url": "https://github.com/leanprover/elan/releases/download/v4.2.3/elan-x86_64-unknown-linux-gnu.tar.gz",
    "sha256": "df0b2b3a439961ffcbb3985214365ffe40f49bc871df04dff268c7d8e21ca8b2",
    "bytes": 4984019,
}
MANIFEST_PACKAGES = {
    "plausible": "b1c4a69a7e247ab7df20460212001673d74f08c0",
    "LeanSearchClient": "0498c7c070c143a3bf7379f4d99a2c63bb9d9715",
    "importGraph": "18a90119a5d316358fde6c86e0ca24e59212e32c",
    "proofwidgets": "b1436dc749e722c9920036b52cdc43b3451d0b69",
    "aesop": "57d3325be72a842920813bcb40f96a6f7393c185",
    "Qq": "ee41917ae11d38479fb8fb24745f7ca4bf0a784d",
    "batteries": "0ecf8993df88c044962426c2cbca0de5717d6150",
    "Cli": "da07ca808b6718cb2aed14dba154e5a08b8f8ecf",
}

BASELINE = {
    "previous_remote_head": "ab477fd17cd8f8616cd5c879940327ddbf6e5728",
    "path": SOURCE_PATH,
    "mode": "100644",
    "git_blob_sha": "1c760ca4464e58d5903371ca854af4ebd2fe6ddf",
    "sha256": "1cb1e5c2aba4e76637f8d706ebfbc7cf615b4a5e9b6a2871ef8e992c40e97192",
    "bytes": 2796055,
    "lines": 62559,
    "declaration_count": 4416,
    "declaration_name_sequence_sha256": "c1b152f5c2ad433904e323847453a0f25b94a9c15b7cb215dbc4d88e0d47eb8e",
    "declaration_header_projection_sha256": "ea5a7a51cb0677925fc8e360b44ec994860ceab407d5da94be40f421b73fb420",
    "declaration_header_projection_bytes": 1063065,
    "first_declaration": "cauchy_schwarz",
    "last_declaration": "graphCompletionEquivWeightedWeak_unconditional",
    "maxHeartbeats_token_count": 9,
    "set_option_maxHeartbeats_count": 9,
    "source_hygiene": {"utf8": True, "cr_count": 0, "lf_count": 62559, "nul_count": 0, "bom": False, "single_final_lf": True, "last_two_code_units": [118, 10]},
    "comment_projection": {"count": 3129, "bytes": 440570, "sha256": "be36422473700450e4564b7f2d33c802df907431ce3a2befa80f7e3a307a78c2"},
    "attribute_projection": {"count": 498, "bytes": 4982, "sha256": "e49903f17a024352d11af7aad27ec9fb16252ad73fa806281007067a60c61276"},
    "import_command_projection": {"count": 70, "bytes": 3658, "sha256": "761db5b55bb01c97a3d785f45f623fdb57cb3b296d76eebc2b2fe63c041cc807"},
    "set_option_command_projection": {"count": 23, "bytes": 1004, "sha256": "eba4f7bff23850a262df13afa893dbb402d787412124b4afadbb5e45592c9687"},
}

PINNED_DEPENDENCIES = {
    "Mock2": {
        "path": "PrimalitySheafVerification/Mock2.lean",
        "mode": "100644",
        "git_blob_sha": "94f8894b5f866701955a105044b8958a8deb7734",
        "sha256": "36a034721c389888b2c235d856753e5f2e38f9f6a258fddabbb70fe751ae3594",
        "bytes": 1119419,
    },
    "Mock2_Advanced": {
        "path": "PrimalitySheafVerification/Mock2_Advanced.lean",
        "mode": "100644",
        "git_blob_sha": "a60fa47ebcd8c1fb6037d705e81b54c80910657a",
        "sha256": "cf44063abca1d5b47331a9001a3cff45a86b5e889865812fe4e7826c6af41526",
        "bytes": 1390059,
    },
    "runner": {
        "path": "scripts/fa_v42_direct_compile_ci.sh",
        "mode": "100644",
        "git_blob_sha": "b9a661e563d79e925a208a3ab6b303baebae8077",
        "sha256": "2459f0a2cd44f6a3716de1ed2934c7588ba1a1e27ef443947d9e6089af196514",
        "bytes": 2554,
    },
    "collector": {
        "path": "scripts/fa_v42_collect_full_diagnostics.py",
        "mode": "100644",
        "git_blob_sha": "3ce4270681bf9adc7cde996eb78423dc01f8b861",
        "sha256": "7de7bc92e4e2735c0d25706d70777ea67340d8afcf67434e43b051d5cb8c90c6",
        "bytes": 12932,
    },
    "lean_toolchain": {
        "path": "lean-toolchain",
        "mode": "100644",
        "git_blob_sha": "fd85b262bf1c734663aa8292b0101f672168788f",
        "sha256": "62c2d9c0fc1ec4c67e151c11eff41ca004ef38e179cf9476c230406e6defedef",
        "bytes": 29,
    },
    "lake_manifest": {
        "path": "lake-manifest.json",
        "mode": "100644",
        "git_blob_sha": "71d2d1d50d8f0ca3d99347e6f2f00c54038b0e25",
        "sha256": "672474eb93bc14c66cd1ff45203c451987fe525f7b5d13ecd83140be46434b26",
        "bytes": 2815,
    },
    "lakefile": {
        "path": "lakefile.lean",
        "mode": "100644",
        "git_blob_sha": "2afc2a7a30308ade4ea00e21966faa37232dd4dc",
        "sha256": "9618b4491ba2a0ce2edde2cd29a6ff12974ccec5b331773ad0ae679cbebbc857",
        "bytes": 7130,
    },
}

LEGACY_AUTHORITY = {
    "run_id": "31699916923",
    "job_id": "94446323369",
    "head_sha": "6867203e032c9711b47d8c2e1bd74f30d15cbd59",
    "head_branch": "codex/fa-qym-cleanbuild-final-20260811-fast",
    "artifact_id": "9181214334",
    "artifact_digest": "sha256:bb18b117b461a4fd36746685ce4437d835382989d4b7e1cff87bb6ebbcc9c870",
    "source_sha256": "d7e99092e79b26af21cd8c960b8e9c811731e27343757b750b62c53608805937",
    "diagnostics_sha256": "b50357457a8213b1a53ae353c67fd7639334a9db4b5f7a4e61ad9c00b9f07fcf",
    "fa_log_sha256": "dc4370280c35eb1b8565e9776d9e93e42f4bf299b543a4bdaea029f438445530",
}

TRUST_KEYS = ("sorry", "admit", "axiom", "unsafe", "native_decide", "Lean.ofReduceBool")
STEMS = ("Mock2", "Mock2_Advanced", "Mock2_FunctionalAnalysis")
DECL_RE = re.compile(
    r"(?m)^(?:protected\s+|private\s+|noncomputable\s+|local\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance|structure|class)\s+(?P<name>[^\s(:]+)"
)
DIAGNOSTIC_RE = re.compile(
    r"^(?P<file>.+?\.lean):(?P<line>\d+):(?P<column>\d+):\s+"
    r"(?P<severity>error|warning)(?:\((?P<code>[^()]+)\))?:"
    r"(?P<message>.*)$"
)
CAP_SENTINEL_RE = re.compile(r"(?i)(maximum number of errors|maxErrors|too many errors|error limit)")
SYNTHETIC_SORRY_RE = re.compile(r"(?i)declaration\s+uses\s+[`']?sorry[`']?")
PANIC_RE = re.compile(r"(?i)\bPANIC\b")
HEX40 = re.compile(r"[0-9a-f]{40}")

PRE_GATE_NAMES = frozenset(
    {
        "CHECKOUT_PROVENANCE.json",
        "candidate.sha256",
        "Mock2_FunctionalAnalysis-checked-head.lean",
        "elan.log",
        "toolchain.log",
        "cache.log",
        "lean-version.txt",
        "lake-version.txt",
        "elan-version.txt",
        "elan-x86_64-unknown-linux-gnu.tar.gz",
        "elan-installer.sha256",
        "elan-download.log",
        "candidate.before.sha256",
        "candidate.before-fa.sha256",
        "candidate.after.sha256",
        "wrapper.exit",
        "Mock2_FunctionalAnalysis-observed.lean",
        "FULL_DIAGNOSTICS.json",
        "FULL_WARNINGS.json",
        "DIAGNOSTIC_DECLARATION_COUNTS.json",
        "SYNTHETIC_SORRY_WARNINGS.json",
        "METRIC.json",
        "metric-console.log",
    }
    | {f"{stem}.{suffix}" for stem in STEMS for suffix in ("command", "executed", "exit", "log")}
)
GATE_OUTPUT_NAMES = (
    "CURRENT_HEAD_ATTESTATION.json",
    "FIRST_ACTUAL_ERROR.json",
    "FINAL_GATE.json",
)
POST_GATE_NAMES = PRE_GATE_NAMES | frozenset(GATE_OUTPUT_NAMES)
assert len(PRE_GATE_NAMES) == 35
assert len(POST_GATE_NAMES) == 38

OFFICIAL_NAME_RE = re.compile(r"codex-fa-v66-checked-head-official-[0-9a-f]{40}-attempt[1-9][0-9]*")
DEBUG_NAME_RE = re.compile(r"codex-fa-v66-checked-head-incomplete-debug-[0-9a-f]{40}-attempt[1-9][0-9]*")
BODY_ONLY_REQUIREMENT = {
    "proof_body_only_delta_audit_required": True,
    "gate_locked_projections": ["declaration_headers", "comments", "attributes", "imports", "all_set_option_lines"],
    "gate_does_not_fully_cover": ["namespace", "section", "open", "remaining_scaffolding"],
}


def require(value: bool, message: str) -> None:
    if not value:
        raise AssertionError(message)


def sha256(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def git_blob_sha(payload: bytes) -> str:
    return hashlib.sha1(f"blob {len(payload)}\0".encode("ascii") + payload).hexdigest()


def canonical(value: Any) -> bytes:
    return (json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True) + "\n").encode("utf-8")


def compact(value: Any) -> bytes:
    return (json.dumps(value, ensure_ascii=False, separators=(",", ":"), sort_keys=True) + "\n").encode("utf-8")


def link_like(path: Path) -> bool:
    return path.is_symlink() or (hasattr(path, "is_junction") and path.is_junction())


def ordinary(path: Path) -> bytes:
    require(path.is_file() and not link_like(path), f"missing ordinary evidence: {path.name}")
    return path.read_bytes()


def reject_duplicate_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        require(key not in result, f"duplicate JSON key: {key}")
        result[key] = value
    return result


def load_json(path: Path) -> Any:
    return json.loads(ordinary(path), object_pairs_hook=reject_duplicate_keys)


def load_canonical_json(path: Path) -> Any:
    value = load_json(path)
    require(ordinary(path) == canonical(value), f"JSON byte form mismatch: {path.name}")
    return value


def parse_exit(path: Path) -> int:
    payload = ordinary(path)
    text = payload.decode("ascii").strip()
    require(re.fullmatch(r"(?:0|[1-9][0-9]{0,2})", text) is not None, f"malformed exit: {path.name}")
    value = int(text)
    require(0 <= value <= 255, f"exit out of range: {path.name}")
    require(payload == f"{value}\n".encode("ascii"), f"exit byte form mismatch: {path.name}")
    return value


def require_sha_lock(path: Path, expected_sha256: str) -> None:
    require(ordinary(path) == (expected_sha256 + "\n").encode("ascii"), f"SHA lock identity/byte-form drift: {path.name}")


def direct_inventory(root: Path) -> frozenset[str]:
    names: set[str] = set()
    for path in root.iterdir():
        require(path.is_file() and not link_like(path), f"non-flat/non-ordinary artifact member: {path.name}")
        names.add(path.name)
    return frozenset(names)


def require_inventory(root: Path, expected: frozenset[str], phase: str) -> None:
    actual = direct_inventory(root)
    require(actual == expected, f"{phase} inventory mismatch: missing={sorted(expected-actual)!r} extra={sorted(actual-expected)!r}")


def preflight_outputs(paths: list[Path], root: Path) -> list[Path]:
    resolved: list[Path] = []
    for path in paths:
        require(path.is_absolute() and not path.exists() and not link_like(path), f"output must be absent absolute non-link: {path.name}")
        require(path.parent.is_dir() and not link_like(path.parent) and path.parent.resolve(strict=True) == root, f"output escapes exact ordinary root: {path.name}")
        target = path.resolve(strict=False)
        require(target.parent == root, f"output is not direct child: {path.name}")
        resolved.append(target)
    require(len({os.path.normcase(str(path)) for path in resolved}) == len(paths), "output paths must be distinct")
    return resolved


def write_new(path: Path, payload: bytes) -> None:
    with path.open("xb") as stream:
        stream.write(payload)


def git(repo: Path, *args: str) -> bytes:
    proc = subprocess.run(["git", "-C", str(repo), *args], capture_output=True, check=False)
    require(proc.returncode == 0, f"git {' '.join(args)} failed: {proc.stderr.decode(errors='replace')}")
    return proc.stdout


def checked_path_lock(repo: Path, relative: str) -> dict[str, Any]:
    path = repo / relative
    resolved = path.resolve(strict=True)
    require(resolved.is_relative_to(repo) and not link_like(path), f"checked path escapes or links: {relative}")
    payload = ordinary(path)
    row = git(repo, "ls-tree", "-z", "HEAD", "--", relative)
    require(row.endswith(b"\0") and row.count(b"\0") == 1, f"git tree row missing/duplicate: {relative}")
    meta, recorded = row[:-1].split(b"\t", 1)
    mode, kind, tree_blob = meta.decode("ascii").split(" ")
    require(recorded.decode("utf-8") == relative and mode == "100644" and kind == "blob" and HEX40.fullmatch(tree_blob) is not None, f"git tree identity mismatch: {relative}")
    computed_blob = git_blob_sha(payload)
    hash_object = git(repo, "hash-object", "--no-filters", "--", relative).decode("ascii").strip()
    require(tree_blob == computed_blob == hash_object, f"ls-tree/hash-object/worktree blob mismatch: {relative}")
    return {"path": relative, "mode": mode, "git_blob_sha": tree_blob, "sha256": sha256(payload), "bytes": len(payload)}


def manifest_environment(repo: Path, checkout_head: str) -> dict[str, Any]:
    manifest = load_json(repo / "lake-manifest.json")
    require(isinstance(manifest, dict), "lake manifest root is not object")
    require(set(manifest) == {"version", "packagesDir", "packages", "name", "lakeDir", "fixedToolchain"}, "lake manifest root keys drift")
    require(
        {
            "version": manifest.get("version"),
            "packagesDir": manifest.get("packagesDir"),
            "name": manifest.get("name"),
            "lakeDir": manifest.get("lakeDir"),
            "fixedToolchain": manifest.get("fixedToolchain"),
        }
        == {"version": "1.2.0", "packagesDir": ".lake/packages", "name": "mathlib", "lakeDir": ".lake", "fixedToolchain": True},
        "lake manifest root identity drift",
    )
    packages = manifest.get("packages")
    require(isinstance(packages, list) and len(packages) == 8 and all(isinstance(row, dict) for row in packages), "lake manifest package shape drift")
    revisions = {row.get("name"): row.get("rev") for row in packages}
    require(revisions == MANIFEST_PACKAGES, "lake manifest package revision map drift")
    return {
        "manifest_schema_version": "1.2.0",
        "root_package": "mathlib",
        "root_mathlib_revision": checkout_head,
        "root_mathlib_revision_derivation": "CURRENT_CHECKOUT_HEAD_NO_SEPARATE_MANIFEST_PACKAGE_REV",
        "fixedToolchain": True,
        "packagesDir": ".lake/packages",
        "lakeDir": ".lake",
        "package_revisions": revisions,
    }


def evidence_file_lock(path: Path, nonempty: bool = False) -> dict[str, Any]:
    payload = ordinary(path)
    if nonempty:
        require(payload, f"empty environment evidence: {path.name}")
    return {"path": path.name, "sha256": sha256(payload), "bytes": len(payload)}


def strip_noncode(text: str) -> str:
    chars = list(text)
    i = 0
    depth = 0
    in_string = False
    escaped = False
    while i < len(chars):
        if depth:
            if text.startswith("/-", i):
                chars[i] = chars[i + 1] = " "
                depth += 1
                i += 2
                continue
            if text.startswith("-/", i):
                chars[i] = chars[i + 1] = " "
                depth -= 1
                i += 2
                continue
            if chars[i] != "\n":
                chars[i] = " "
            i += 1
            continue
        if in_string:
            original = chars[i]
            if original != "\n":
                chars[i] = " "
            if escaped:
                escaped = False
            elif original == "\\":
                escaped = True
            elif original == '"':
                in_string = False
            i += 1
            continue
        if text.startswith("/-", i):
            chars[i] = chars[i + 1] = " "
            depth = 1
            i += 2
            continue
        if text.startswith("--", i):
            while i < len(chars) and chars[i] != "\n":
                chars[i] = " "
                i += 1
            continue
        if chars[i] == '"':
            chars[i] = " "
            in_string = True
        i += 1
    return "".join(chars)


def comments_and_attributes(text: str) -> tuple[list[str], list[str]]:
    """Return ordered raw comments/attributes while ignoring string contents."""
    comments: list[str] = []
    attributes: list[str] = []
    index = 0
    size = len(text)
    in_string = False
    escaped = False
    while index < size:
        char = text[index]
        if in_string:
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
            index += 1
            continue
        if char == '"':
            in_string = True
            index += 1
            continue
        if text.startswith("--", index):
            end = text.find("\n", index)
            end = size if end < 0 else end
            comments.append(text[index:end])
            index = end
            continue
        if text.startswith("/-", index):
            start = index
            depth = 1
            index += 2
            while index < size and depth:
                if text.startswith("/-", index):
                    depth += 1
                    index += 2
                elif text.startswith("-/", index):
                    depth -= 1
                    index += 2
                else:
                    index += 1
            require(depth == 0, "unterminated block comment")
            comments.append(text[start:index])
            continue
        if text.startswith("@[", index):
            end = text.find("]", index + 2)
            require(end >= 0, "unterminated attribute")
            attributes.append(text[index : end + 1])
            index = end + 1
            continue
        index += 1
    return comments, attributes


def compact_projection(values: list[str] | list[list[str]]) -> dict[str, Any]:
    payload = json.dumps(values, ensure_ascii=False, separators=(",", ":")).encode("utf-8")
    return {"count": len(values), "bytes": len(payload), "sha256": sha256(payload)}


def top_level_command_projections(text: str) -> tuple[list[str], list[str]]:
    executable = strip_noncode(text)
    imports: list[str] = []
    set_options: list[str] = []
    raw_lines = text.splitlines()
    executable_lines = executable.splitlines()
    require(len(raw_lines) == len(executable_lines), "source lexer line preservation failed")
    for raw_line, executable_line in zip(raw_lines, executable_lines, strict=True):
        if re.match(r"^\s*import(?:[ \t]|$)", executable_line):
            imports.append(raw_line)
        if re.match(r"^\s*set_option(?:[ \t]|$)", executable_line):
            set_options.append(raw_line)
    return imports, set_options


def source_structure(text: str) -> dict[str, Any]:
    matches = list(DECL_RE.finditer(text))
    regions = [
        {"name": match.group("name"), "start": match.start(), "end": matches[index + 1].start() if index + 1 < len(matches) else len(text)}
        for index, match in enumerate(matches)
    ]
    headers: list[list[str]] = []
    for row in regions:
        region = text[row["start"] : row["end"]]
        cuts = [point for point in (region.find(":= by"), region.find(":="), region.find(" where\n")) if point >= 0]
        headers.append([row["name"], region if not cuts else region[: min(cuts)]])
    names_payload = "\n".join(row["name"] for row in regions).encode("utf-8")
    headers_payload = json.dumps(headers, ensure_ascii=False, separators=(",", ":")).encode("utf-8")
    code = strip_noncode(text)
    comments, attributes = comments_and_attributes(text)
    imports, set_options = top_level_command_projections(text)
    trust = {
        token: len(re.findall(r"(?<![A-Za-z0-9_])" + re.escape(token) + r"(?![A-Za-z0-9_])", code))
        for token in TRUST_KEYS
    }
    return {
        "declaration_count": len(regions),
        "declaration_name_sequence_sha256": sha256(names_payload),
        "declaration_header_projection_sha256": sha256(headers_payload),
        "declaration_header_projection_bytes": len(headers_payload),
        "first_declaration": regions[0]["name"] if regions else None,
        "last_declaration": regions[-1]["name"] if regions else None,
        "maxHeartbeats_token_count": len(re.findall(r"(?<![A-Za-z0-9_])maxHeartbeats(?![A-Za-z0-9_])", code)),
        "set_option_maxHeartbeats_count": len(re.findall(r"(?m)^\s*set_option\s+maxHeartbeats\b", code)),
        "trust_six": trust,
        "comment_projection": compact_projection(comments),
        "attribute_projection": compact_projection(attributes),
        "import_command_projection": compact_projection(imports),
        "set_option_command_projection": compact_projection(set_options),
        "source_hygiene": {
            "utf8": True,
            "cr_count": text.count("\r"),
            "lf_count": text.count("\n"),
            "nul_count": text.count("\x00"),
            "bom": text.startswith("\ufeff"),
            "single_final_lf": text.endswith("\n") and not text.endswith("\n\n"),
            "last_two_code_units": [ord(char) for char in text[-2:]],
        },
    }


def require_stable_source_structure(structure: dict[str, Any]) -> None:
    for key in (
        "declaration_count",
        "declaration_name_sequence_sha256",
        "declaration_header_projection_sha256",
        "declaration_header_projection_bytes",
        "first_declaration",
        "last_declaration",
        "maxHeartbeats_token_count",
        "set_option_maxHeartbeats_count",
        "comment_projection",
        "attribute_projection",
        "import_command_projection",
        "set_option_command_projection",
    ):
        require(structure.get(key) == BASELINE[key], f"source structural lock mismatch: {key}")
    require(structure.get("trust_six") == {key: 0 for key in TRUST_KEYS}, "source trust-six is not exact zero")
    require_source_hygiene(structure.get("source_hygiene"))


def require_source_hygiene(hygiene: Any) -> None:
    require(isinstance(hygiene, dict), "source hygiene missing")
    require(
        hygiene.get("utf8") is True
        and hygiene.get("cr_count") == 0
        and hygiene.get("nul_count") == 0
        and hygiene.get("bom") is False
        and hygiene.get("single_final_lf") is True
        and isinstance(hygiene.get("lf_count"), int)
        and hygiene.get("lf_count") > 0
        and isinstance(hygiene.get("last_two_code_units"), list)
        and hygiene["last_two_code_units"][-1:] == [10],
        "source hygiene invariant mismatch",
    )


def require_dependency_log(stem: str, inventory: dict[str, Any], timeout_lines: list[str]) -> None:
    require(inventory.get("error_count") == 0, f"dependency compiler error header present: {stem}")
    require(timeout_lines == [], f"dependency timeout evidence present: {stem}")


def require_fa_semantic_state(fa_exit: int, errors: list[Any], warnings: list[Any], timeout_lines: list[str]) -> None:
    require((fa_exit == 0 and not errors) or (fa_exit == 1 and bool(errors)), "FA exit/error-list semantic coherence mismatch")
    if fa_exit == 0:
        require(warnings == [], "FA0 with warnings is not TRUE PASS evidence")
        require(timeout_lines == [], "FA0 with timeout evidence is not TRUE PASS")


def parse_diagnostics(source_text: str, log_text: str) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    declarations = list(DECL_RE.finditer(source_text))
    starts = [source_text.count("\n", 0, match.start()) + 1 for match in declarations]
    errors: list[dict[str, Any]] = []
    warnings: list[dict[str, Any]] = []
    source_name = Path(SOURCE_PATH).name
    for raw in log_text.splitlines():
        match = DIAGNOSTIC_RE.match(raw)
        if match is None:
            continue
        line = int(match.group("line"))
        same_source = Path(match.group("file")).name == source_name
        index = bisect_right(starts, line) - 1 if same_source else -1
        message = match.group("message").strip()
        item: dict[str, Any] = {
            "file": match.group("file"),
            "line": line,
            "column": int(match.group("column")),
            "severity": match.group("severity"),
            "diagnostic_code": match.group("code"),
            "message": message,
            "normalized_message_signature": re.sub(r"\s+", " ", message).strip(),
            "source_file_match": same_source,
            "declaration": declarations[index].group("name") if index >= 0 else None,
            "declaration_index": index if index >= 0 else None,
            "raw_header": raw,
        }
        target = errors if item["severity"] == "error" else warnings
        item["ordinal"] = len(target) + 1
        target.append(item)
    return errors, warnings


def expected_command(stem: str) -> list[str]:
    cap = "2000" if stem == "Mock2_FunctionalAnalysis" else "1"
    base = f".lake/build/lib/lean/PrimalitySheafVerification/{stem}"
    return ["lake", "env", "lean", f"-DmaxErrors={cap}", "-DwarningAsError=false", "-o", f"{base}.olean", "-i", f"{base}.ilean", f"PrimalitySheafVerification/{stem}.lean"]


def expected_command_bytes(stem: str) -> bytes:
    return (" ".join(expected_command(stem)) + " \n").encode("ascii")


def raw_header_inventory(log_text: str) -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    for raw in log_text.splitlines():
        match = DIAGNOSTIC_RE.match(raw)
        if match is None:
            continue
        rows.append(
            {
                "file": match.group("file"),
                "line": int(match.group("line")),
                "column": int(match.group("column")),
                "severity": match.group("severity"),
                "diagnostic_code": match.group("code"),
                "message": match.group("message").strip(),
                "raw_header": raw,
            }
        )
    projection = compact_projection([row["raw_header"] for row in rows])
    error_headers = [row["raw_header"] for row in rows if row["severity"] == "error"]
    warning_headers = [row["raw_header"] for row in rows if row["severity"] == "warning"]
    return {
        "error_count": len(error_headers),
        "warning_count": len(warning_headers),
        "diagnostic_count": len(rows),
        "raw_header_projection": projection,
        "error_raw_headers": error_headers,
        "warning_raw_headers": warning_headers,
    }


def compiled_product_lock(repo: Path, stem: str, suffix: str, required: bool) -> dict[str, Any]:
    relative = f".lake/build/lib/lean/PrimalitySheafVerification/{stem}.{suffix}"
    path = repo / relative
    require(not link_like(path), f"compiled product is link-like: {relative}")
    if not path.exists():
        require(not required, f"required compiled product missing: {relative}")
        return {"path": relative, "required": required, "present": False}
    resolved = path.resolve(strict=True)
    require(resolved.is_relative_to(repo), f"compiled product escapes repository: {relative}")
    parent = path.parent
    while parent != repo:
        require(not link_like(parent), f"compiled product parent is link-like: {relative}")
        parent = parent.parent
    payload = ordinary(path)
    require(payload, f"compiled product is empty: {relative}")
    return {"path": relative, "required": required, "present": True, "sha256": sha256(payload), "bytes": len(payload)}


def official_artifact_name_allowed(name: str) -> bool:
    return OFFICIAL_NAME_RE.fullmatch(name) is not None and "incomplete-debug" not in name


def artifact_names(head: str, attempt: str) -> tuple[str, str]:
    official = f"codex-fa-v66-checked-head-official-{head}-attempt{attempt}"
    debug = f"codex-fa-v66-checked-head-incomplete-debug-{head}-attempt{attempt}"
    require(official_artifact_name_allowed(official), "constructed official artifact name rejected")
    require(DEBUG_NAME_RE.fullmatch(debug) is not None and not official_artifact_name_allowed(debug), "debug artifact name not fail-closed")
    return official, debug


def validate_envelope(args: argparse.Namespace) -> dict[str, str]:
    require(os.environ.get("GITHUB_REPOSITORY") == REPOSITORY, "repository envelope mismatch")
    require(os.environ.get("GITHUB_SHA") == args.expected_github_sha, "GITHUB_SHA envelope mismatch")
    require(os.environ.get("GITHUB_REF") == args.expected_github_ref, "GITHUB_REF envelope mismatch")
    require(os.environ.get("GITHUB_RUN_ID") == args.expected_run_id, "GITHUB_RUN_ID envelope mismatch")
    require(os.environ.get("GITHUB_RUN_ATTEMPT") == args.expected_run_attempt, "GITHUB_RUN_ATTEMPT envelope mismatch")
    event = os.environ.get("GITHUB_EVENT_NAME")
    require(event in {"push", "workflow_dispatch"}, "unexpected event envelope")
    return {"repository": REPOSITORY, "event_name": event}


def validated_paths(args: argparse.Namespace) -> tuple[Path, Path, Path]:
    require(args.repo_root.is_absolute() and args.repo_root.is_dir() and not link_like(args.repo_root), "repo root must be absolute ordinary directory")
    repo = args.repo_root.resolve(strict=True)
    require(args.out.is_absolute() and args.out.is_dir() and not link_like(args.out), "output root must be absolute ordinary directory")
    root = args.out.resolve(strict=True)
    expected_root = (repo / OUT_RELATIVE).resolve(strict=True)
    require(root == expected_root, "output root is not the exact v66 evidence directory")
    source_path = (repo / SOURCE_PATH).resolve(strict=True)
    require(args.source.resolve(strict=True) == source_path and not link_like(args.source), "source is not exact checked-in path")
    return repo, root, source_path


def capture_provenance(args: argparse.Namespace, repo: Path, root: Path, source_path: Path) -> int:
    require_inventory(root, frozenset(), "pre-capture")
    envelope = validate_envelope(args)
    checkout_head = git(repo, "rev-parse", "HEAD").decode("ascii").strip()
    checkout_tree = git(repo, "rev-parse", "HEAD^{tree}").decode("ascii").strip()
    require(checkout_head == args.expected_github_sha and HEX40.fullmatch(checkout_tree) is not None, "checkout head/tree mismatch")

    source_payload = ordinary(source_path)
    source_text = source_payload.decode("utf-8")
    source_row = checked_path_lock(repo, SOURCE_PATH)
    source_row["lines"] = len(source_text.splitlines())
    source_row["structure"] = source_structure(source_text)
    require_stable_source_structure(source_row["structure"])

    dependencies = {name: checked_path_lock(repo, expected["path"]) for name, expected in PINNED_DEPENDENCIES.items()}
    for name, expected in PINNED_DEPENDENCIES.items():
        require(dependencies[name] == expected, f"pinned dependency mismatch: {name}")
    require(ordinary(repo / "lean-toolchain") == b"leanprover/lean4:v4.33.0-rc1\n", "lean-toolchain content mismatch")
    dependencies["workflow"] = checked_path_lock(repo, WORKFLOW_PATH)
    dependencies["final_gate"] = checked_path_lock(repo, GATE_PATH)
    mathlib_environment = manifest_environment(repo, checkout_head)

    baseline_identity = {key: source_row.get(key) for key in ("path", "mode", "git_blob_sha", "sha256", "bytes", "lines")}
    baseline_match = baseline_identity == {key: BASELINE[key] for key in baseline_identity}
    official_name, debug_name = artifact_names(args.expected_github_sha, args.expected_run_attempt)
    provenance = {
        "schema": PROVENANCE_SCHEMA,
        **envelope,
        "run_id": args.expected_run_id,
        "run_attempt": args.expected_run_attempt,
        "github_ref": args.expected_github_ref,
        "github_sha": args.expected_github_sha,
        "checkout_head": checkout_head,
        "checkout_tree": checkout_tree,
        "source": source_row,
        "dependencies": dependencies,
        "mathlib_environment": mathlib_environment,
        "activation_baseline": BASELINE,
        "activation_baseline_source_match": baseline_match,
        "source_materialized_or_overwritten": False,
        "artifact_names": {"official": official_name, "incomplete_debug": debug_name},
    }
    outputs = preflight_outputs(
        [root / "CHECKOUT_PROVENANCE.json", root / "candidate.sha256", root / "Mock2_FunctionalAnalysis-checked-head.lean"],
        root,
    )
    payloads = [canonical(provenance), (source_row["sha256"] + "\n").encode("ascii"), source_payload]
    for path, payload in zip(outputs, payloads, strict=True):
        write_new(path, payload)
    print(json.dumps(provenance, ensure_ascii=False, sort_keys=True))
    return 0


def final_gate(args: argparse.Namespace, repo: Path, root: Path, source_path: Path) -> int:
    require_inventory(root, PRE_GATE_NAMES, "pre-final")
    require(args.provenance is not None and args.provenance.resolve(strict=True) == (root / "CHECKOUT_PROVENANCE.json").resolve(strict=True), "provenance path mismatch")
    envelope = validate_envelope(args)
    provenance = load_canonical_json(args.provenance)
    require(provenance.get("schema") == PROVENANCE_SCHEMA, "provenance schema mismatch")
    require(provenance.get("repository") == REPOSITORY and provenance.get("event_name") == envelope["event_name"], "provenance repository/event mismatch")
    require(provenance.get("github_sha") == args.expected_github_sha == provenance.get("checkout_head"), "checkout head mismatch")
    require(provenance.get("github_ref") == args.expected_github_ref, "checkout ref mismatch")
    require(str(provenance.get("run_id")) == args.expected_run_id and str(provenance.get("run_attempt")) == args.expected_run_attempt, "run envelope mismatch")
    checkout_head = git(repo, "rev-parse", "HEAD").decode("ascii").strip()
    checkout_tree = git(repo, "rev-parse", "HEAD^{tree}").decode("ascii").strip()
    require((checkout_head, checkout_tree) == (provenance.get("checkout_head"), provenance.get("checkout_tree")), "checkout changed after capture")

    source = ordinary(source_path)
    source_text = source.decode("utf-8")
    source_row = checked_path_lock(repo, SOURCE_PATH)
    source_row["lines"] = len(source_text.splitlines())
    source_row["structure"] = source_structure(source_text)
    require_stable_source_structure(source_row["structure"])
    require(source_row == provenance.get("source"), "source changed after capture")
    source_lock = {key: source_row[key] for key in ("sha256", "bytes", "lines", "git_blob_sha")}

    dependencies = provenance.get("dependencies")
    require(isinstance(dependencies, dict) and set(dependencies) == set(PINNED_DEPENDENCIES) | {"workflow", "final_gate"}, "dependency inventory mismatch")
    for name, expected in PINNED_DEPENDENCIES.items():
        current = checked_path_lock(repo, expected["path"])
        require(current == expected == dependencies.get(name), f"pinned dependency changed: {name}")
    for name, relative in (("workflow", WORKFLOW_PATH), ("final_gate", GATE_PATH)):
        require(checked_path_lock(repo, relative) == dependencies.get(name), f"dynamic dependency changed: {name}")
    require(ordinary(repo / "lean-toolchain") == b"leanprover/lean4:v4.33.0-rc1\n", "lean-toolchain content mismatch")
    require(ordinary(root / "lean-version.txt") == LEAN_VERSION, "Lean version mismatch")
    require(ordinary(root / "lake-version.txt") == LAKE_VERSION, "Lake version mismatch")
    elan_version_payload = ordinary(root / "elan-version.txt")
    require(
        re.fullmatch(rb"elan 4\.2\.3[^\r\n]*\n", elan_version_payload) is not None,
        "elan version is not a single-LF v4.2.3 record",
    )
    mathlib_environment = manifest_environment(repo, checkout_head)
    require(provenance.get("mathlib_environment") == mathlib_environment, "captured mathlib environment drift")
    elan_payload = ordinary(root / ELAN_ASSET["name"])
    require((sha256(elan_payload), len(elan_payload)) == (ELAN_ASSET["sha256"], ELAN_ASSET["bytes"]), "elan release asset lock mismatch")
    require(
        ordinary(root / "elan-installer.sha256") == f"{ELAN_ASSET['sha256']}  {ELAN_ASSET['name']}\n".encode("ascii"),
        "elan installer checksum file mismatch",
    )
    environment_evidence = {
        "elan_release_asset": {**ELAN_ASSET, **evidence_file_lock(root / ELAN_ASSET["name"], nonempty=True)},
        "elan_installer_sha256_file": evidence_file_lock(root / "elan-installer.sha256", nonempty=True),
        "elan_download_log": evidence_file_lock(root / "elan-download.log"),
        "elan_install_log": evidence_file_lock(root / "elan.log"),
        "toolchain_install_log": evidence_file_lock(root / "toolchain.log", nonempty=True),
        "cache_log": evidence_file_lock(root / "cache.log", nonempty=True),
        "lean_version": evidence_file_lock(root / "lean-version.txt", nonempty=True),
        "lake_version": evidence_file_lock(root / "lake-version.txt", nonempty=True),
        "elan_version": {**evidence_file_lock(root / "elan-version.txt", nonempty=True), "validation": "RECORDED_HASH_BYTES_AND_SEMANTIC_EXACT_VERSION_4.2.3"},
        "mathlib": mathlib_environment,
    }

    baseline_identity = {key: source_row.get(key) for key in ("path", "mode", "git_blob_sha", "sha256", "bytes", "lines")}
    baseline_match = baseline_identity == {key: BASELINE[key] for key in baseline_identity}
    require(provenance.get("activation_baseline") == BASELINE and provenance.get("activation_baseline_source_match") is baseline_match, "activation baseline classification mismatch")
    official_name, debug_name = artifact_names(args.expected_github_sha, args.expected_run_attempt)
    require(provenance.get("artifact_names") == {"official": official_name, "incomplete_debug": debug_name}, "artifact name contract drift")

    for name in ("candidate.sha256", "candidate.before.sha256", "candidate.before-fa.sha256", "candidate.after.sha256"):
        require_sha_lock(root / name, source_row["sha256"])
    require(ordinary(root / "Mock2_FunctionalAnalysis-checked-head.lean") == source, "initial checked-head source copy mismatch")
    require(ordinary(root / "Mock2_FunctionalAnalysis-observed.lean") == source, "observed source copy mismatch")

    exits = {stem: parse_exit(root / f"{stem}.exit") for stem in STEMS}
    wrapper_rc = parse_exit(root / "wrapper.exit")
    require(wrapper_rc == 0, "direct wrapper infrastructure failure")
    require(exits["Mock2"] == 0 and exits["Mock2_Advanced"] == 0, "dependency compile failure")
    require(exits["Mock2_FunctionalAnalysis"] in {0, 1}, "FA exit is not a semantic 0/1 result")
    for stem in STEMS:
        require(ordinary(root / f"{stem}.executed") == b"", f"execution marker malformed: {stem}")
        command_payload = ordinary(root / f"{stem}.command")
        command_text = command_payload.decode("utf-8")
        require(command_payload == expected_command_bytes(stem) and shlex.split(command_text) == expected_command(stem), f"exact command/byte-form mismatch: {stem}")

    logs = {stem: ordinary(root / f"{stem}.log").decode("utf-8", errors="replace") for stem in STEMS}
    panic_lines = [line for stem in STEMS for line in logs[stem].splitlines() if PANIC_RE.search(line)]
    require(not panic_lines, "PANIC-class infrastructure evidence present")
    timeout_lines = {stem: [line for line in logs[stem].splitlines() if re.search(r"(?i)\btimeout\b", line)] for stem in STEMS}
    header_inventories = {stem: raw_header_inventory(logs[stem]) for stem in STEMS}
    for stem in ("Mock2", "Mock2_Advanced"):
        require_dependency_log(stem, header_inventories[stem], timeout_lines[stem])
    compiled_products = {
        stem: {
            suffix: compiled_product_lock(repo, stem, suffix, required=(stem != "Mock2_FunctionalAnalysis" or exits[stem] == 0))
            for suffix in ("olean", "ilean")
        }
        for stem in STEMS
    }

    metric = load_canonical_json(root / "METRIC.json")
    require(ordinary(root / "metric-console.log") == canonical(metric), "metric console/JSON byte mirror mismatch")
    diagnostics = load_canonical_json(root / "FULL_DIAGNOSTICS.json")
    warnings = load_canonical_json(root / "FULL_WARNINGS.json")
    declaration_counts = load_canonical_json(root / "DIAGNOSTIC_DECLARATION_COUNTS.json")
    synthetic_sorry = load_canonical_json(root / "SYNTHETIC_SORRY_WARNINGS.json")
    require(all(isinstance(value, list) for value in (diagnostics, warnings, declaration_counts, synthetic_sorry)), "collector output shape mismatch")

    parsed_errors, parsed_warnings = parse_diagnostics(source_text, logs["Mock2_FunctionalAnalysis"])
    require(diagnostics == parsed_errors and warnings == parsed_warnings, "raw log/diagnostic list/order mismatch")
    require(
        (header_inventories["Mock2_FunctionalAnalysis"]["error_count"], header_inventories["Mock2_FunctionalAnalysis"]["warning_count"])
        == (len(parsed_errors), len(parsed_warnings)),
        "FA raw-header inventory count mismatch",
    )
    expected_declaration_counts = collections.Counter((row["declaration_index"], row["declaration"]) for row in parsed_errors)
    expected_declaration_rows = [
        {"declaration_index": key[0], "declaration": key[1], "count": count}
        for key, count in sorted(expected_declaration_counts.items(), key=lambda item: (item[0][0] if item[0][0] is not None else -1, item[0][1] or ""))
    ]
    require(declaration_counts == expected_declaration_rows, "diagnostic declaration ledger mismatch")
    expected_synthetic = [row for row in parsed_warnings if SYNTHETIC_SORRY_RE.search(row["message"])]
    require(synthetic_sorry == expected_synthetic == [], "synthetic declaration-uses-sorry warning present or incoherent")
    cap_sentinel = CAP_SENTINEL_RE.search(logs["Mock2_FunctionalAnalysis"]) is not None
    require(not cap_sentinel and len(parsed_errors) < 2000, "diagnostic cap/sentinel prevents complete inventory")

    require(metric.get("schema") == "fa-v42-two-variant-highcap2000-metric-v1", "legacy collector schema drift")
    require(metric.get("authority") == LEGACY_AUTHORITY, "legacy collector authority drift")
    require(metric.get("variant") == "checked_head" and metric.get("variant_index_expected_sha256") is None and metric.get("variant_index_actual_sha256") is None, "collector variant envelope drift")
    require(metric.get("github_head_sha") == args.expected_github_sha and str(metric.get("github_run_id")) == args.expected_run_id, "metric run/head mismatch")
    require(metric.get("candidate_expected_sha256") == metric.get("candidate_locked_sha256") == metric.get("source_sha256") == source_row["sha256"], "metric source identity mismatch")
    require((metric.get("source_bytes"), metric.get("source_lines"), metric.get("source_declaration_count")) == (source_row["bytes"], source_row["lines"], 4416), "metric source size/lines/declarations mismatch")
    require(metric.get("source_executable_trust_counts") == {key: 0 for key in TRUST_KEYS} and metric.get("source_executable_trust_six_zero") is True, "metric trust-six mismatch")
    require(metric.get("source_identity_locked") is True and metric.get("all_required_lean_executed") is True, "collector source/execution evidence incomplete")
    require(metric.get("all_required_raw_logs_uploaded") is True and metric.get("all_required_raw_logs_from_execution") is True, "collector raw-log evidence incomplete")
    require(metric.get("raw_log_placeholders") == [] and metric.get("exit_parse_errors") == {}, "collector placeholder/exit parse drift")
    require((metric.get("Mock2_exit"), metric.get("Mock2_Advanced_exit"), metric.get("FA_exit")) == (0, 0, exits["Mock2_FunctionalAnalysis"]), "metric exit mismatch")
    require(metric.get("compiler_exit_clean") is (exits["Mock2_FunctionalAnalysis"] == 0), "collector clean-exit classification mismatch")
    require(metric.get("FA_compile_max_errors") == 2000, "collector max-errors drift")
    require(metric.get("FA_error_headers_captured") == len(parsed_errors), "collector error count mismatch")
    require(metric.get("FA_warning_headers_captured") == len(parsed_warnings), "collector warning count mismatch")
    require(metric.get("FA_diagnostic_headers_captured") == len(parsed_errors) + len(parsed_warnings), "collector diagnostic count mismatch")
    require(metric.get("FA_error_cap_sentinel_present") is False and metric.get("FA_inventory_below_configured_cap") is True and metric.get("FA_inventory_complete_by_header_evidence") is True, "collector inventory completeness mismatch")
    require(metric.get("unique_declarations_with_errors") == len(expected_declaration_counts), "collector declaration count mismatch")
    require(metric.get("unique_normalized_message_signatures") == len({row["normalized_message_signature"] for row in parsed_errors}), "collector signature count mismatch")
    expected_codes = collections.Counter(row["diagnostic_code"] or "<none>" for row in parsed_errors)
    require(metric.get("error_headers_by_optional_code") == dict(sorted(expected_codes.items())), "collector diagnostic-code multiset mismatch")
    require(metric.get("synthetic_declaration_uses_sorry_warning_count") == 0 and metric.get("synthetic_declaration_uses_sorry_warning_declarations") == [] and metric.get("synthetic_trust_clean") is True, "collector synthetic trust mismatch")
    require(metric.get("direct_lean_verified") is True, "collector direct Lean marker missing")

    first = parsed_errors[0] if parsed_errors else None
    first_tuple = (None, None, None, None, None, None) if first is None else (
        first["line"], first["column"], first["declaration"], first["declaration_index"], first["diagnostic_code"], first["message"]
    )
    metric_first = (
        metric.get("FA_first_actual_error_line"), metric.get("FA_first_actual_error_col"), metric.get("FA_first_error_declaration"),
        metric.get("FA_first_error_declaration_index"), metric.get("FA_first_error_code"), metric.get("FA_first_error_message"),
    )
    require(metric_first == first_tuple, "global first actual error mismatch")
    fa_exit = exits["Mock2_FunctionalAnalysis"]
    require_fa_semantic_state(fa_exit, parsed_errors, parsed_warnings, timeout_lines["Mock2_FunctionalAnalysis"])
    require(metric.get("semantic_clean") is (fa_exit == 0), "legacy collector semantic classification mismatch")

    timeout_errors = [row for row in parsed_errors if "timeout" in row["message"].lower()]
    semantic_clean = fa_exit == 0
    dependency_warning_count = sum(header_inventories[stem]["warning_count"] for stem in ("Mock2", "Mock2_Advanced"))
    whole_chain_warning_zero = dependency_warning_count == 0 and len(parsed_warnings) == 0
    current_authority = {
        "repository": REPOSITORY,
        "run_id": args.expected_run_id,
        "run_attempt": args.expected_run_attempt,
        "event_name": envelope["event_name"],
        "ref": args.expected_github_ref,
        "head_sha": args.expected_github_sha,
        "head_tree": checkout_tree,
        "source": source_row,
        "dependencies": dependencies,
        "compiled_products": compiled_products,
        "environment_evidence": environment_evidence,
    }
    artifact_contract = {
        "schema": ARTIFACT_CONTRACT_SCHEMA,
        "official_name_regex": OFFICIAL_NAME_RE.pattern,
        "debug_name_regex": DEBUG_NAME_RE.pattern,
        "deny_name_substring": "incomplete-debug",
        "official_name": official_name,
        "incomplete_debug_name": debug_name,
        "official_name_accepted": official_artifact_name_allowed(official_name),
        "incomplete_debug_name_accepted": official_artifact_name_allowed(debug_name),
        "required_flat_member_count": 38,
        "required_flat_members": sorted(POST_GATE_NAMES),
        "required_final_gate_schema": SCHEMA,
        "accepted_final_gate_statuses": ["EVIDENCE_COMPLETE_FA0", "EVIDENCE_COMPLETE_FA1_FIRST_ERROR"],
    }
    input_inventory = {name: {"sha256": sha256(ordinary(root / name)), "bytes": len(ordinary(root / name))} for name in sorted(PRE_GATE_NAMES)}
    first_payload = {
        "schema": FIRST_ERROR_SCHEMA,
        "present": first is not None,
        "diagnostic": first,
        "global_error_count": len(parsed_errors),
        "source_file_error_count": sum(row["source_file_match"] is True for row in parsed_errors),
        "timeout_error_count": len(timeout_errors),
        "panic_line_count": 0,
    }
    attestation = {
        "schema": ATTESTATION_SCHEMA,
        "status": "EXACT_CURRENT_HEAD_CHECKED_IN_SOURCE_OBSERVED",
        "current_authority": current_authority,
        "activation_baseline": {"expected": BASELINE, "source_match": baseline_match},
        "source_identity": {"capture": source_lock, "before": source_lock, "before_fa": source_lock, "after": source_lock, "observed": source_lock},
        "source_materialized_or_overwritten": False,
        "collector_authority_classification": "LEGACY_NONAUTHORITATIVE_FOR_V66",
        "legacy_collector_authority": LEGACY_AUTHORITY,
        "v66_authority_derived_from_legacy_collector": False,
        "artifact_consumer_contract": artifact_contract,
        "future_source_promotion_requirement": BODY_ONLY_REQUIREMENT,
    }
    final = {
        "schema": SCHEMA,
        "status": "EVIDENCE_COMPLETE_FA0" if semantic_clean else "EVIDENCE_COMPLETE_FA1_FIRST_ERROR",
        "current_authority": current_authority,
        "source_identity": source_lock,
        "source_structure": source_row["structure"],
        "activation_baseline_source_match": baseline_match,
        "wrapper_rc": wrapper_rc,
        "captured_exits": exits,
        "first_actual_error": first,
        "global_error_count": len(parsed_errors),
        "source_file_error_count": sum(row["source_file_match"] is True for row in parsed_errors),
        "warning_count": len(parsed_warnings),
        "dependency_warning_count": dependency_warning_count,
        "dependency_diagnostic_inventories": {stem: header_inventories[stem] for stem in ("Mock2", "Mock2_Advanced")},
        "compiled_products": compiled_products,
        "timeout_error_count": len(timeout_errors),
        "panic_line_count": 0,
        "diagnostic_declaration_ledger_rows": len(declaration_counts),
        "synthetic_sorry_warning_count": 0,
        "source_trust_six": source_row["structure"]["trust_six"],
        "full_diagnostics_complete": True,
        "input_evidence_inventory": input_inventory,
        "official_artifact_consumer_contract": artifact_contract,
        "collector_authority_classification": "LEGACY_NONAUTHORITATIVE_FOR_V66",
        "semantic_clean": semantic_clean,
        "clean_claimed": semantic_clean,
        "clean_claim_scope": "FA_FILE_TRUE_PASS_WITH_ERROR_FREE_DEPENDENCIES_DEPENDENCY_WARNINGS_ALLOWED_AND_RECORDED",
        "whole_chain_warning_zero": whole_chain_warning_zero,
        "whole_chain_clean_claimed": semantic_clean and whole_chain_warning_zero,
        "future_source_promotion_requirement": BODY_ONLY_REQUIREMENT,
        "next_action": "FA_IS_TRUE_PASS_CONTINUE_SEPARATE_13_FILE_WARNING_ZERO_AUDIT" if semantic_clean else "STOP_AND_ADDRESS_ONLY_FIRST_ACTUAL_ERROR",
    }

    outputs = preflight_outputs([root / name for name in GATE_OUTPUT_NAMES], root)
    payloads = [canonical(attestation), canonical(first_payload), canonical(final)]
    for path, payload in zip(outputs, payloads, strict=True):
        write_new(path, payload)
    require_inventory(root, POST_GATE_NAMES, "post-final")
    print(json.dumps(final, ensure_ascii=False, sort_keys=True))
    return 0


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--mode", choices=("capture", "final"), required=True)
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--provenance", type=Path)
    parser.add_argument("--repo-root", type=Path, required=True)
    parser.add_argument("--expected-github-sha", required=True)
    parser.add_argument("--expected-github-ref", required=True)
    parser.add_argument("--expected-run-id", required=True)
    parser.add_argument("--expected-run-attempt", required=True)
    args = parser.parse_args()

    require(HEX40.fullmatch(args.expected_github_sha) is not None, "github SHA malformed")
    require(args.expected_github_ref == BRANCH_REF, "unexpected branch ref")
    require(re.fullmatch(r"[1-9][0-9]*", args.expected_run_id) is not None, "run id malformed")
    require(re.fullmatch(r"[1-9][0-9]*", args.expected_run_attempt) is not None, "run attempt malformed")
    repo, root, source_path = validated_paths(args)
    if args.mode == "capture":
        require(args.provenance is None, "capture mode forbids provenance argument")
        return capture_provenance(args, repo, root, source_path)
    return final_gate(args, repo, root, source_path)


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (AssertionError, KeyError, TypeError, ValueError, OSError, UnicodeError, json.JSONDecodeError) as exc:
        print(f"FAIL-CLOSED: {exc}", file=sys.stderr)
        raise SystemExit(CONTRACT_EXIT)
