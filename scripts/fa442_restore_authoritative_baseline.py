#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
from pathlib import Path

ROOT = Path.cwd()
SOURCE_REL = Path("PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean")
SOURCE = ROOT / SOURCE_REL
EXPECTED_SHA256 = "71dc36f16ebea92d537aa40a5d420443e4bcb93ccb76fea31efb40a6cb5c3aa0"
EXPECTED_LINES = 60453
TARGET_DECLARATION = "actualEdgeAmbientParam_hasDerivAt"
DECL_RE = re.compile(
    r"^(?:protected\s+|private\s+|noncomputable\s+)?"
    r"(?:theorem|lemma|def|abbrev|instance|structure|class)\s+([^\s(:]+)"
)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def line_count(data: bytes) -> int:
    return data.count(b"\n") + (0 if data.endswith(b"\n") else 1)


def run_git(*args: str) -> subprocess.CompletedProcess[bytes]:
    return subprocess.run(
        ["git", *args],
        cwd=ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )


def declaration_header(text: str, name: str) -> str:
    lines = text.splitlines(keepends=True)
    start: int | None = None
    for index, line in enumerate(lines):
        match = DECL_RE.match(line)
        if match and match.group(1) == name:
            start = index
            break
    if start is None:
        raise RuntimeError(f"declaration not found: {name}")
    end = len(lines)
    for index in range(start + 1, len(lines)):
        if DECL_RE.match(lines[index]):
            end = index
            break
    block = "".join(lines[start:end])
    marker = block.find(":= by")
    marker_len = len(":= by")
    if marker < 0:
        marker = block.find(":=")
        marker_len = len(":=")
    if marker < 0:
        raise RuntimeError(f"proof body marker not found: {name}")
    return block[: marker + marker_len]


def candidate_commits() -> list[str]:
    result: list[str] = []
    commands = [
        ("rev-list", "HEAD", "--", str(SOURCE_REL)),
        ("rev-list", "--all", "--", str(SOURCE_REL)),
    ]
    for command in commands:
        proc = run_git(*command)
        if proc.returncode != 0:
            continue
        for raw in proc.stdout.decode("utf-8", errors="replace").splitlines():
            commit = raw.strip()
            if commit and commit not in result:
                result.append(commit)
    return result


def recover() -> tuple[bytes, str, str]:
    current = SOURCE.read_bytes()
    if sha256(current) == EXPECTED_SHA256:
        head = run_git("rev-parse", "HEAD")
        return current, "checked-in-worktree", head.stdout.decode().strip()

    checked = 0
    for commit in candidate_commits():
        proc = run_git("show", f"{commit}:{SOURCE_REL.as_posix()}")
        if proc.returncode != 0:
            continue
        checked += 1
        data = proc.stdout
        if sha256(data) == EXPECTED_SHA256:
            return data, "git-history", commit
    raise RuntimeError(
        "authoritative baseline source was not found in fetched git history; "
        f"searched {checked} historical versions for SHA256 {EXPECTED_SHA256}"
    )


def append_output(values: dict[str, object]) -> None:
    output = os.environ.get("GITHUB_OUTPUT")
    if not output:
        return
    with open(output, "a", encoding="utf-8") as handle:
        for key, value in values.items():
            handle.write(
                f"{key}={str(value).lower() if isinstance(value, bool) else value}\n"
            )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output-dir", required=True)
    args = parser.parse_args()

    output = Path(args.output_dir)
    output.mkdir(parents=True, exist_ok=True)
    before = SOURCE.read_bytes()
    before_sha = sha256(before)
    try:
        data, provenance, provenance_commit = recover()
        recovered_sha = sha256(data)
        recovered_lines = line_count(data)
        if recovered_sha != EXPECTED_SHA256:
            raise RuntimeError(
                f"recovery produced {recovered_sha}, expected {EXPECTED_SHA256}"
            )
        if recovered_lines != EXPECTED_LINES:
            raise RuntimeError(
                f"recovery produced {recovered_lines} lines, expected {EXPECTED_LINES}"
            )
        text = data.decode("utf-8")
        header = declaration_header(text, TARGET_DECLARATION)
        SOURCE.write_bytes(data)
        after = SOURCE.read_bytes()
        result = {
            "classification": "RECOVERED_BASELINE",
            "ok": True,
            "source_path": str(SOURCE_REL),
            "before_sha256": before_sha,
            "source_sha256": sha256(after),
            "line_count": line_count(after),
            "target_declaration": TARGET_DECLARATION,
            "target_header_sha256": sha256(header.encode("utf-8")),
            "provenance": provenance,
            "provenance_commit": provenance_commit,
            "repository_head": run_git("rev-parse", "HEAD").stdout.decode().strip(),
            "expected_sha256": EXPECTED_SHA256,
            "expected_line_count": EXPECTED_LINES,
        }
        (output / "BASELINE_RECOVERY.json").write_text(
            json.dumps(result, indent=2) + "\n", encoding="utf-8"
        )
        (output / "Mock2_FunctionalAnalysis-authoritative-baseline.lean").write_bytes(
            after
        )
        print(json.dumps(result, indent=2))
        append_output(
            {
                "ok": True,
                "source_sha": result["source_sha256"],
                "line_count": result["line_count"],
                "provenance_commit": provenance_commit,
            }
        )
    except Exception as exc:
        result = {
            "classification": "INFRA_FAILURE",
            "ok": False,
            "source_path": str(SOURCE_REL),
            "before_sha256": before_sha,
            "expected_sha256": EXPECTED_SHA256,
            "expected_line_count": EXPECTED_LINES,
            "error": f"{type(exc).__name__}: {exc}",
        }
        (output / "BASELINE_RECOVERY.json").write_text(
            json.dumps(result, indent=2) + "\n", encoding="utf-8"
        )
        (output / "INFRA_FAILURE").write_text(result["error"] + "\n", encoding="utf-8")
        print(json.dumps(result, indent=2))
        append_output({"ok": False, "source_sha": "", "line_count": 0})
        raise


if __name__ == "__main__":
    main()
