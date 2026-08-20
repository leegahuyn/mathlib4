#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import importlib.util
import json
import os
import re
import subprocess
import sys
from pathlib import Path
from typing import Any

ROOT = Path.cwd()
VARIANT = os.environ.get("VARIANT", "unknown")
OUT = Path(
    os.environ.get(
        "FA442_OUT_DIR",
        f"build-logs/fa442-pipeline-repair/candidates/{VARIANT}",
    )
)
SOURCE = Path(
    os.environ.get(
        "FA442_SOURCE",
        "PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean",
    )
)
METADATA_PATH = Path(
    os.environ.get("FA442_METADATA", str(OUT / "CANDIDATE.json"))
)
EXPECTED_LINES = int(os.environ.get("FA442_EXPECTED_LINES", "60453"))
EXPECTED_BASELINE_SHA = (
    "71dc36f16ebea92d537aa40a5d420443e4bcb93ccb76fea31efb40a6cb5c3aa0"
)
TARGET_DECLARATION = "actualEdgeAmbientParam_hasDerivAt"
DECL_RE = re.compile(
    r"^(?:protected\s+|private\s+|noncomputable\s+)?"
    r"(?:theorem|lemma|def|abbrev|instance|structure|class)\s+([^\s(:]+)"
)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def line_count(data: bytes) -> int:
    return data.count(b"\n") + (0 if data.endswith(b"\n") else 1)


def read_text(path: Path) -> str:
    return path.read_text(encoding="utf-8", errors="replace") if path.exists() else ""


def read_int(path: Path, default: int = 125) -> int:
    try:
        return int(read_text(path).strip())
    except (TypeError, ValueError):
        return default


def run_text(*args: str) -> str:
    proc = subprocess.run(
        list(args),
        cwd=ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        check=False,
    )
    return proc.stdout.strip() if proc.returncode == 0 else ""


def declarations(text: str) -> list[dict[str, Any]]:
    result: list[dict[str, Any]] = []
    for line_number, line in enumerate(text.splitlines(), start=1):
        match = DECL_RE.match(line)
        if match:
            result.append({"name": match.group(1), "line": line_number})
    return result


def declaration_at(
    declaration_rows: list[dict[str, Any]], line_number: int
) -> tuple[str, int, int]:
    if line_number <= 0:
        return "<none>", -1, 0
    current_name = "<unknown>"
    current_index = -1
    current_line = 0
    for index, row in enumerate(declaration_rows):
        row_line = int(row["line"])
        if row_line > line_number:
            break
        current_name = str(row["name"])
        current_index = index
        current_line = row_line
    return current_name, current_index, current_line


def declaration_header(text: str, name: str) -> str:
    lines = text.splitlines(keepends=True)
    start: int | None = None
    for index, line in enumerate(lines):
        match = DECL_RE.match(line)
        if match and match.group(1) == name:
            start = index
            break
    if start is None:
        return ""
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
    return block[: marker + marker_len] if marker >= 0 else ""


def parse_errors(stem: str) -> dict[str, Any]:
    log_path = OUT / f"{stem}.log"
    log = read_text(log_path)
    pattern = re.compile(
        rf"(?m)^(?P<prefix>.*?{re.escape(stem)}\.lean):"
        r"(?P<line>\d+):(?P<col>\d+):\s+error:\s*(?P<message>.*)$"
    )
    matches = list(pattern.finditer(log))
    first_line = int(matches[0].group("line")) if matches else 0
    first_col = int(matches[0].group("col")) if matches else 0
    message = ""
    if matches:
        start = matches[0].start("message")
        end = matches[1].start() if len(matches) > 1 else len(log)
        chunk = log[start:end]
        continuation: list[str] = []
        for index, raw in enumerate(chunk.splitlines()):
            if index > 0 and re.match(
                r"^.*\.lean:\d+:\d+:\s+(?:error|warning):", raw
            ):
                break
            continuation.append(raw.rstrip())
            if len("\n".join(continuation)) >= 2000:
                break
        message = "\n".join(continuation).strip()[:2000]
    return {
        "error_headers_captured": len(matches),
        "first_line": first_line,
        "first_col": first_col,
        "first_message": message,
        "log_path": str(log_path),
    }


def load_forbidden_counts(text: str) -> dict[str, int]:
    script = ROOT / "scripts/fa442_prepare_same_height_candidate.py"
    try:
        spec = importlib.util.spec_from_file_location("fa442_prepare_for_audit", script)
        if spec is None or spec.loader is None:
            raise RuntimeError("cannot load audit helper")
        module = importlib.util.module_from_spec(spec)
        sys.modules[spec.name] = module
        spec.loader.exec_module(module)
        return dict(module.forbidden_counts(text))
    except Exception:
        code = text
        patterns = {
            "sorry": r"\bsorry\b",
            "admit": r"\badmit\b",
            "new_global_axiom": r"(?m)^\s*(?:protected\s+|private\s+)?axiom\b",
            "unsafe": r"\bunsafe\b",
            "native_decide": r"\bnative_decide\b",
            "Lean.ofReduceBool": r"\bLean\.ofReduceBool\b",
        }
        return {key: len(re.findall(pattern, code)) for key, pattern in patterns.items()}


def marker(stem: str, suffix: str) -> Path:
    return OUT / f"{stem}.{suffix}"


def main() -> None:
    OUT.mkdir(parents=True, exist_ok=True)
    infra_reasons: list[str] = []

    if SOURCE.exists():
        source_data = SOURCE.read_bytes()
        source_text = source_data.decode("utf-8", errors="replace")
    else:
        source_data = b""
        source_text = ""
        infra_reasons.append(f"source missing: {SOURCE}")

    try:
        metadata = json.loads(METADATA_PATH.read_text(encoding="utf-8"))
    except Exception as exc:
        metadata = {}
        infra_reasons.append(
            f"candidate metadata unavailable: {type(exc).__name__}: {exc}"
        )

    source_sha = sha256(source_data) if source_data else ""
    source_lines = line_count(source_data) if source_data else 0
    metadata_sha = str(metadata.get("candidate_sha256", ""))
    source_metadata_identity = bool(source_sha and source_sha == metadata_sha)
    if not source_metadata_identity:
        infra_reasons.append(
            f"source/metadata SHA mismatch: source={source_sha} metadata={metadata_sha}"
        )
    if source_lines != EXPECTED_LINES:
        infra_reasons.append(
            f"line count {source_lines} does not equal required {EXPECTED_LINES}"
        )

    declaration_rows = declarations(source_text)
    declaration_sequence = [str(row["name"]) for row in declaration_rows]
    declaration_sequence_sha = sha256(
        json.dumps(
            declaration_sequence, ensure_ascii=False, separators=(",", ":")
        ).encode("utf-8")
    )
    target_header = declaration_header(source_text, TARGET_DECLARATION)
    target_header_sha = sha256(target_header.encode("utf-8")) if target_header else ""
    expected_header_sha = str(metadata.get("target_header_sha256", ""))
    if not target_header:
        infra_reasons.append(f"target declaration header missing: {TARGET_DECLARATION}")
    elif expected_header_sha and target_header_sha != expected_header_sha:
        infra_reasons.append(
            "target theorem statement/header changed: "
            f"actual={target_header_sha} expected={expected_header_sha}"
        )

    target_declaration_index = next(
        (
            index
            for index, row in enumerate(declaration_rows)
            if row["name"] == TARGET_DECLARATION
        ),
        -1,
    )

    stems = ("Mock2", "Mock2_Advanced", "Mock2_FunctionalAnalysis")
    exits = {stem: read_int(marker(stem, "exit")) for stem in stems}
    executed = {stem: marker(stem, "executed").exists() for stem in stems}
    commands = {stem: read_text(marker(stem, "command")).strip() for stem in stems}
    for stem in stems:
        if not executed[stem]:
            infra_reasons.append(f"direct Lean CLI not executed for {stem}")
        if not commands[stem]:
            infra_reasons.append(f"exact compile command missing for {stem}")

    toolchain_install_exit = read_int(OUT / "toolchain-install.exit", default=125)
    cache_get_exit = read_int(OUT / "cache-get.exit", default=125)
    if toolchain_install_exit != 0:
        infra_reasons.append(
            f"pinned Lean toolchain installation failed: {toolchain_install_exit}"
        )
    if cache_get_exit != 0:
        infra_reasons.append(f"lake exe cache get failed: {cache_get_exit}")

    fa_errors = parse_errors("Mock2_FunctionalAnalysis")
    m2_errors = parse_errors("Mock2")
    m2a_errors = parse_errors("Mock2_Advanced")
    first_declaration, first_declaration_index, first_declaration_line = declaration_at(
        declaration_rows, int(fa_errors["first_line"])
    )

    if executed["Mock2_FunctionalAnalysis"] and exits["Mock2_FunctionalAnalysis"] != 0:
        if int(fa_errors["error_headers_captured"]) == 0:
            infra_reasons.append(
                "FA Lean process failed without a parseable Lean error header"
            )

    audit = (
        load_forbidden_counts(source_text)
        if source_text
        else {
            "sorry": -1,
            "admit": -1,
            "new_global_axiom": -1,
            "unsafe": -1,
            "native_decide": -1,
            "Lean.ofReduceBool": -1,
        }
    )
    forbidden_clean = all(value == 0 for value in audit.values())
    if not forbidden_clean:
        infra_reasons.append(f"forbidden trust audit failed: {audit}")

    baseline_audit = metadata.get("baseline_forbidden_counts", {})
    forbidden_not_increased = all(
        int(audit.get(key, 0)) <= int(baseline_audit.get(key, 0))
        for key in baseline_audit
    )
    if baseline_audit and not forbidden_not_increased:
        infra_reasons.append("candidate forbidden-token count increased from baseline")

    head_source_sha = ""
    head_source = subprocess.run(
        ["git", "show", f"HEAD:{SOURCE.as_posix()}"],
        cwd=ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if head_source.returncode == 0:
        head_source_sha = sha256(head_source.stdout)

    lean_executed = executed["Mock2_FunctionalAnalysis"]
    all_required_lean_executed = all(executed.values())
    fa_exit = exits["Mock2_FunctionalAnalysis"]
    if infra_reasons:
        classification = "INFRA_FAILURE"
    elif exits["Mock2"] != 0 or exits["Mock2_Advanced"] != 0:
        classification = "LEAN_FAILURE"
    elif fa_exit == 0:
        classification = "FA_PASS_CANDIDATE"
    else:
        classification = "LEAN_FAILURE"

    metric: dict[str, Any] = {
        "classification": classification,
        "authority": "direct Lean CLI on repository source path",
        "variant": VARIANT,
        "source_path": str(SOURCE),
        "source_sha256": source_sha,
        "candidate_metadata_sha256": metadata_sha,
        "source_metadata_identity": source_metadata_identity,
        "head_source_sha256_before_candidate_materialization": head_source_sha,
        "baseline_sha256_required": EXPECTED_BASELINE_SHA,
        "line_count": source_lines,
        "required_line_count": EXPECTED_LINES,
        "target_declaration": TARGET_DECLARATION,
        "target_declaration_index": target_declaration_index,
        "target_header_sha256": target_header_sha,
        "metadata_target_header_sha256": expected_header_sha,
        "declaration_count": len(declaration_rows),
        "declaration_sequence_sha256": declaration_sequence_sha,
        "lean_executed": lean_executed,
        "all_required_lean_executed": all_required_lean_executed,
        "Mock2_executed": executed["Mock2"],
        "Mock2_exit": exits["Mock2"],
        "Mock2_errors_under_cap": m2_errors["error_headers_captured"],
        "Mock2_Advanced_executed": executed["Mock2_Advanced"],
        "Mock2_Advanced_exit": exits["Mock2_Advanced"],
        "Mock2_Advanced_errors_under_cap": m2a_errors["error_headers_captured"],
        "FA_executed": executed["Mock2_FunctionalAnalysis"],
        "FA_exit": fa_exit,
        "FA_error_headers_captured": fa_errors["error_headers_captured"],
        "FA_first_actual_error_line": fa_errors["first_line"],
        "FA_first_actual_error_col": fa_errors["first_col"],
        "FA_first_error_message": fa_errors["first_message"],
        "FA_first_error_declaration": first_declaration,
        "FA_error_declaration_index": first_declaration_index,
        "FA_error_declaration_start_line": first_declaration_line,
        "exact_compile_commands": commands,
        "maxErrors_cap": int(os.environ.get("MAX_ERRORS", "50")),
        "maxErrors_interpretation": (
            "diagnostic cap only; not total errors and not proof-progress evidence"
        ),
        "lean_version": read_text(OUT / "lean-version.txt").strip(),
        "lake_version": read_text(OUT / "lake-version.txt").strip(),
        "lean_toolchain": read_text(ROOT / "lean-toolchain").strip(),
        "toolchain_install_exit": toolchain_install_exit,
        "cache_get_exit": cache_get_exit,
        "repository_head": run_text("git", "rev-parse", "HEAD"),
        "repository_tree": run_text("git", "rev-parse", "HEAD^{tree}"),
        "lake_manifest_sha256": (
            sha256((ROOT / "lake-manifest.json").read_bytes())
            if (ROOT / "lake-manifest.json").exists()
            else ""
        ),
        "candidate_forbidden_counts": audit,
        "baseline_forbidden_counts": baseline_audit,
        "forbidden_not_increased": forbidden_not_increased,
        "forbidden_clean": forbidden_clean,
        "repairs": metadata.get("repairs", []),
        "infra_reasons": infra_reasons,
    }

    (OUT / "METRIC.json").write_text(
        json.dumps(metric, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )
    (OUT / "METRIC.txt").write_text(
        "\n".join(f"{key}={value}" for key, value in metric.items()) + "\n",
        encoding="utf-8",
    )
    print(json.dumps(metric, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
