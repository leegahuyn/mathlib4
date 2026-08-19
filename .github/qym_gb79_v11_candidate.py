#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import collections
import hashlib
import json
import os
import re
import runpy
import shutil
import subprocess
import sys
import traceback

REPO_QYM = Path("PrimalitySheafVerification/QYM.lean")
FRONTIER = Path(".github/qym-frontier")
BASE_ERRORS = 79
OUT_ROOT = Path(os.environ.get("OUT_ROOT", "/tmp/qym-gb79-v11"))

DIAG_RE = re.compile(
    r"^(?P<file>.*?\.lean):(?P<line>\d+):(?P<column>\d+): "
    r"(?P<severity>error|warning)(?:\((?P<code>[^)]*)\))?:\s*(?P<message>.*)$",
    re.M,
)
PANIC_RE = re.compile(r"(?im)^.*(?:internal error|uncaught exception|panic(?:!|:|\s)).*$")

VARIANTS = {
    "direct",
    "structural",
    "direct_atlas",
    "structural_atlas",
    "direct_atlas_tail_normnum",
    "structural_atlas_tail_simppow",
    "direct_remove_tail_normcast",
    "structural_remove_tail_normnum",
}


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git_blob(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def audit(text: str) -> dict[str, int]:
    return {
        "sorry": len(re.findall(r"\bsorry\b", text)),
        "admit": len(re.findall(r"\badmit\b", text)),
        "native_decide": len(re.findall(r"\bnative_decide\b", text)),
        "Lean.ofReduceBool": text.count("Lean.ofReduceBool"),
        "global_axiom": len(re.findall(r"(?m)^\s*axiom\s+", text)),
        "unsafe": len(re.findall(r"(?m)^\s*unsafe\s+", text)),
        "maxHeartbeats_zero": len(
            re.findall(r"set_option\s+maxHeartbeats\s+0\b", text)
        ),
    }


def load_donor(path: str) -> dict[str, object]:
    p = Path(path)
    if not p.is_file():
        raise RuntimeError(f"missing donor script: {p}")
    return runpy.run_path(str(p), run_name=f"qym_donor_{p.stem}")


def replace_regex_once(
    text: str,
    pattern: re.Pattern[str],
    replacement: str,
    label: str,
    applied: list[str],
    *,
    required: bool,
) -> str:
    matches = list(pattern.finditer(text))
    if len(matches) == 0 and not required:
        return text
    if len(matches) != 1:
        raise RuntimeError(f"{label}: expected one match, found {len(matches)}")
    m = matches[0]
    applied.append(label)
    return text[: m.start()] + replacement.rstrip() + "\n\n" + text[m.end() :]


def replace_exact_optional(
    text: str,
    old: str,
    new: str,
    label: str,
    applied: list[str],
) -> str:
    count = text.count(old)
    if count == 0:
        return text
    if count != 1:
        raise RuntimeError(f"{label}: exact source count is {count}")
    applied.append(label)
    return text.replace(old, new, 1)


def find_authority() -> tuple[Path, dict[str, object], Path]:
    candidates: list[tuple[int, Path, dict[str, object]]] = []
    for p in sorted(FRONTIER.glob("*.json")):
        name = p.name.upper()
        if "RESULT" not in name or ("V10" not in name and "79" not in name):
            continue
        try:
            obj = json.loads(p.read_text(encoding="utf-8"))
        except Exception:
            continue
        if not isinstance(obj, dict):
            continue
        if int(obj.get("error_headers", -1)) != BASE_ERRORS:
            continue
        if int(obj.get("panic_lines", -1)) != 0:
            continue
        source_sha = obj.get("candidate_qym_sha256")
        if not isinstance(source_sha, str) or len(source_sha) != 64:
            continue
        try:
            run_id = int(obj.get("run_id") or 0)
        except Exception:
            run_id = 0
        candidates.append((run_id, p, obj))
    if not candidates:
        raise RuntimeError("no checked-in verified 79-error V10/V10.1 result JSON found")
    candidates.sort(key=lambda row: (row[0], row[1].name), reverse=True)
    _, result_path, result = candidates[0]
    expected_sha = str(result["candidate_qym_sha256"])

    source_paths = [REPO_QYM]
    source_paths.extend(sorted(FRONTIER.glob("QYM*.lean")))
    exact_sources: list[Path] = []
    for source in source_paths:
        if source.is_file() and sha256_bytes(source.read_bytes()) == expected_sha:
            exact_sources.append(source)
    if not exact_sources:
        raise RuntimeError(
            f"verified result exists but exact 79-error source {expected_sha} is absent"
        )
    source = REPO_QYM if REPO_QYM in exact_sources else exact_sources[0]
    return result_path, result, source


def apply_c7_c9(text: str, structural: bool, applied: list[str]) -> str:
    d = load_donor(".github/qym_probe_c7_c9_matrix.py")
    patterns = d["PATTERNS"]
    text = replace_regex_once(text, patterns["c7"], d["C7"], "c7-boundary", applied, required=True)
    c8 = d["C8_STRUCTURAL"] if structural else d["C8_DIRECT"]
    text = replace_regex_once(text, patterns["c8"], c8, "c8-normal-real", applied, required=True)
    text = replace_regex_once(text, patterns["c9"], d["C9"], "c9-normal-im", applied, required=True)
    return text


def apply_atlas(text: str, applied: list[str]) -> str:
    d = load_donor(".github/qym_patch_c10_c13.py")
    text = replace_regex_once(
        text, d["ATLAS_RE"], d["ATLAS_BLOCK"], "c10-c11-atlas", applied, required=True
    )
    text = replace_regex_once(
        text, d["C12_RE"], d["C12"], "c12-fibre-coordinate", applied, required=True
    )
    marker = d["C13_MARKER"]
    insertion = d["C13_INSERT"]
    if insertion.strip() not in text:
        count = text.count(marker)
        if count != 1:
            raise RuntimeError(f"c13 topology marker count is {count}")
        text = text.replace(marker, insertion + marker, 1)
        applied.append("c13-fibre-topology")
    return text


def apply_remove_instances(text: str, structural: bool, applied: list[str]) -> str:
    d = load_donor(".github/qym_probe24_remove_instances.py")
    pairs = [
        ("OLD_OPNORM", "NEW_OPNORM", "remove-opnorm-annotation"),
        ("OLD_HHALF", "NEW_HHALF", "explicit-hhalf-inner-product"),
        ("OLD_GROUP_H", "NEW_GROUP_H", "groupoid-H-as-theorem"),
        ("OLD_GROUP_COMPLEX", "NEW_GROUP_COMPLEX", "groupoid-complex-explicit"),
        ("OLD_GROUP_COMPLEX_END", "NEW_GROUP_COMPLEX_END", "groupoid-complex-omit"),
        ("OLD_MANIFOLD", "NEW_MANIFOLD", "manifold-explicit-instances"),
        ("OLD_INCLUSION", "NEW_INCLUSION", "inclusion-explicit-instances"),
    ]
    for old_key, new_key, label in pairs:
        text = replace_exact_optional(text, d[old_key], d[new_key], label, applied)
    if structural:
        text = replace_exact_optional(
            text, d["OLD_GAMMA"], d["NEW_GAMMA"], "gamma-membership-normalization", applied
        )
    return text


def apply_tail(text: str, coord_variant: str, applied: list[str]) -> str:
    d = load_donor(".github/qym_probe32_tail_matrix.py")
    for index, pair in enumerate(d["COMMON_REPLACEMENTS"], start=1):
        old, new = pair
        text = replace_exact_optional(text, old, new, f"tail-common-{index}", applied)
    old_coord = d["OLD_COORD"]
    coord_map = d["COORD_VARIANTS"]
    if coord_variant not in coord_map:
        raise RuntimeError(f"unknown coordinate variant {coord_variant}")
    text = replace_exact_optional(
        text, old_coord, coord_map[coord_variant], f"tail-coordinate-{coord_variant}", applied
    )
    return text


def materialize_variant(source: Path, variant: str, out_dir: Path) -> tuple[Path, dict[str, object]]:
    before = source.read_bytes()
    text = before.decode("utf-8")
    before_audit = audit(text)
    applied: list[str] = []

    structural = variant.startswith("structural")
    text = apply_c7_c9(text, structural, applied)
    if "remove" in variant:
        text = apply_remove_instances(text, structural, applied)
    if "atlas" in variant:
        text = apply_atlas(text, applied)
    if "tail" in variant:
        if "normnum" in variant:
            coord = "norm-num"
        elif "simppow" in variant:
            coord = "simp-pow"
        elif "normcast" in variant:
            coord = "norm-cast"
        else:
            raise RuntimeError("tail variant lacks coordinate strategy")
        text = apply_tail(text, coord, applied)

    after_audit = audit(text)
    if after_audit != before_audit:
        raise RuntimeError(f"forbidden-token delta: {before_audit} -> {after_audit}")
    if not applied:
        raise RuntimeError("candidate made no source changes")

    candidate = out_dir / f"QYM.candidate-{variant}.lean"
    candidate.write_text(text, encoding="utf-8")
    raw = candidate.read_bytes()
    patch = {
        "schema": "qym-gb79-v11-candidate-v1",
        "variant": variant,
        "input_sha256": sha256_bytes(before),
        "input_blob": git_blob(before),
        "candidate_sha256": sha256_bytes(raw),
        "candidate_blob": git_blob(raw),
        "bytes": len(raw),
        "lf": raw.count(b"\n"),
        "applied": applied,
        "forbidden": after_audit,
    }
    write_json(out_dir / "PATCH_RESULT.json", patch)
    return candidate, patch


def parse_log(log_path: Path) -> tuple[list[dict[str, object]], list[str]]:
    text = log_path.read_text(encoding="utf-8", errors="replace") if log_path.exists() else ""
    rows: list[dict[str, object]] = []
    for match in DIAG_RE.finditer(text):
        row: dict[str, object] = match.groupdict()
        row["line"] = int(row["line"])
        row["column"] = int(row["column"])
        rows.append(row)
    return rows, PANIC_RE.findall(text)


def compile_candidate(candidate: Path, variant: str, out_dir: Path) -> dict[str, object]:
    original = out_dir / "QYM.checked-in.lean"
    shutil.copy2(REPO_QYM, original)
    shutil.copy2(candidate, REPO_QYM)
    log_path = out_dir / "QYM.log"
    time_path = out_dir / "QYM.time"
    olean = out_dir / "QYM.olean"
    ilean = out_dir / "QYM.ilean"
    cmd = [
        "/usr/bin/time", "-v", "-o", str(time_path),
        "lake", "env", "lean",
        "-DmaxErrors=10000", "-DwarningAsError=false",
        "-o", str(olean), "-i", str(ilean), str(REPO_QYM),
    ]
    try:
        with log_path.open("wb") as handle:
            proc = subprocess.run(cmd, stdout=handle, stderr=subprocess.STDOUT)
    finally:
        shutil.copy2(original, REPO_QYM)

    rows, panics = parse_log(log_path)
    errors = [row for row in rows if row["severity"] == "error"]
    warnings = [row for row in rows if row["severity"] == "warning"]
    raw_log = log_path.read_bytes() if log_path.exists() else b""
    semantic_pass = (
        proc.returncode == 0
        and len(errors) == 0
        and len(panics) == 0
        and olean.is_file() and olean.stat().st_size > 0
        and ilean.is_file() and ilean.stat().st_size > 0
    )
    result: dict[str, object] = {
        "schema": "qym-gb79-v11-full-result-v1",
        "variant": variant,
        "phase": "full",
        "baseline_error_headers": BASE_ERRORS,
        "exit": proc.returncode,
        "error_headers": len(errors),
        "warning_headers": len(warnings),
        "panic_lines": len(panics),
        "first_error": errors[0] if errors else None,
        "last_error": errors[-1] if errors else None,
        "error_codes": dict(sorted(collections.Counter(
            str(row.get("code") or "uncoded") for row in errors
        ).items())),
        "candidate_qym_sha256": sha256_bytes(candidate.read_bytes()),
        "candidate_qym_blob": git_blob(candidate.read_bytes()),
        "log_sha256": sha256_bytes(raw_log),
        "olean_exists": olean.is_file() and olean.stat().st_size > 0,
        "ilean_exists": ilean.is_file() and ilean.stat().st_size > 0,
        "olean_sha256": sha256_bytes(olean.read_bytes()) if olean.is_file() else None,
        "ilean_sha256": sha256_bytes(ilean.read_bytes()) if ilean.is_file() else None,
        "semantic_pass": semantic_pass,
        "strict_improvement": semantic_pass or (len(panics) == 0 and len(errors) < BASE_ERRORS),
        "run_id": os.environ.get("GITHUB_RUN_ID"),
        "run_attempt": os.environ.get("GITHUB_RUN_ATTEMPT"),
        "trigger_sha": os.environ.get("GITHUB_SHA"),
    }
    return result


def fatal_result(variant: str, exc: BaseException, out_dir: Path) -> dict[str, object]:
    message = f"{type(exc).__name__}: {exc}"
    (out_dir / "FATAL.txt").write_text(
        message + "\n\n" + traceback.format_exc(), encoding="utf-8"
    )
    return {
        "schema": "qym-gb79-v11-full-result-v1",
        "variant": variant,
        "phase": "fatal",
        "baseline_error_headers": BASE_ERRORS,
        "exit": 99,
        "error_headers": 1000000,
        "warning_headers": 0,
        "panic_lines": 1000000,
        "first_error": {"message": message},
        "last_error": {"message": message},
        "error_codes": {"candidate_generation_failure": 1},
        "candidate_qym_sha256": None,
        "candidate_qym_blob": None,
        "log_sha256": None,
        "olean_exists": False,
        "ilean_exists": False,
        "olean_sha256": None,
        "ilean_sha256": None,
        "semantic_pass": False,
        "strict_improvement": False,
        "run_id": os.environ.get("GITHUB_RUN_ID"),
        "run_attempt": os.environ.get("GITHUB_RUN_ATTEMPT"),
        "trigger_sha": os.environ.get("GITHUB_SHA"),
    }


def main() -> int:
    if len(sys.argv) != 2 or sys.argv[1] not in VARIANTS:
        raise SystemExit(f"usage: {Path(sys.argv[0]).name} VARIANT; variants={sorted(VARIANTS)}")
    variant = sys.argv[1]
    out_dir = OUT_ROOT / variant
    out_dir.mkdir(parents=True, exist_ok=True)
    try:
        result_path, authority, source = find_authority()
        authority_record = {
            "result_file": str(result_path),
            "result": authority,
            "source_file": str(source),
            "source_sha256": sha256_bytes(source.read_bytes()),
            "source_blob": git_blob(source.read_bytes()),
        }
        write_json(out_dir / "AUTHORITY.json", authority_record)
        candidate, patch = materialize_variant(source, variant, out_dir)
        result = compile_candidate(candidate, variant, out_dir)
        result["authority_result_file"] = str(result_path)
        result["authority_source_sha256"] = authority_record["source_sha256"]
        result["applied"] = patch["applied"]
    except BaseException as exc:
        result = fatal_result(variant, exc, out_dir)
    write_json(out_dir / "RESULT.json", result)
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
