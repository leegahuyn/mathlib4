#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import argparse
import collections
import hashlib
import importlib.util
import json
import os
import re
import shutil
import subprocess
import sys
from typing import Any, Iterable

QYM = Path(os.environ.get("QYM", "PrimalitySheafVerification/QYM.lean"))
FRONTIER = Path(".github/qym-frontier")
OUT = Path(os.environ.get("OUT", "/tmp/qym-gb79-v11"))
BASE_ERRORS = 79
LOCAL_MAX_ERRORS = 8
DIAG_RE = re.compile(
    r"^(?P<file>.*?\.lean):(?P<line>\d+):(?P<column>\d+): "
    r"(?P<severity>error|warning)(?:\((?P<code>[^)]*)\))?:\s*(?P<message>.*)$",
    re.M,
)
PANIC_RE = re.compile(r"(?im)^.*(?:internal error|uncaught exception|panic(?:!|:|\s)).*$")
PAIR_SCRIPTS = [
    "qym_probe24_remove_instances.py",
    "qym_probe27_infer_opnorm.py",
    "qym_probe28_explicit_sinf_opnorm.py",
    "qym_probe29_placeholder_opnorm.py",
    "qym_probe30_producer_matrix.py",
    "qym_probe31_horocycle_matrix.py",
    "qym_probe32_tail_matrix.py",
    "qym_probe33_opnorm_instance_matrix.py",
    "qym_probe34_compact_resolvent.py",
    "qym_probe34_opnorm_friedrichs.py",
    "qym_probe35_custom_sinf_norm.py",
    "qym_probe35_hhalf_matrix.py",
    "qym_probe37_explicit_sinf.py",
    "qym_probe38_groupoid.py",
    "qym_probe39_gamma_two.py",
    "qym_probe39i_gamma_two.py",
    "qym_probe41_gamma2.py",
    "qym_probe42_adaptive.py",
    "qym_probe43_gamma.py",
    "qym_probe44_gamma_chain.py",
    "qym_probe44b_gamma_conjunction.py",
    "qym_probe45_cusp_contdiff.py",
]


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_path(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def git_blob(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def write_json(path: Path, value: Any) -> None:
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
        "maxHeartbeats_zero": len(re.findall(r"set_option\s+maxHeartbeats\s+0\b", text)),
    }


def result_rows(obj: Any, result_file: Path) -> Iterable[dict[str, Any]]:
    if not isinstance(obj, dict):
        return
    candidates: list[dict[str, Any]] = []
    if isinstance(obj.get("error_headers"), int):
        candidates.append(obj)
    for key in ("best", "result", "full"):
        row = obj.get(key)
        if isinstance(row, dict) and isinstance(row.get("error_headers"), int):
            candidates.append(row)
    for row in candidates:
        enriched = dict(row)
        enriched["_result_file"] = str(result_file)
        yield enriched


def find_authority() -> tuple[Path, dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for path in sorted(FRONTIER.glob("*.json")):
        try:
            obj = json.loads(path.read_text(encoding="utf-8"))
        except Exception:
            continue
        for row in result_rows(obj, path):
            try:
                errors = int(row.get("error_headers", -1))
                panic = int(row.get("panic_lines", -1))
            except Exception:
                continue
            candidate_sha = row.get("candidate_qym_sha256") or row.get("qym_sha256")
            run_id = row.get("run_id")
            phase = row.get("phase")
            if errors != BASE_ERRORS or panic != 0 or not candidate_sha or run_id is None:
                continue
            if phase not in (None, "full"):
                continue
            rows.append(row)
    if not rows:
        raise RuntimeError("no committed full-QYM 79-error result with panic=0 was found")

    def run_rank(row: dict[str, Any]) -> int:
        try:
            return int(str(row.get("run_id")))
        except Exception:
            return -1

    rows.sort(key=run_rank, reverse=True)
    result = rows[0]
    expected_sha = str(result.get("candidate_qym_sha256") or result.get("qym_sha256"))
    sources = [QYM] + sorted(FRONTIER.glob("*.lean"), reverse=True)
    matches = [p for p in sources if p.is_file() and sha256_path(p) == expected_sha]
    if not matches:
        raise RuntimeError(f"79-error result exists but no committed source matches SHA256 {expected_sha}")
    source = matches[0]
    authority = {
        "schema": "qym-gb79-authority-v1",
        "result": result,
        "source": str(source),
        "source_sha256": expected_sha,
        "source_blob": git_blob(source.read_bytes()),
        "verified_conditions": {
            "error_headers_79": int(result["error_headers"]) == BASE_ERRORS,
            "panic_zero": int(result["panic_lines"]) == 0,
            "run_id_present": result.get("run_id") is not None,
            "log_sha256_present": bool(result.get("log_sha256")),
            "source_sha_match": sha256_path(source) == expected_sha,
        },
    }
    if not all(authority["verified_conditions"].values()):
        raise RuntimeError(f"79 authority gate failed: {authority['verified_conditions']}")
    write_json(OUT / "AUTHORITY.json", authority)
    return source, result


def load_module(path: Path):
    if not path.is_file():
        return None
    name = "qym_dynamic_" + hashlib.sha1(str(path).encode()).hexdigest()
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        return None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def replace_exact(text: str, old: str, new: str, label: str, applied: list[str]) -> str:
    if not isinstance(old, str) or not isinstance(new, str) or old == new or not old:
        return text
    count = text.count(old)
    if count == 1:
        text = text.replace(old, new, 1)
        applied.append(label)
    return text


def replace_regex(text: str, pattern: re.Pattern[str], replacement: str, label: str,
                  applied: list[str]) -> str:
    matches = list(pattern.finditer(text))
    if len(matches) != 1:
        return text
    match = matches[0]
    old = match.group(0)
    if old.strip() == replacement.strip():
        return text
    applied.append(label)
    return text[:match.start()] + replacement.rstrip() + "\n\n" + text[match.end():]


def module_pairs(module: Any) -> list[tuple[str, str, str]]:
    pairs: list[tuple[str, str, str]] = []
    common = getattr(module, "COMMON_REPLACEMENTS", None)
    if isinstance(common, (list, tuple)):
        for index, item in enumerate(common):
            if isinstance(item, (list, tuple)) and len(item) == 2 and all(isinstance(x, str) for x in item):
                pairs.append((item[0], item[1], f"COMMON_REPLACEMENTS[{index}]"))
    values = vars(module)
    for name, old in values.items():
        if not name.startswith("OLD_") or not isinstance(old, str):
            continue
        new_name = "NEW_" + name[4:]
        new = values.get(new_name)
        if isinstance(new, str) and new:
            pairs.append((old, new, name[4:]))
    unique: list[tuple[str, str, str]] = []
    seen: set[tuple[str, str]] = set()
    for old, new, label in pairs:
        key = (old, new)
        if key not in seen:
            seen.add(key)
            unique.append((old, new, label))
    return unique


def apply_generic_pairs(text: str, descending: bool, applied: list[str]) -> str:
    names = list(PAIR_SCRIPTS)
    if descending:
        names.reverse()
    for script in names:
        path = Path(".github") / script
        try:
            module = load_module(path)
        except Exception:
            continue
        if module is None:
            continue
        pairs = module_pairs(module)
        pairs.sort(key=lambda item: len(item[0]), reverse=True)
        for old, new, label in pairs:
            text = replace_exact(text, old, new, f"{script}:{label}", applied)
    return text


def apply_c7_c9(text: str, structural: bool, applied: list[str]) -> str:
    path = Path(".github/qym_probe_c7_c9_matrix.py")
    module = load_module(path)
    if module is None:
        return text
    replacements = {
        "c7": getattr(module, "C7", ""),
        "c8": getattr(module, "C8_STRUCTURAL" if structural else "C8_DIRECT", ""),
        "c9": getattr(module, "C9", ""),
    }
    patterns = getattr(module, "PATTERNS", {})
    for key in ("c7", "c8", "c9"):
        pattern = patterns.get(key) if isinstance(patterns, dict) else None
        replacement = replacements[key]
        if isinstance(pattern, re.Pattern) and isinstance(replacement, str) and replacement:
            text = replace_regex(text, pattern, replacement, f"c7_c9:{key}:{'structural' if structural else 'direct'}", applied)
    return text


def apply_c10_c13(text: str, applied: list[str]) -> str:
    module = load_module(Path(".github/qym_patch_c10_c13.py"))
    if module is None:
        return text
    atlas_re = getattr(module, "ATLAS_RE", None)
    atlas_block = getattr(module, "ATLAS_BLOCK", "")
    c12_re = getattr(module, "C12_RE", None)
    c12 = getattr(module, "C12", "")
    if isinstance(atlas_re, re.Pattern) and atlas_block:
        text = replace_regex(text, atlas_re, atlas_block, "c10_c13:atlas", applied)
    if isinstance(c12_re, re.Pattern) and c12:
        text = replace_regex(text, c12_re, c12, "c10_c13:fibre_reconstruction", applied)
    marker = getattr(module, "C13_MARKER", "")
    insertion = getattr(module, "C13_INSERT", "")
    if marker and insertion and insertion.strip() not in text and text.count(marker) == 1:
        text = text.replace(marker, insertion + marker, 1)
        applied.append("c10_c13:fibre_topology")
    return text


def apply_tail(text: str, coordinate_variant: str, applied: list[str]) -> str:
    module = load_module(Path(".github/qym_probe32_tail_matrix.py"))
    if module is None:
        return text
    common = getattr(module, "COMMON_REPLACEMENTS", [])
    if isinstance(common, (list, tuple)):
        for index, item in enumerate(common):
            if isinstance(item, (list, tuple)) and len(item) == 2:
                text = replace_exact(text, item[0], item[1], f"tail:common:{index}", applied)
    old_coord = getattr(module, "OLD_COORD", "")
    variants = getattr(module, "COORD_VARIANTS", {})
    new_coord = variants.get(coordinate_variant) if isinstance(variants, dict) else None
    if isinstance(old_coord, str) and isinstance(new_coord, str):
        text = replace_exact(text, old_coord, new_coord, f"tail:coordinate:{coordinate_variant}", applied)
    return text


def patch_variant(source: Path, destination: Path, variant: str) -> dict[str, Any]:
    before_raw = source.read_bytes()
    text = before_raw.decode("utf-8")
    before_audit = audit(text)
    applied: list[str] = []

    if variant == "geometry_direct":
        text = apply_c7_c9(text, False, applied)
    elif variant == "geometry_structural":
        text = apply_c7_c9(text, True, applied)
    elif variant == "atlas":
        text = apply_c10_c13(text, applied)
    elif variant == "atlas_pairs_desc":
        text = apply_c10_c13(text, applied)
        text = apply_generic_pairs(text, True, applied)
    elif variant == "tail_norm_num":
        text = apply_tail(text, "norm-num", applied)
    elif variant == "tail_simp_pow":
        text = apply_tail(text, "simp-pow", applied)
    elif variant == "tail_norm_cast":
        text = apply_tail(text, "norm-cast", applied)
    elif variant == "pairs_desc":
        text = apply_generic_pairs(text, True, applied)
    elif variant == "pairs_asc":
        text = apply_generic_pairs(text, False, applied)
    elif variant == "mega_direct_desc":
        text = apply_c7_c9(text, False, applied)
        text = apply_c10_c13(text, applied)
        text = apply_tail(text, "norm-num", applied)
        text = apply_generic_pairs(text, True, applied)
    elif variant == "mega_structural_asc":
        text = apply_c7_c9(text, True, applied)
        text = apply_c10_c13(text, applied)
        text = apply_tail(text, "simp-pow", applied)
        text = apply_generic_pairs(text, False, applied)
    else:
        raise ValueError(f"unknown patch variant {variant}")

    after_audit = audit(text)
    if after_audit != before_audit:
        raise RuntimeError(f"{variant}: forbidden-token delta {before_audit} -> {after_audit}")
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(text, encoding="utf-8")
    after_raw = destination.read_bytes()
    manifest = {
        "schema": "qym-gb79-v11-patch-v1",
        "variant": variant,
        "input_sha256": sha256_bytes(before_raw),
        "candidate_sha256": sha256_bytes(after_raw),
        "candidate_blob": git_blob(after_raw),
        "bytes": len(after_raw),
        "lf": after_raw.count(b"\n"),
        "changed": before_raw != after_raw,
        "applied": applied,
        "forbidden": after_audit,
    }
    write_json(destination.with_suffix(".PATCH.json"), manifest)
    return manifest


def parse_log(log_path: Path) -> tuple[list[dict[str, Any]], list[str]]:
    raw = log_path.read_bytes() if log_path.exists() else b""
    text = raw.decode(errors="replace")
    rows: list[dict[str, Any]] = []
    for match in DIAG_RE.finditer(text):
        row: dict[str, Any] = match.groupdict()
        row["line"] = int(row["line"])
        row["column"] = int(row["column"])
        rows.append(row)
    return rows, PANIC_RE.findall(text)


def compile_candidate(candidate: Path, label: str, phase: str, max_errors: int) -> dict[str, Any]:
    shutil.copy2(candidate, QYM)
    safe = re.sub(r"[^A-Za-z0-9_.-]+", "_", label)
    log_path = OUT / f"{safe}.{phase}.log"
    olean = OUT / f"{safe}.{phase}.olean"
    ilean = OUT / f"{safe}.{phase}.ilean"
    cmd = [
        "lake", "env", "lean", f"-DmaxErrors={max_errors}", "-DwarningAsError=false",
        "-o", str(olean), "-i", str(ilean), str(QYM),
    ]
    with log_path.open("wb") as handle:
        proc = subprocess.run(cmd, stdout=handle, stderr=subprocess.STDOUT)
    rows, panics = parse_log(log_path)
    errors = [row for row in rows if row["severity"] == "error"]
    warnings = [row for row in rows if row["severity"] == "warning"]
    result = {
        "label": label,
        "phase": phase,
        "exit": proc.returncode,
        "error_headers": len(errors),
        "warning_headers": len(warnings),
        "panic_lines": len(panics),
        "first_error": errors[0] if errors else None,
        "last_error": errors[-1] if errors else None,
        "error_codes": dict(sorted(collections.Counter(str(row.get("code") or "uncoded") for row in errors).items())),
        "candidate_qym_sha256": sha256_path(candidate),
        "candidate_qym_blob": git_blob(candidate.read_bytes()),
        "log_sha256": sha256_path(log_path),
        "olean_exists": olean.is_file() and olean.stat().st_size > 0,
        "ilean_exists": ilean.is_file() and ilean.stat().st_size > 0,
        "run_id": os.environ.get("GITHUB_RUN_ID"),
        "trigger_sha": os.environ.get("GITHUB_SHA"),
    }
    write_json(OUT / f"{safe}.{phase}.json", result)
    return result


def first_line(result: dict[str, Any]) -> int:
    first = result.get("first_error") or {}
    try:
        return int(first.get("line"))
    except Exception:
        return 10**9


def prepare_candidates(source: Path, destination: Path) -> dict[str, Any]:
    destination.mkdir(parents=True, exist_ok=True)
    variants = [
        "geometry_direct", "geometry_structural", "atlas", "atlas_pairs_desc",
        "tail_norm_num", "tail_simp_pow", "tail_norm_cast", "pairs_desc", "pairs_asc",
        "mega_direct_desc", "mega_structural_asc",
    ]
    rows = []
    for variant in variants:
        candidate = destination / f"QYM.candidate-{variant}.lean"
        manifest = patch_variant(source, candidate, variant)
        rows.append(manifest)
    summary = {
        "schema": "qym-gb79-v12-preparation-v1",
        "authority_sha256": sha256_path(source),
        "candidate_count": len(rows),
        "changed_candidate_count": sum(1 for row in rows if row["changed"]),
        "candidates": rows,
    }
    write_json(destination / "PREPARED.json", summary)
    return summary


def run_pipeline() -> int:
    OUT.mkdir(parents=True, exist_ok=True)
    checked_in = OUT / "QYM.checked-in.lean"
    shutil.copy2(QYM, checked_in)
    try:
        authority_source, authority_result = find_authority()
        frozen = OUT / "QYM.GB79.lean"
        shutil.copy2(authority_source, frozen)
        current_source = frozen
        current_result = dict(authority_result)
        current_errors = int(current_result["error_headers"])
        baseline_sha = sha256_path(frozen)
        history: list[dict[str, Any]] = []

        stages = [
            ("V11_geometry", ["geometry_direct", "geometry_structural"], 2),
            ("V12_atlas", ["atlas", "atlas_pairs_desc"], 1),
            ("V13_tail", ["tail_norm_num", "tail_simp_pow", "tail_norm_cast"], 1),
            ("V14_historical", ["pairs_desc", "pairs_asc"], 1),
            ("V15_mega_fallback", ["mega_direct_desc", "mega_structural_asc"], 1),
        ]

        for stage_name, variants, full_limit in stages:
            if current_errors == 0:
                break
            stage_rows: list[dict[str, Any]] = []
            for index, variant in enumerate(variants):
                candidate = OUT / f"{stage_name}.candidate-{variant}.lean"
                manifest = patch_variant(current_source, candidate, variant)
                if not manifest["changed"]:
                    stage_rows.append({"variant": variant, "priority": index, "patch": manifest, "unchanged": True})
                    continue
                local = compile_candidate(candidate, f"{stage_name}-{variant}", "local", LOCAL_MAX_ERRORS)
                stage_rows.append({
                    "variant": variant, "priority": index, "candidate": str(candidate),
                    "patch": manifest, "local": local, "unchanged": False,
                })

            viable = [row for row in stage_rows if not row.get("unchanged") and int(row["local"]["panic_lines"]) == 0]
            viable.sort(key=lambda row: (-first_line(row["local"]), int(row["local"]["error_headers"]), int(row["priority"])))
            full_rows: list[dict[str, Any]] = []
            for row in viable[:full_limit]:
                candidate = Path(str(row["candidate"]))
                full = compile_candidate(candidate, f"{stage_name}-{row['variant']}", "full", 10000)
                full["baseline_error_headers"] = current_errors
                semantic_pass = (
                    int(full["exit"]) == 0 and int(full["error_headers"]) == 0 and
                    int(full["panic_lines"]) == 0 and bool(full["olean_exists"]) and bool(full["ilean_exists"])
                )
                strict = semantic_pass or (
                    int(full["panic_lines"]) == 0 and int(full["error_headers"]) < current_errors
                )
                full["semantic_pass"] = semantic_pass
                full["strict_improvement"] = strict
                row["full"] = full
                full_rows.append(row)

            improved = [row for row in full_rows if bool(row["full"]["strict_improvement"])]
            improved.sort(key=lambda row: (int(row["full"]["error_headers"]), -first_line(row["full"]), int(row["priority"])))
            stage_record: dict[str, Any] = {
                "stage": stage_name,
                "input_error_headers": current_errors,
                "input_sha256": sha256_path(current_source),
                "candidates": stage_rows,
                "strict_improvement_found": bool(improved),
            }
            if improved:
                best = improved[0]
                current_source = Path(str(best["candidate"]))
                current_result = dict(best["full"])
                current_errors = int(current_result["error_headers"])
                stage_record["best_variant"] = best["variant"]
                stage_record["best"] = current_result
            history.append(stage_record)
            write_json(OUT / f"{stage_name}.SELECTION.json", stage_record)

        final_semantic = (
            int(current_result.get("exit", 1)) == 0 and current_errors == 0 and
            int(current_result.get("panic_lines", 1)) == 0 and
            bool(current_result.get("olean_exists")) and bool(current_result.get("ilean_exists"))
        )
        final = dict(current_result)
        final.update({
            "schema": "qym-gb79-v11-final-v1",
            "baseline_error_headers": BASE_ERRORS,
            "baseline_qym_sha256": baseline_sha,
            "error_headers": current_errors,
            "semantic_pass": final_semantic,
            "strict_improvement": final_semantic or current_errors < BASE_ERRORS,
            "candidate_qym_sha256": sha256_path(current_source),
            "candidate_qym_blob": git_blob(current_source.read_bytes()),
            "pipeline_stages": [row["stage"] for row in history],
        })
        selection = {
            "schema": "qym-gb79-v11-selection-v1",
            "authority_result": authority_result,
            "baseline_sha256": baseline_sha,
            "baseline_error_headers": BASE_ERRORS,
            "final": final,
            "history": history,
        }
        write_json(OUT / "FINAL_RESULT.json", final)
        write_json(OUT / "SELECTION.json", selection)
        if bool(final["strict_improvement"]):
            shutil.copy2(current_source, OUT / "QYM.best.lean")
            return 0
        return 2
    finally:
        if checked_in.exists():
            shutil.copy2(checked_in, QYM)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("mode", choices=("run", "prepare"), nargs="?", default="run")
    parser.add_argument("--prepare-out", default="/tmp/qym-gb79-v12-prep")
    args = parser.parse_args()
    OUT.mkdir(parents=True, exist_ok=True)
    source, _ = find_authority()
    if args.mode == "prepare":
        prepare_candidates(source, Path(args.prepare_out))
        return 0
    return run_pipeline()


if __name__ == "__main__":
    raise SystemExit(main())
