#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import time
import traceback
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterable

ROOT = Path(__file__).resolve().parents[1]
EVIDENCE = ROOT / ".final_authority"
LOGS = EVIDENCE / "logs"

REPOSITORY = "leegahuyn/mathlib4"
AUTHORITY_BRANCH = "gpt/final-authority-gb0-canonical-20260820"
BASE_COMMIT = "af501c4355561cfdb5e264bc2ec0d0eb79e4e435"
PINNED_TOOLCHAIN = "leanprover/lean4:v4.33.0-rc1"

QYM_PATH = Path("PrimalitySheafVerification/QYM.lean")
QYM_SHA256 = "ab7c394f68b812046bcfae109b274a2d4fa42479bf8e76461c73a9c190fb3204"
QYM_BLOB = "7afb309d7c4da97da7bc6b922931734d72830d41"
QYM_ORIGINAL_RUN = 32341941077
QYM_REPLAY_RUN = 32344604895

FA_PATH = Path("PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean")
FA_BLOB = "28f614d48e02a0f28d3f5a758e813350b3ea89cf"
INTEGRATED_PATH = Path("PrimalitySheafVerification/Mock2_FunctionalAnalysis_Integrated.lean")
INTEGRATED_BLOB = "464f5dd095876b20165d12690c8127ef9d909e6a"
MOCK3_PATH = Path("PrimalitySheafVerification/Mock3.lean")
BUILDALL_PATH = Path("PrimalitySheafVerification/BuildAll.lean")

ROOTS: list[tuple[int, Path, str]] = [
    (1, Path("PrimalitySheafVerification/Spt1.lean"), "PrimalitySheafVerification.Spt1"),
    (2, Path("PrimalitySheafVerification/Spt2.lean"), "PrimalitySheafVerification.Spt2"),
    (3, Path("PrimalitySheafVerification/Spt3.lean"), "PrimalitySheafVerification.Spt3"),
    (4, Path("PrimalitySheafVerification/Spt4.lean"), "PrimalitySheafVerification.Spt4"),
    (5, Path("PrimalitySheafVerification/Spt5.lean"), "PrimalitySheafVerification.Spt5"),
    (6, Path("PrimalitySheafVerification/Spt6.lean"), "PrimalitySheafVerification.Spt6"),
    (7, Path("PrimalitySheafVerification/Spt7.lean"), "PrimalitySheafVerification.Spt7"),
    (8, Path("PrimalitySheafVerification/Mock1.lean"), "PrimalitySheafVerification.Mock1"),
    (9, Path("PrimalitySheafVerification/Mock1_Advanced.lean"), "PrimalitySheafVerification.Mock1_Advanced"),
    (10, Path("PrimalitySheafVerification/Mock2.lean"), "PrimalitySheafVerification.Mock2"),
    (11, Path("PrimalitySheafVerification/Mock2_Advanced.lean"), "PrimalitySheafVerification.Mock2_Advanced"),
    (12, FA_PATH, "PrimalitySheafVerification.Mock2_FunctionalAnalysis"),
    (13, QYM_PATH, "PrimalitySheafVerification.QYM"),
]
BRIDGES: list[tuple[str, Path, str]] = [
    ("Integrated", INTEGRATED_PATH, "PrimalitySheafVerification.Mock2_FunctionalAnalysis_Integrated"),
    ("Mock3", MOCK3_PATH, "PrimalitySheafVerification.Mock3"),
]
BUILDALL_MODULE = "PrimalitySheafVerification.BuildAll"

REQUIRED_REPORT_NAMES = [
    "QYM_GB0_LOCK_RESULT.json",
    "QYM_CANONICAL_REPLAY_RESULT.json",
    "MOCK3_CANONICAL_RESULT.json",
    "FINAL_13_ROOTS.txt",
    "FINAL_13_BUILD_RESULTS.json",
    "BUILDALL_RESULT.json",
    "CLEAN_BUILD_1_RESULT.json",
    "CLEAN_BUILD_2_RESULT.json",
    "FINAL_15_CHECKLIST_RESULT.json",
    "FINAL_SOURCE_IDENTITY.json",
    "FINAL_STATUS_CARD.md",
    "FINAL_TRUE_PASS_REPORT.md",
]

DIAGNOSTIC_RE = re.compile(
    r"^(?P<file>.*?\.lean):(?P<line>\d+):(?P<column>\d+): "
    r"(?P<severity>error|warning)(?:\((?P<code>[^)]*)\))?:\s*(?P<message>.*)$",
    re.MULTILINE,
)
DECL_RE = re.compile(
    r"^\s*(?:(?:private|protected|noncomputable|local)\s+)*"
    r"(?:theorem|lemma|def|abbrev|opaque|instance|structure|class|inductive)\s+"
    r"([^\s(:{]+)"
)

STATE: dict[str, Any] = {
    "started_at_utc": datetime.now(timezone.utc).isoformat(),
    "stages": {},
    "first_failure": None,
}


def ensure_dirs() -> None:
    EVIDENCE.mkdir(parents=True, exist_ok=True)
    LOGS.mkdir(parents=True, exist_ok=True)


def json_write(name: str, value: Any) -> None:
    (EVIDENCE / name).write_text(
        json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )


def text_write(name: str, value: str) -> None:
    (EVIDENCE / name).write_text(value, encoding="utf-8")


def git(*args: str, check: bool = True) -> str:
    p = subprocess.run(
        ["git", *args],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if check and p.returncode != 0:
        raise RuntimeError(f"git {' '.join(args)} failed: {p.stderr.strip()}")
    return p.stdout.strip()


def command_text(args: Iterable[str]) -> str:
    return " ".join(subprocess.list2cmdline([str(x)]) for x in args)


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def blob_for(path: Path) -> str:
    return git("hash-object", "--no-filters", str(path))


def count_lines(raw: bytes) -> int:
    if not raw:
        return 0
    return raw.count(b"\n") + (0 if raw.endswith(b"\n") else 1)


def fingerprint(path: Path) -> dict[str, Any]:
    full = ROOT / path
    raw = full.read_bytes()
    return {
        "path": str(path),
        "module": module_for_path(path),
        "sha256": hashlib.sha256(raw).hexdigest(),
        "git_blob": blob_for(path),
        "bytes": len(raw),
        "lines": count_lines(raw),
        "is_symlink": full.is_symlink(),
    }


def module_for_path(path: Path) -> str:
    return str(path.with_suffix("")).replace(os.sep, ".").replace("/", ".")


def path_for_module(module: str) -> Path:
    return Path(*module.split(".")).with_suffix(".lean")


def parse_imports(path: Path) -> list[str]:
    text = (ROOT / path).read_text(encoding="utf-8")
    imports: list[str] = []
    for line in text.splitlines():
        m = re.match(r"^\s*import\s+(.+?)\s*$", line)
        if not m:
            continue
        body = m.group(1).split("--", 1)[0]
        for token in body.split():
            token = token.strip()
            if re.fullmatch(r"[A-Za-z0-9_'.]+", token):
                imports.append(token)
    return imports


def local_imports(path: Path) -> list[str]:
    return [x for x in parse_imports(path) if x.startswith("PrimalitySheafVerification.")]


def build_graph(target_modules: Iterable[str]) -> tuple[list[Path], dict[str, list[str]], list[str]]:
    graph: dict[str, list[str]] = {}
    missing: list[str] = []
    visiting: set[str] = set()
    visited: set[str] = set()
    order: list[Path] = []

    def visit(module: str) -> None:
        if module in visited:
            return
        if module in visiting:
            raise RuntimeError(f"local import cycle at {module}")
        visiting.add(module)
        path = path_for_module(module)
        if not (ROOT / path).is_file():
            missing.append(module)
            visiting.remove(module)
            return
        deps = local_imports(path)
        graph[module] = deps
        for dep in deps:
            visit(dep)
        visiting.remove(module)
        visited.add(module)
        order.append(path)

    for target in target_modules:
        visit(target)
    return order, graph, sorted(set(missing))


def strip_lean_comments_and_strings(text: str) -> str:
    out: list[str] = []
    i = 0
    block_depth = 0
    line_comment = False
    in_string = False
    escaped = False
    while i < len(text):
        c = text[i]
        n = text[i + 1] if i + 1 < len(text) else ""
        if line_comment:
            if c == "\n":
                line_comment = False
                out.append("\n")
            else:
                out.append(" ")
            i += 1
            continue
        if block_depth:
            if c == "/" and n == "-":
                block_depth += 1
                out.extend((" ", " "))
                i += 2
            elif c == "-" and n == "/":
                block_depth -= 1
                out.extend((" ", " "))
                i += 2
            else:
                out.append("\n" if c == "\n" else " ")
                i += 1
            continue
        if in_string:
            if escaped:
                escaped = False
                out.append(" ")
            elif c == "\\":
                escaped = True
                out.append(" ")
            elif c == '"':
                in_string = False
                out.append(" ")
            else:
                out.append("\n" if c == "\n" else " ")
            i += 1
            continue
        if c == "-" and n == "-":
            line_comment = True
            out.extend((" ", " "))
            i += 2
        elif c == "/" and n == "-":
            block_depth = 1
            out.extend((" ", " "))
            i += 2
        elif c == '"':
            in_string = True
            out.append(" ")
            i += 1
        else:
            out.append(c)
            i += 1
    return "".join(out)


def source_audit(paths: list[Path]) -> dict[str, Any]:
    forbidden_patterns = {
        "sorry": re.compile(r"\bsorry\b"),
        "admit": re.compile(r"\badmit\b"),
        "axiom_declaration": re.compile(r"(?m)^\s*axiom\s+"),
        "native_decide": re.compile(r"\bnative_decide\b"),
        "Lean.ofReduceBool": re.compile(r"\bLean\.ofReduceBool\b"),
        "unsafe_declaration": re.compile(r"(?m)^\s*unsafe\s+"),
        "maxHeartbeats_zero": re.compile(r"set_option\s+maxHeartbeats\s+0\b"),
        "fake_pass_marker": re.compile(r"(?i)\b(?:fake[_ -]?pass|placeholder|temporary[_ -]?assumption)\b"),
    }
    diagnostic_patterns = {
        "#check": re.compile(r"(?m)^\s*#check\b"),
        "#print": re.compile(r"(?m)^\s*#print\b"),
        "#eval": re.compile(r"(?m)^\s*#eval\b"),
        "#reduce": re.compile(r"(?m)^\s*#reduce\b"),
        "#synth": re.compile(r"(?m)^\s*#synth\b"),
    }
    files: list[dict[str, Any]] = []
    forbidden_total = 0
    control_total = 0
    prose_prefix_failures = 0
    for path in paths:
        raw = (ROOT / path).read_bytes()
        text = raw.decode("utf-8", errors="strict")
        code = strip_lean_comments_and_strings(text)
        forbidden = {name: len(p.findall(code)) for name, p in forbidden_patterns.items()}
        diagnostics = {name: len(p.findall(code)) for name, p in diagnostic_patterns.items()}
        controls = [
            {"offset": i, "byte": b}
            for i, b in enumerate(raw)
            if b < 32 and b not in (9, 10, 13)
        ]
        prefix = code.lstrip()
        prefix_ok = (
            not prefix
            or prefix.startswith(
                (
                    "import ",
                    "prelude",
                    "set_option ",
                    "namespace ",
                    "section",
                    "open ",
                    "universe ",
                    "variable ",
                    "noncomputable ",
                    "private ",
                    "protected ",
                    "theorem ",
                    "lemma ",
                    "def ",
                    "abbrev ",
                    "structure ",
                    "class ",
                    "inductive ",
                    "instance ",
                )
            )
        )
        forbidden_total += sum(forbidden.values())
        control_total += len(controls)
        prose_prefix_failures += int(not prefix_ok)
        files.append(
            {
                "path": str(path),
                "forbidden": forbidden,
                "diagnostic_commands": diagnostics,
                "control_characters": controls[:50],
                "prose_prefix_ok": prefix_ok,
            }
        )
    return {
        "files": files,
        "forbidden_count": forbidden_total,
        "control_character_count": control_total,
        "prose_prefix_failures": prose_prefix_failures,
        "pass": forbidden_total == 0 and control_total == 0 and prose_prefix_failures == 0,
        "policy": {
            "warnings": "counted and preserved; nonzero ordinary warnings do not override the current GB0 authority",
            "forbidden": "sorry/admit/project axiom/native_decide/Lean.ofReduceBool/unsafe proof escape/maxHeartbeats 0/fake-pass markers must be zero",
        },
    }


def diagnostics_from_log(log_path: Path) -> dict[str, Any]:
    text = log_path.read_text(encoding="utf-8", errors="replace") if log_path.exists() else ""
    rows: list[dict[str, Any]] = []
    for m in DIAGNOSTIC_RE.finditer(text):
        d = m.groupdict()
        d["line"] = int(d["line"])
        d["column"] = int(d["column"])
        rows.append(d)
    errors = [x for x in rows if x["severity"] == "error"]
    warnings = [x for x in rows if x["severity"] == "warning"]
    panic_lines = [
        line for line in text.splitlines()
        if re.search(r"(?i)(internal error|uncaught exception|panic!|:\s*panic(?:\s|:))", line)
    ]
    sorry_lines = [
        line for line in text.splitlines()
        if re.search(r"(?i)(declaration uses ['`]?sorry|sorryAx)", line)
    ]
    return {
        "error_headers": len(errors),
        "warning_headers": len(warnings),
        "panic_lines": len(panic_lines),
        "sorry_warning_lines": len(sorry_lines),
        "first_error": errors[0] if errors else None,
        "last_error": errors[-1] if errors else None,
        "panic_samples": panic_lines[:20],
        "sorry_warning_samples": sorry_lines[:20],
    }


def nearest_declaration(path: Path, line_number: int | None) -> str | None:
    if not line_number or not (ROOT / path).exists():
        return None
    lines = (ROOT / path).read_text(encoding="utf-8", errors="replace").splitlines()
    for line in reversed(lines[:line_number]):
        m = DECL_RE.match(line)
        if m:
            return m.group(1)
    return None


def object_paths(path: Path) -> tuple[Path, Path]:
    rel = path.with_suffix("")
    base = ROOT / ".lake/build/lib/lean" / rel
    return base.with_suffix(".olean"), base.with_suffix(".ilean")


def clear_objects(paths: Iterable[Path]) -> list[str]:
    removed: list[str] = []
    for path in paths:
        for obj in object_paths(path):
            if obj.exists():
                obj.unlink()
                removed.append(str(obj.relative_to(ROOT)))
    return removed


def compile_one(path: Path, stage: str) -> dict[str, Any]:
    stage_dir = LOGS / stage
    stage_dir.mkdir(parents=True, exist_ok=True)
    safe_name = str(path.with_suffix("")).replace("/", "__")
    log_path = stage_dir / f"{safe_name}.log"
    olean, ilean = object_paths(path)
    olean.parent.mkdir(parents=True, exist_ok=True)
    for obj in (olean, ilean):
        if obj.exists():
            obj.unlink()
    max_errors = "10000" if path in (QYM_PATH, FA_PATH) else "2000"
    cmd = [
        "lake",
        "env",
        "lean",
        f"-DmaxErrors={max_errors}",
        "-DwarningAsError=false",
        "-o",
        str(olean.relative_to(ROOT)),
        "-i",
        str(ilean.relative_to(ROOT)),
        str(path),
    ]
    print(f"::group::{stage}: {path}", flush=True)
    print(command_text(cmd), flush=True)
    started = time.monotonic()
    with log_path.open("wb") as log:
        proc = subprocess.run(cmd, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
    elapsed = round(time.monotonic() - started, 3)
    diag = diagnostics_from_log(log_path)
    first = diag.get("first_error")
    blocker = nearest_declaration(path, first.get("line") if first else None)
    result = {
        "path": str(path),
        "module": module_for_path(path),
        "source_sha256": sha256_file(ROOT / path),
        "source_git_blob": blob_for(path),
        "command": command_text(cmd),
        "exit": proc.returncode,
        **diag,
        "blocker_declaration": blocker,
        "elapsed_seconds": elapsed,
        "olean_generated": olean.is_file() and olean.stat().st_size > 0,
        "ilean_generated": ilean.is_file() and ilean.stat().st_size > 0,
        "olean_sha256": sha256_file(olean) if olean.is_file() else None,
        "ilean_sha256": sha256_file(ilean) if ilean.is_file() else None,
        "log_path": str(log_path.relative_to(ROOT)),
    }
    result["pass"] = (
        result["exit"] == 0
        and result["error_headers"] == 0
        and result["panic_lines"] == 0
        and result["sorry_warning_lines"] == 0
        and result["olean_generated"]
        and result["ilean_generated"]
    )
    if not result["pass"] and STATE["first_failure"] is None:
        STATE["first_failure"] = {
            "stage": stage,
            "path": str(path),
            "first_error": result["first_error"],
            "blocker_declaration": blocker,
            "exit": result["exit"],
            "lean_actually_ran": True,
            "classification": "actual Lean compile failure",
        }
    print(json.dumps({k: result[k] for k in (
        "path", "exit", "error_headers", "warning_headers", "panic_lines",
        "sorry_warning_lines", "blocker_declaration", "elapsed_seconds", "pass"
    )}, ensure_ascii=False), flush=True)
    print("::endgroup::", flush=True)
    return result


def compile_sequence(stage: str, paths: list[Path], clean_first: bool) -> dict[str, Any]:
    protection_before = verify_protected(f"{stage}:before")
    removed = clear_objects(paths) if clean_first else []
    results: list[dict[str, Any]] = []
    stopped = False
    for path in paths:
        if stopped:
            results.append(
                {
                    "path": str(path),
                    "module": module_for_path(path),
                    "status": "NOT_RUN",
                    "reason": "upstream actual Lean failure",
                    "pass": False,
                }
            )
            continue
        result = compile_one(path, stage)
        results.append(result)
        if not result["pass"]:
            stopped = True
    protection_after = verify_protected(f"{stage}:after")
    return {
        "stage": stage,
        "clean_first": clean_first,
        "removed_objects": removed,
        "removed_object_count": len(removed),
        "results": results,
        "pass": (
            protection_before["pass"]
            and protection_after["pass"]
            and bool(results)
            and all(x.get("pass") is True for x in results)
        ),
        "protected_before": protection_before,
        "protected_after": protection_after,
    }


def verify_protected(label: str) -> dict[str, Any]:
    qym = fingerprint(QYM_PATH) if (ROOT / QYM_PATH).is_file() else None
    fa = fingerprint(FA_PATH) if (ROOT / FA_PATH).is_file() else None
    integrated = fingerprint(INTEGRATED_PATH) if (ROOT / INTEGRATED_PATH).is_file() else None
    result = {
        "label": label,
        "qym": qym,
        "fa": fa,
        "integrated": integrated,
    }
    result["pass"] = bool(
        qym
        and fa
        and integrated
        and qym["sha256"] == QYM_SHA256
        and qym["git_blob"] == QYM_BLOB
        and fa["git_blob"] == FA_BLOB
        and integrated["git_blob"] == INTEGRATED_BLOB
    )
    if not result["pass"] and STATE["first_failure"] is None:
        STATE["first_failure"] = {
            "stage": label,
            "path": str(QYM_PATH),
            "first_error": None,
            "blocker_declaration": None,
            "exit": None,
            "lean_actually_ran": False,
            "classification": "source identity regression",
        }
    return result


def result_for_path(sequence: dict[str, Any], path: Path) -> dict[str, Any] | None:
    for result in sequence.get("results", []):
        if result.get("path") == str(path):
            return result
    return None


def skipped_result(stage: str, reason: str) -> dict[str, Any]:
    return {
        "stage": stage,
        "status": "NOT_RUN",
        "reason": reason,
        "pass": False,
        "results": [],
    }


def run_git_diff_check() -> dict[str, Any]:
    cmd = ["git", "diff", "--check", f"{BASE_COMMIT}..HEAD"]
    p = subprocess.run(cmd, cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    return {
        "command": command_text(cmd),
        "exit": p.returncode,
        "output": p.stdout,
        "pass": p.returncode == 0 and not p.stdout.strip(),
    }


def tracked_temporary_audit() -> dict[str, Any]:
    tracked = git("ls-files").splitlines()
    changed = set(git("diff", "--name-only", f"{BASE_COMMIT}..HEAD").splitlines())
    bad: list[str] = []
    for name in tracked:
        if name not in changed:
            continue
        lower = name.lower()
        base = Path(name).name.lower()
        if lower.endswith((".olean", ".ilean", ".log", ".tmp")):
            bad.append(name)
        elif re.search(r"(?:^|[/_-])(?:probe|segment)(?:[/_.-]|$)", lower) and lower.endswith(".lean"):
            bad.append(name)
        elif base.endswith((".bak", ".backup", "~")):
            bad.append(name)
    return {"changed_tracked_bad_paths": sorted(set(bad)), "pass": not bad}


def changed_paths_audit(source_commit: str) -> dict[str, Any]:
    changed = [
        x for x in git("diff", "--name-only", f"{BASE_COMMIT}..{source_commit}").splitlines()
        if x
    ]
    allowed = {
        "PrimalitySheafVerification/Mock3.lean",
        "PrimalitySheafVerification/BuildAll.lean",
        "scripts/final_authority_gate.py",
        ".github/workflows/gpt-final-authority-gb0-canonical.yml",
    }
    unexpected = sorted(set(changed) - allowed)
    root_changes = sorted(
        set(changed)
        & {str(path) for _, path, _ in ROOTS}
    )
    return {
        "base_commit": BASE_COMMIT,
        "source_commit": source_commit,
        "changed_paths": changed,
        "allowed_paths": sorted(allowed),
        "unexpected_paths": unexpected,
        "primary_root_changes": root_changes,
        "pass": not unexpected and not root_changes,
    }


def make_manifest(
    root_fingerprints: list[dict[str, Any]],
    bridge_fingerprints: list[dict[str, Any]],
    graph: dict[str, list[str]],
    source_commit: str,
) -> str:
    lines = [
        "# FINAL_13_ROOTS.txt",
        f"# repository={REPOSITORY}",
        f"# branch={os.environ.get('GITHUB_REF_NAME', git('branch', '--show-current'))}",
        f"# source_commit={source_commit}",
        "# exact_primary_root_count=13",
        "index\tcanonical_path\tlogical_module\tsha256\tgit_blob\tbytes\tlines\tlocal_dependencies",
    ]
    by_path = {x["path"]: x for x in root_fingerprints}
    for index, path, module in ROOTS:
        fp = by_path[str(path)]
        deps = ",".join(graph.get(module, [])) or "-"
        lines.append(
            f"{index}\t{path}\t{module}\t{fp['sha256']}\t{fp['git_blob']}\t"
            f"{fp['bytes']}\t{fp['lines']}\t{deps}"
        )
    lines += [
        "",
        "# mandatory bridges (not counted in the primary 13)",
        "name\tcanonical_path\tlogical_module\tsha256\tgit_blob\tbytes\tlines\tlocal_dependencies",
    ]
    by_bridge = {x["path"]: x for x in bridge_fingerprints}
    for name, path, module in BRIDGES:
        fp = by_bridge[str(path)]
        deps = ",".join(graph.get(module, [])) or "-"
        lines.append(
            f"{name}\t{path}\t{module}\t{fp['sha256']}\t{fp['git_blob']}\t"
            f"{fp['bytes']}\t{fp['lines']}\t{deps}"
        )
    return "\n".join(lines) + "\n"


def summarize_counts(sequence: dict[str, Any], paths: list[Path]) -> dict[str, int]:
    counts = {"PASS": 0, "FAIL": 0, "SKIPPED": 0, "NOT_RUN": 0}
    for path in paths:
        result = result_for_path(sequence, path)
        if result is None or result.get("status") == "NOT_RUN":
            counts["NOT_RUN"] += 1
        elif result.get("status") == "SKIPPED":
            counts["SKIPPED"] += 1
        elif result.get("pass"):
            counts["PASS"] += 1
        else:
            counts["FAIL"] += 1
    return counts


def compile_result_summary(sequence: dict[str, Any]) -> dict[str, Any]:
    errors = sum(int(x.get("error_headers", 0)) for x in sequence.get("results", []))
    warnings = sum(int(x.get("warning_headers", 0)) for x in sequence.get("results", []))
    panic = sum(int(x.get("panic_lines", 0)) for x in sequence.get("results", []))
    sorry = sum(int(x.get("sorry_warning_lines", 0)) for x in sequence.get("results", []))
    return {
        "pass": sequence.get("pass", False),
        "errors": errors,
        "warnings": warnings,
        "panic": panic,
        "sorry_warnings": sorry,
    }


def checklist_item(
    number: int,
    requirement: str,
    check: str,
    source_commit: str,
    passed: bool,
    evidence: str,
    detail: Any = None,
) -> dict[str, Any]:
    return {
        "item_number": number,
        "exact_requirement": requirement,
        "command_or_check": check,
        "source_commit": source_commit,
        "result": detail,
        "evidence_path": evidence,
        "status": "PASS" if passed else "FAIL",
    }


def main() -> int:
    ensure_dirs()
    source_commit = git("rev-parse", "HEAD")
    branch = os.environ.get("GITHUB_REF_NAME") or git("branch", "--show-current")
    run_id = os.environ.get("GITHUB_RUN_ID")
    run_attempt = os.environ.get("GITHUB_RUN_ATTEMPT")
    run_url = f"https://github.com/{REPOSITORY}/actions/runs/{run_id}" if run_id else None

    tracked_status = git("status", "--porcelain=v1", "--untracked-files=no")
    toolchain = (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip()
    lean_version = subprocess.check_output(["lean", "--version"], cwd=ROOT, text=True).strip()
    lake_version = subprocess.check_output(["lake", "--version"], cwd=ROOT, text=True).strip()
    lake_manifest_sha = sha256_file(ROOT / "lake-manifest.json")
    commit_subject = git("show", "-s", "--format=%s", source_commit)
    commit_date = git("show", "-s", "--format=%cI", source_commit)
    remote_url = git("remote", "get-url", "origin")

    lock = verify_protected("QYM_GB0_LOCK")
    lock.update(
        {
            "repository": REPOSITORY,
            "branch": branch,
            "source_commit": source_commit,
            "expected_qym_sha256": QYM_SHA256,
            "expected_qym_git_blob": QYM_BLOB,
            "original_direct_lean_run": QYM_ORIGINAL_RUN,
            "previous_independent_replay_run": QYM_REPLAY_RUN,
            "lean_version": lean_version,
            "lake_version": lake_version,
            "toolchain": toolchain,
        }
    )
    json_write("QYM_GB0_LOCK_RESULT.json", lock)
    if (ROOT / QYM_PATH).is_file():
        shutil.copy2(ROOT / QYM_PATH, EVIDENCE / "QYM_GB0_TRUE_PASS.lean")

    all_declared_paths = [path for _, path, _ in ROOTS] + [p for _, p, _ in BRIDGES] + [BUILDALL_PATH]
    existence = {
        str(path): {
            "exists": (ROOT / path).is_file(),
            "is_symlink": (ROOT / path).is_symlink(),
        }
        for path in all_declared_paths
    }
    root_count_ok = len(ROOTS) == 13
    all_exist = all(x["exists"] and not x["is_symlink"] for x in existence.values())
    unique_paths = len({str(p) for _, p, _ in ROOTS}) == 13
    unique_modules = len({m for _, _, m in ROOTS}) == 13

    targets = [m for _, _, m in ROOTS] + [m for _, _, m in BRIDGES] + [BUILDALL_MODULE]
    topo_order, graph, missing_imports = build_graph(targets)
    direct_buildall_imports = set(local_imports(BUILDALL_PATH))
    required_buildall_imports = {m for _, _, m in ROOTS} | {m for _, _, m in BRIDGES}
    buildall_missing = sorted(required_buildall_imports - direct_buildall_imports)

    root_fps = [fingerprint(path) for _, path, _ in ROOTS]
    bridge_fps = [fingerprint(path) for _, path, _ in BRIDGES]
    buildall_fp = fingerprint(BUILDALL_PATH)
    manifest = make_manifest(root_fps, bridge_fps, graph, source_commit)
    text_write("FINAL_13_ROOTS.txt", manifest)

    audit_paths = [path for _, path, _ in ROOTS] + [p for _, p, _ in BRIDGES] + [BUILDALL_PATH]
    forbidden_audit = source_audit(audit_paths)
    json_write("FORBIDDEN_AUDIT.json", forbidden_audit)
    diff_check = run_git_diff_check()
    temp_audit = tracked_temporary_audit()
    changed_audit = changed_paths_audit(source_commit)

    graph_result = {
        "target_modules": targets,
        "topological_compile_order": [str(x) for x in topo_order],
        "graph": graph,
        "missing_local_imports": missing_imports,
        "buildall_direct_imports": sorted(direct_buildall_imports),
        "buildall_required_imports": sorted(required_buildall_imports),
        "buildall_missing_required_imports": buildall_missing,
        "pass": not missing_imports and not buildall_missing,
    }
    json_write("SOURCE_GRAPH.json", graph_result)

    preflight = {
        "repository": REPOSITORY,
        "remote_url": remote_url,
        "branch": branch,
        "source_commit": source_commit,
        "commit_subject": commit_subject,
        "commit_date": commit_date,
        "tracked_status": tracked_status,
        "toolchain": toolchain,
        "toolchain_expected": PINNED_TOOLCHAIN,
        "lean_version": lean_version,
        "lake_version": lake_version,
        "lake_manifest_sha256": lake_manifest_sha,
        "root_count": len(ROOTS),
        "root_count_ok": root_count_ok,
        "all_paths_exist_and_are_canonical_files": all_exist,
        "unique_paths": unique_paths,
        "unique_modules": unique_modules,
        "existence": existence,
        "graph": graph_result,
        "forbidden_audit": forbidden_audit,
        "diff_check": diff_check,
        "temporary_file_audit": temp_audit,
        "changed_paths_audit": changed_audit,
        "github_run_id": run_id,
        "github_run_attempt": run_attempt,
        "github_run_url": run_url,
    }
    preflight["pass"] = bool(
        not tracked_status
        and branch == AUTHORITY_BRANCH
        and toolchain == PINNED_TOOLCHAIN
        and root_count_ok
        and all_exist
        and unique_paths
        and unique_modules
        and graph_result["pass"]
        and forbidden_audit["pass"]
        and diff_check["pass"]
        and temp_audit["pass"]
        and changed_audit["pass"]
        and lock["pass"]
    )
    json_write("PREFLIGHT.json", preflight)

    qym_replay: dict[str, Any]
    mock3_result: dict[str, Any]
    final13: dict[str, Any]
    buildall: dict[str, Any]
    clean1: dict[str, Any]
    clean2: dict[str, Any]

    if preflight["pass"]:
        qym_order, _, qym_missing = build_graph(["PrimalitySheafVerification.QYM"])
        if qym_missing:
            qym_replay = skipped_result("QYM_CANONICAL_REPLAY", f"missing local imports: {qym_missing}")
        else:
            qym_sequence = compile_sequence("qym_canonical_replay", qym_order, clean_first=False)
            qym_result = result_for_path(qym_sequence, QYM_PATH)
            qym_replay = {
                **qym_sequence,
                "source_commit": source_commit,
                "canonical_qym_result": qym_result,
                "expected_sha256": QYM_SHA256,
                "expected_git_blob": QYM_BLOB,
                "pass": bool(qym_sequence["pass"] and qym_result and qym_result.get("pass")),
            }
    else:
        qym_replay = skipped_result("QYM_CANONICAL_REPLAY", "preflight or immutable lock failed")
    json_write("QYM_CANONICAL_REPLAY_RESULT.json", qym_replay)

    if qym_replay.get("pass"):
        mock3_compile = compile_sequence("mock3_canonical", [MOCK3_PATH], clean_first=False)
        mock3_leaf = result_for_path(mock3_compile, MOCK3_PATH)
        mock3_result = {
            **mock3_compile,
            "canonical_path": str(MOCK3_PATH),
            "relationship_to_qym": "transparent checked-in bridge importing the frozen canonical QYM module",
            "qym_source_identity_after": verify_protected("MOCK3:QYM_RECHECK"),
            "canonical_result": mock3_leaf,
            "pass": bool(
                mock3_compile["pass"]
                and mock3_leaf
                and mock3_leaf.get("pass")
                and verify_protected("MOCK3:FINAL_QYM_RECHECK")["pass"]
            ),
        }
    else:
        mock3_result = skipped_result("MOCK3_CANONICAL", "QYM canonical replay did not pass")
    json_write("MOCK3_CANONICAL_RESULT.json", mock3_result)

    support_targets = [m for _, _, m in ROOTS] + [m for _, _, m in BRIDGES]
    support_order, _, support_missing = build_graph(support_targets)
    if mock3_result.get("pass") and not support_missing:
        final13_sequence = compile_sequence("final13_actual_lean", support_order, clean_first=False)
        counts = summarize_counts(final13_sequence, [p for _, p, _ in ROOTS])
        bridge_counts = summarize_counts(final13_sequence, [p for _, p, _ in BRIDGES])
        final13 = {
            **final13_sequence,
            "root_count": 13,
            "counts": counts,
            "bridge_counts": bridge_counts,
            "manifest_verified": True,
            "pass": bool(
                final13_sequence["pass"]
                and counts == {"PASS": 13, "FAIL": 0, "SKIPPED": 0, "NOT_RUN": 0}
                and bridge_counts["PASS"] == len(BRIDGES)
                and bridge_counts["FAIL"] == 0
                and bridge_counts["SKIPPED"] == 0
                and bridge_counts["NOT_RUN"] == 0
            ),
        }
    else:
        final13 = skipped_result(
            "FINAL13_ACTUAL_LEAN",
            f"Mock3 did not pass or local imports missing: {support_missing}",
        )
        final13["counts"] = {"PASS": 0, "FAIL": 0, "SKIPPED": 0, "NOT_RUN": 13}
        final13["bridge_counts"] = {"PASS": 0, "FAIL": 0, "SKIPPED": 0, "NOT_RUN": len(BRIDGES)}
        final13["manifest_verified"] = not support_missing
    json_write("FINAL_13_BUILD_RESULTS.json", final13)

    if final13.get("pass"):
        buildall_sequence = compile_sequence("buildall", [BUILDALL_PATH], clean_first=False)
        buildall_leaf = result_for_path(buildall_sequence, BUILDALL_PATH)
        buildall = {
            **buildall_sequence,
            "aggregate_command": buildall_leaf.get("command") if buildall_leaf else None,
            "targets_included": sorted(direct_buildall_imports),
            "required_targets": sorted(required_buildall_imports),
            "required_skipped_targets": buildall_missing,
            "aggregate_result": buildall_leaf,
            "pass": bool(
                buildall_sequence["pass"]
                and buildall_leaf
                and buildall_leaf.get("pass")
                and not buildall_missing
            ),
        }
    else:
        buildall = skipped_result("BUILDALL", "Final13 13/13 gate did not pass")
        buildall["required_skipped_targets"] = buildall_missing
    json_write("BUILDALL_RESULT.json", buildall)

    full_order, _, full_missing = build_graph([BUILDALL_MODULE])
    if buildall.get("pass") and not full_missing:
        clean1 = compile_sequence("clean_build_1", full_order, clean_first=True)
        clean1["source_commit"] = source_commit
        clean1["qym_golden_hash_unchanged"] = verify_protected("CLEAN1:QYM_FINAL")["pass"]
        clean1["pass"] = bool(clean1["pass"] and clean1["qym_golden_hash_unchanged"])
    else:
        clean1 = skipped_result("CLEAN_BUILD_1", f"BuildAll did not pass or imports missing: {full_missing}")
    json_write("CLEAN_BUILD_1_RESULT.json", clean1)

    if clean1.get("pass"):
        clean2 = compile_sequence("clean_build_2", full_order, clean_first=True)
        clean2["source_commit"] = source_commit
        clean2["qym_golden_hash_unchanged"] = verify_protected("CLEAN2:QYM_FINAL")["pass"]
        clean2["pass"] = bool(clean2["pass"] and clean2["qym_golden_hash_unchanged"])
    else:
        clean2 = skipped_result("CLEAN_BUILD_2", "Clean build #1 did not pass")
    json_write("CLEAN_BUILD_2_RESULT.json", clean2)

    all_sequences = [qym_replay, mock3_result, final13, buildall, clean1, clean2]
    all_log_sorry = sum(
        int(x.get("sorry_warning_lines", 0))
        for seq in all_sequences
        for x in seq.get("results", [])
    )
    axiom_audit = {
        "method": "comment/string-aware project-source scan plus kernel compilation of every required source and both clean reproductions",
        "project_axiom_declarations": sum(
            f["forbidden"]["axiom_declaration"] for f in forbidden_audit["files"]
        ),
        "sorry_tokens": sum(f["forbidden"]["sorry"] for f in forbidden_audit["files"]),
        "admit_tokens": sum(f["forbidden"]["admit"] for f in forbidden_audit["files"]),
        "sorryAx_or_sorry_warnings_in_compiler_logs": all_log_sorry,
        "legitimate_imported_foundations_classified_as_non_project_escapes": [
            "propext",
            "Classical.choice",
            "Quot.sound",
        ],
    }
    axiom_audit["pass"] = (
        axiom_audit["project_axiom_declarations"] == 0
        and axiom_audit["sorry_tokens"] == 0
        and axiom_audit["admit_tokens"] == 0
        and axiom_audit["sorryAx_or_sorry_warnings_in_compiler_logs"] == 0
    )
    json_write("AXIOM_AUDIT.json", axiom_audit)

    source_identity = {
        "repository": REPOSITORY,
        "branch": branch,
        "tested_source_commit": source_commit,
        "base_authority_commit": BASE_COMMIT,
        "lean_version": lean_version,
        "lake_version": lake_version,
        "toolchain": toolchain,
        "lake_manifest_sha256": lake_manifest_sha,
        "primary_roots": root_fps,
        "bridges": bridge_fps,
        "buildall": buildall_fp,
        "protected": verify_protected("FINAL_SOURCE_IDENTITY"),
        "changed_paths_audit": changed_audit,
        "all_pass_evidence_source_identical": all(
            seq.get("protected_before", {"pass": True}).get("pass", True)
            and seq.get("protected_after", {"pass": True}).get("pass", True)
            for seq in all_sequences
        ),
        "github_run_id": run_id,
        "github_run_url": run_url,
    }
    source_identity["pass"] = bool(
        source_identity["protected"]["pass"]
        and source_identity["changed_paths_audit"]["pass"]
        and source_identity["all_pass_evidence_source_identical"]
    )
    json_write("FINAL_SOURCE_IDENTITY.json", source_identity)

    final13_counts = final13.get("counts", {"PASS": 0, "FAIL": 0, "SKIPPED": 0, "NOT_RUN": 13})
    qym_leaf = result_for_path(qym_replay, QYM_PATH)
    mock3_leaf = result_for_path(mock3_result, MOCK3_PATH)
    fa_leaf = result_for_path(final13, FA_PATH)
    integrated_leaf = result_for_path(final13, INTEGRATED_PATH)

    checklist_prereq = bool(
        lock.get("pass")
        and qym_replay.get("pass")
        and mock3_result.get("pass")
        and final13.get("pass")
        and buildall.get("pass")
        and clean1.get("pass")
        and clean2.get("pass")
        and forbidden_audit.get("pass")
        and axiom_audit.get("pass")
        and source_identity.get("pass")
    )

    log_summary = {
        "qym_replay": compile_result_summary(qym_replay),
        "mock3": compile_result_summary(mock3_result),
        "final13": compile_result_summary(final13),
        "buildall": compile_result_summary(buildall),
        "clean1": compile_result_summary(clean1),
        "clean2": compile_result_summary(clean2),
    }
    warnings_total = sum(x["warnings"] for x in log_summary.values())
    errors_total = sum(x["errors"] for x in log_summary.values())
    panic_total = sum(x["panic"] for x in log_summary.values())
    sorry_total = sum(x["sorry_warnings"] for x in log_summary.values())

    commits = [
        {"sha": line.split("\t", 1)[0], "subject": line.split("\t", 1)[1] if "\t" in line else ""}
        for line in git("log", "--format=%H%x09%s", f"{BASE_COMMIT}..{source_commit}").splitlines()
        if line
    ]
    checkpoint_pass = len(commits) >= 3 and all(x["subject"].strip() for x in commits)
    branch_push_pass = branch == AUTHORITY_BRANCH and branch != "master" and bool(run_id)

    checklist = [
        checklist_item(
            1,
            "Completion report for all 13 primary files; actual direct Lean exit 0, errors 0, sorry warnings 0, panic 0; integrated/clean/CI-equivalent gates pass. Ordinary warnings are counted under the current GB0 authority override rather than hidden.",
            "FINAL_13_BUILD_RESULTS + BUILDALL_RESULT + CLEAN_BUILD_1/2_RESULT",
            source_commit,
            checklist_prereq and errors_total == 0 and panic_total == 0 and sorry_total == 0,
            "FINAL_13_BUILD_RESULTS.json",
            {"counts": final13_counts, "warnings_counted": warnings_total, "warning_policy": forbidden_audit["policy"]["warnings"]},
        ),
        checklist_item(
            2,
            "Record current remote branch, repository identity, pinned Lean/Lake/Mathlib environment, manifest SHA, commit and clean tracked status.",
            "git/lean/lake preflight",
            source_commit,
            preflight["pass"],
            "PREFLIGHT.json",
            {"branch": branch, "toolchain": toolchain, "lean": lean_version, "lake": lake_version},
        ),
        checklist_item(
            3,
            "Inspect changed paths/diff statistics and restrict modifications to necessary project integration and authority files.",
            f"git diff --name-only {BASE_COMMIT}..{source_commit}",
            source_commit,
            changed_audit["pass"],
            "PREFLIGHT.json",
            changed_audit,
        ),
        checklist_item(
            4,
            "Keep temporary probes, logs, olean/ilean and scratch files out of tracked production paths.",
            "git ls-files temporary-artifact audit",
            source_commit,
            temp_audit["pass"],
            "PREFLIGHT.json",
            temp_audit,
        ),
        checklist_item(
            5,
            "Comment/string-aware forbidden-element audit for sorry, admit, project axiom, native_decide, Lean.ofReduceBool, unsafe proof escapes and fake-pass markers.",
            "scripts/final_authority_gate.py source_audit",
            source_commit,
            forbidden_audit["pass"],
            "FORBIDDEN_AUDIT.json",
            {"forbidden_count": forbidden_audit["forbidden_count"]},
        ),
        checklist_item(
            6,
            "Whitespace/diff/mathematical-integrity review; protected mathematical roots remain byte-identical and only bridge/build wiring changes.",
            f"git diff --check {BASE_COMMIT}..{source_commit}",
            source_commit,
            diff_check["pass"] and changed_audit["pass"] and lock["pass"],
            "PREFLIGHT.json",
            {"diff_check": diff_check, "protected": lock["pass"]},
        ),
        checklist_item(
            7,
            "Record path, line count, byte count, SHA256 and Git blob for all 13 roots and mandatory bridges.",
            "FINAL_13_ROOTS manifest generation",
            source_commit,
            len(root_fps) == 13 and len(bridge_fps) == len(BRIDGES),
            "FINAL_13_ROOTS.txt",
            {"primary": len(root_fps), "bridges": len(bridge_fps)},
        ),
        checklist_item(
            8,
            "Exact intended staging only; no git add dot and no accidental source/compiler artifacts.",
            "changed-path allowlist + exact-path persistence workflow",
            source_commit,
            changed_audit["pass"] and temp_audit["pass"],
            "PREFLIGHT.json",
            {"allowed_paths": changed_audit["allowed_paths"]},
        ),
        checklist_item(
            9,
            "Use meaningful logical checkpoint commits; do not create fake empty commits.",
            f"git log {BASE_COMMIT}..{source_commit}",
            source_commit,
            checkpoint_pass,
            "PREFLIGHT.json",
            commits,
        ),
        checklist_item(
            10,
            "Record branch, full/short commit SHA, subject/date, Lean version and Mathlib/environment identity.",
            "git show + toolchain metadata",
            source_commit,
            bool(source_commit and commit_subject and commit_date and lean_version and lake_manifest_sha),
            "FINAL_SOURCE_IDENTITY.json",
            {"commit": source_commit, "subject": commit_subject, "date": commit_date},
        ),
        checklist_item(
            11,
            "Push only to the designated successor repair branch; never master and never force-push.",
            "GitHub push-triggered branch identity",
            source_commit,
            branch_push_pass,
            "FINAL_SOURCE_IDENTITY.json",
            {"branch": branch, "run_id": run_id},
        ),
        checklist_item(
            12,
            "Use GitHub Actions as independent verification and count PASS only where actual direct Lean steps ran.",
            "GitHub Actions run + compiler logs",
            source_commit,
            checklist_prereq and bool(run_id),
            "FINAL_TRUE_PASS_REPORT.md",
            {"run_id": run_id, "run_url": run_url},
        ),
        checklist_item(
            13,
            "Confirm exact remote source identities, plausible line counts, intended paths, toolchain, full-file compilation and no segment/prefix substitution.",
            "source fingerprints + full direct Lean commands",
            source_commit,
            source_identity["pass"] and all(x["lines"] > 0 for x in root_fps),
            "FINAL_SOURCE_IDENTITY.json",
            {"source_identity": source_identity["pass"]},
        ),
        checklist_item(
            14,
            "Axiom/trust audit: no sorryAx, user-defined/project axiom or newly introduced proof escape; imported logical foundations classified separately.",
            "static axiom scan + kernel compilation/log audit",
            source_commit,
            axiom_audit["pass"],
            "AXIOM_AUDIT.json",
            axiom_audit,
        ),
        checklist_item(
            15,
            "Final reproducibility/evidence package tying exact checked-in source bytes to two clean direct-Lean reproductions and all authority gates.",
            "required artifact existence + clean #1/#2 + source identity",
            source_commit,
            checklist_prereq,
            "FINAL_TRUE_PASS_REPORT.md",
            {"required_reports": REQUIRED_REPORT_NAMES, "clean1": clean1.get("pass"), "clean2": clean2.get("pass")},
        ),
    ]
    checklist_counts = {
        "PASS": sum(x["status"] == "PASS" for x in checklist),
        "FAIL": sum(x["status"] == "FAIL" for x in checklist),
        "NOT_RUN": 0,
        "SKIPPED": 0,
    }
    checklist_result = {
        "repository": REPOSITORY,
        "branch": branch,
        "source_commit": source_commit,
        "items": checklist,
        "counts": checklist_counts,
        "pass": checklist_counts == {"PASS": 15, "FAIL": 0, "NOT_RUN": 0, "SKIPPED": 0},
    }
    json_write("FINAL_15_CHECKLIST_RESULT.json", checklist_result)

    gates = [
        ("QYM golden locked", lock.get("pass", False)),
        ("QYM independent canonical replay", qym_replay.get("pass", False)),
        ("Mock3 canonical", mock3_result.get("pass", False)),
        ("Final13 manifest verified", preflight.get("pass", False) and graph_result.get("pass", False)),
        ("Final13 13/13 actual Lean", final13.get("pass", False)),
        ("BuildAll", buildall.get("pass", False)),
        ("clean build #1", clean1.get("pass", False)),
        ("clean build #2", clean2.get("pass", False)),
        ("checklist 15/15", checklist_result.get("pass", False)),
    ]
    last_completed = "NONE"
    next_incomplete = "NONE"
    prefix_open = True
    for name, passed in gates:
        if prefix_open and passed:
            last_completed = name
        elif prefix_open:
            next_incomplete = name
            prefix_open = False
    final_authority = bool(
        all(passed for _, passed in gates)
        and forbidden_audit["forbidden_count"] == 0
        and panic_total == 0
        and errors_total == 0
        and source_identity["pass"]
    )

    first_failure = STATE["first_failure"]
    blocker = first_failure.get("blocker_declaration") if first_failure else None
    first_error = first_failure.get("first_error") if first_failure else None

    status_card = f"""# FINAL AUTHORITY STATUS

QYM golden lock:
  {'PASS' if lock.get('pass') else 'FAIL'}
  blob: {lock.get('qym', {}).get('git_blob') if lock.get('qym') else 'NONE'}
  sha256: {lock.get('qym', {}).get('sha256') if lock.get('qym') else 'NONE'}

QYM canonical replay:
  {'PASS' if qym_replay.get('pass') else qym_replay.get('status', 'FAIL')}
  exit: {qym_leaf.get('exit') if qym_leaf else 'NOT RUN'}
  errors: {qym_leaf.get('error_headers') if qym_leaf else 'NOT RUN'}
  warnings: {qym_leaf.get('warning_headers') if qym_leaf else 'NOT RUN'}

FA:
  {'TRUE PASS' if fa_leaf and fa_leaf.get('pass') else 'NOT VERIFIED'}
  blob: {FA_BLOB}

Integrated:
  {'PASS' if integrated_leaf and integrated_leaf.get('pass') else 'NOT VERIFIED'}
  blob: {INTEGRATED_BLOB}

Mock3 canonical:
  {'PASS' if mock3_result.get('pass') else mock3_result.get('status', 'FAIL')}

Final13 manifest:
  {'VERIFIED' if preflight.get('pass') and graph_result.get('pass') else 'NOT VERIFIED'}
  roots: {len(ROOTS)}

Final13 Lean:
  {final13_counts.get('PASS', 0)}/13 PASS

BuildAll:
  {'PASS' if buildall.get('pass') else buildall.get('status', 'FAIL')}

Clean #1:
  {'PASS' if clean1.get('pass') else clean1.get('status', 'FAIL')}

Clean #2:
  {'PASS' if clean2.get('pass') else clean2.get('status', 'FAIL')}

Checklist:
  {checklist_counts['PASS']}/15 PASS

forbidden:
  {forbidden_audit['forbidden_count']}

panic:
  {panic_total}

last completed authority gate:
  {last_completed}

next incomplete gate:
  {next_incomplete}

final blocker:
  {blocker or 'NONE'}

FINAL AUTHORITY:
  {'PASS' if final_authority else 'NOT COMPLETE'}
"""
    text_write("FINAL_STATUS_CARD.md", status_card)

    buildall_leaf = result_for_path(buildall, BUILDALL_PATH)
    report = f"""# FINAL AUTHORITY REPORT

repository: {REPOSITORY}
final branch: {branch}
tested source commit: {source_commit}
GitHub Actions run: {run_id or 'NONE'}
GitHub Actions URL: {run_url or 'NONE'}

Lean version: {lean_version}
Lake version: {lake_version}
Pinned toolchain: {toolchain}
lake-manifest SHA256: {lake_manifest_sha}

Mock2:
  {'PASS' if result_for_path(final13, Path('PrimalitySheafVerification/Mock2.lean')) and result_for_path(final13, Path('PrimalitySheafVerification/Mock2.lean')).get('pass') else 'NOT VERIFIED'}

Mock2_Advanced:
  {'PASS' if result_for_path(final13, Path('PrimalitySheafVerification/Mock2_Advanced.lean')) and result_for_path(final13, Path('PrimalitySheafVerification/Mock2_Advanced.lean')).get('pass') else 'NOT VERIFIED'}

Mock2_FunctionalAnalysis:
  status: {'TRUE PASS' if fa_leaf and fa_leaf.get('pass') else 'NOT VERIFIED'}
  blob: {FA_BLOB}
  sha256: {fa_leaf.get('source_sha256') if fa_leaf else 'NOT RUN'}
  direct Lean exit: {fa_leaf.get('exit') if fa_leaf else 'NOT RUN'}
  errors: {fa_leaf.get('error_headers') if fa_leaf else 'NOT RUN'}

Integrated:
  status: {'PASS' if integrated_leaf and integrated_leaf.get('pass') else 'NOT VERIFIED'}
  blob: {INTEGRATED_BLOB}
  sha256: {integrated_leaf.get('source_sha256') if integrated_leaf else 'NOT RUN'}
  direct Lean exit: {integrated_leaf.get('exit') if integrated_leaf else 'NOT RUN'}
  errors: {integrated_leaf.get('error_headers') if integrated_leaf else 'NOT RUN'}

QYM:
  status: {'TRUE PASS' if qym_leaf and qym_leaf.get('pass') else 'NOT VERIFIED'}
  canonical replay: {'PASS' if qym_replay.get('pass') else qym_replay.get('status', 'FAIL')}
  blob: {QYM_BLOB}
  sha256: {QYM_SHA256}
  direct Lean exit: {qym_leaf.get('exit') if qym_leaf else 'NOT RUN'}
  error_headers: {qym_leaf.get('error_headers') if qym_leaf else 'NOT RUN'}
  warnings: {qym_leaf.get('warning_headers') if qym_leaf else 'NOT RUN'}
  panic: {qym_leaf.get('panic_lines') if qym_leaf else 'NOT RUN'}
  forbidden: {forbidden_audit['forbidden_count']}
  olean: {qym_leaf.get('olean_generated') if qym_leaf else 'NOT RUN'}
  ilean: {qym_leaf.get('ilean_generated') if qym_leaf else 'NOT RUN'}

Mock3:
  canonical path: {MOCK3_PATH}
  blob: {mock3_leaf.get('source_git_blob') if mock3_leaf else 'NOT RUN'}
  sha256: {mock3_leaf.get('source_sha256') if mock3_leaf else 'NOT RUN'}
  direct Lean exit: {mock3_leaf.get('exit') if mock3_leaf else 'NOT RUN'}
  errors: {mock3_leaf.get('error_headers') if mock3_leaf else 'NOT RUN'}

Final13:
  root count: 13
  PASS: {final13_counts.get('PASS', 0)}
  FAIL: {final13_counts.get('FAIL', 0)}
  SKIPPED: {final13_counts.get('SKIPPED', 0)}
  NOT RUN: {final13_counts.get('NOT_RUN', 0)}

BuildAll:
  exit: {buildall_leaf.get('exit') if buildall_leaf else 'NOT RUN'}
  errors: {buildall_leaf.get('error_headers') if buildall_leaf else 'NOT RUN'}
  skipped required targets: {len(buildall.get('required_skipped_targets', []))}

Clean build #1:
  {'PASS' if clean1.get('pass') else clean1.get('status', 'FAIL')}

Clean build #2:
  {'PASS' if clean2.get('pass') else clean2.get('status', 'FAIL')}

15-checklist:
  PASS: {checklist_counts['PASS']}
  FAIL: {checklist_counts['FAIL']}
  NOT RUN: {checklist_counts['NOT_RUN']}
  SKIPPED: {checklist_counts['SKIPPED']}

final first Lean error:
  {json.dumps(first_error, ensure_ascii=False) if first_error else 'NONE'}

final blocker:
  {blocker or 'NONE'}

last completed authority gate:
  {last_completed}

next incomplete gate:
  {next_incomplete}

QYM golden source unchanged:
  {'YES' if source_identity['protected']['pass'] else 'NO'}

all PASS evidence source-identical:
  {'YES' if source_identity['all_pass_evidence_source_identical'] else 'NO'}

warnings:
  counted, preserved, and classified under the current GB0 authority policy; not silently discarded

FINAL AUTHORITY:
  {'PASS' if final_authority else 'NOT COMPLETE'}
"""
    text_write("FINAL_TRUE_PASS_REPORT.md", report)

    existing_required = [name for name in REQUIRED_REPORT_NAMES if (EVIDENCE / name).is_file()]
    checklist_result["required_reports_existing"] = existing_required
    checklist_result["required_reports_missing"] = sorted(set(REQUIRED_REPORT_NAMES) - set(existing_required))
    if checklist_result["required_reports_missing"]:
        checklist_result["pass"] = False
        checklist_result["items"][-1]["status"] = "FAIL"
        checklist_result["counts"]["PASS"] = sum(x["status"] == "PASS" for x in checklist_result["items"])
        checklist_result["counts"]["FAIL"] = sum(x["status"] == "FAIL" for x in checklist_result["items"])
        final_authority = False
        text_write("FINAL_STATUS_CARD.md", status_card.replace("FINAL AUTHORITY:\n  PASS", "FINAL AUTHORITY:\n  NOT COMPLETE"))
        text_write("FINAL_TRUE_PASS_REPORT.md", report.replace("FINAL AUTHORITY:\n  PASS", "FINAL AUTHORITY:\n  NOT COMPLETE"))
    json_write("FINAL_15_CHECKLIST_RESULT.json", checklist_result)

    STATE["finished_at_utc"] = datetime.now(timezone.utc).isoformat()
    STATE["last_completed_authority_gate"] = last_completed
    STATE["next_incomplete_gate"] = next_incomplete
    STATE["final_authority"] = final_authority
    STATE["log_summary"] = log_summary
    json_write("EXECUTION_STATE.json", STATE)
    text_write("FINAL_EXIT", "0\n" if final_authority else "1\n")
    print(status_card, flush=True)
    return 0 if final_authority else 1


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except SystemExit:
        raise
    except Exception as exc:
        ensure_dirs()
        crash = {
            "exception": repr(exc),
            "traceback": traceback.format_exc(),
            "state": STATE,
        }
        json_write("UNHANDLED_EXCEPTION.json", crash)
        if STATE["first_failure"] is None:
            STATE["first_failure"] = {
                "stage": "orchestrator",
                "path": None,
                "first_error": str(exc),
                "blocker_declaration": None,
                "exit": None,
                "lean_actually_ran": False,
                "classification": "workflow/orchestrator infrastructure failure",
            }
        text_write("FINAL_EXIT", "1\n")
        text_write(
            "FINAL_STATUS_CARD.md",
            "# FINAL AUTHORITY STATUS\n\nFINAL AUTHORITY:\n  NOT COMPLETE\n\n"
            f"final blocker:\n  {exc}\n",
        )
        traceback.print_exc()
        raise SystemExit(1)
