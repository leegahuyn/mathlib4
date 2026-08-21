#!/usr/bin/env python3
"""Deterministically repair the sole BuildAll-only Lean error.

The engine is deliberately conservative:
* protected FA / Integrated / QYM sources are immutable;
* it starts from an actual BuildAll log;
* it only handles one diagnostic cluster;
* the main automatic repair is a duplicate fully-qualified declaration exposed
  only when all independently passing roots are imported together;
* every candidate must make a fresh full BuildAll direct-Lean compile pass.
"""
from __future__ import annotations

import hashlib
import json
import os
import re
import subprocess
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
EVIDENCE = ROOT / ".buildall_v10"
EVIDENCE.mkdir(parents=True, exist_ok=True)

BUILDALL = Path("PrimalitySheafVerification/BuildAll.lean")
PROTECTED = {
    Path("PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean"):
        "28f614d48e02a0f28d3f5a758e813350b3ea89cf",
    Path("PrimalitySheafVerification/Mock2_FunctionalAnalysis_Integrated.lean"):
        "464f5dd095876b20165d12690c8127ef9d909e6a",
    Path("PrimalitySheafVerification/QYM.lean"):
        "7afb309d7c4da97da7bc6b922931734d72830d41",
}

DIAG_RE = re.compile(
    r"^(?P<file>.*?\.lean):(?P<line>\d+):(?P<column>\d+): "
    r"error(?:\([^)]*\))?:\s*(?P<message>.*)$",
    re.MULTILINE,
)

DECL_RE_TEMPLATE = (
    r"(?m)^(?P<indent>\s*)"
    r"(?P<prefix>(?:(?:private|protected|noncomputable|local|partial)\s+)*)"
    r"(?P<kind>theorem|lemma|def|abbrev|opaque|structure|class|inductive)\s+"
    r"(?P<name>{name})(?P<tail>(?=\s|\(|\{|:|where|$))"
)


def git(*args: str, check: bool = True) -> str:
    p = subprocess.run(
        ["git", *args], cwd=ROOT, text=True,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE,
    )
    if check and p.returncode != 0:
        raise RuntimeError(f"git {' '.join(args)} failed: {p.stderr.strip()}")
    return p.stdout.strip()


def sha256(path: Path) -> str:
    return hashlib.sha256((ROOT / path).read_bytes()).hexdigest()


def verify_protected(label: str) -> dict[str, Any]:
    rows = []
    ok = True
    for path, expected in PROTECTED.items():
        actual = git("hash-object", "--no-filters", str(path))
        row = {
            "path": str(path), "expected_blob": expected,
            "actual_blob": actual, "sha256": sha256(path),
            "pass": actual == expected,
        }
        rows.append(row)
        ok = ok and row["pass"]
    result = {"label": label, "files": rows, "pass": ok}
    (EVIDENCE / f"PROTECTED_{label}.json").write_text(
        json.dumps(result, indent=2, ensure_ascii=False) + "\n"
    )
    if not ok:
        raise RuntimeError(f"protected identity failure at {label}")
    return result


def parse_log(path: Path) -> dict[str, Any]:
    text = path.read_text(encoding="utf-8", errors="replace") if path.exists() else ""
    rows = []
    for m in DIAG_RE.finditer(text):
        d = m.groupdict()
        d["line"] = int(d["line"])
        d["column"] = int(d["column"])
        d["message"] = d["message"].strip()
        rows.append(d)
    panic = [
        line for line in text.splitlines()
        if re.search(r"(?i)(internal error|uncaught exception|panic!)", line)
    ]
    return {
        "error_headers": len(rows),
        "errors": rows,
        "first_error": rows[0] if rows else None,
        "panic_lines": panic,
    }


def compile_buildall(stage: str) -> dict[str, Any]:
    log = EVIDENCE / f"{stage}.log"
    olean = ROOT / BUILDALL.with_suffix(".olean")
    ilean = ROOT / BUILDALL.with_suffix(".ilean")
    for p in (olean, ilean):
        if p.exists():
            p.unlink()
    cmd = [
        "lake", "env", "lean", "-DmaxErrors=2000", "-DwarningAsError=false",
        str(BUILDALL),
    ]
    with log.open("wb") as f:
        p = subprocess.run(cmd, cwd=ROOT, stdout=f, stderr=subprocess.STDOUT)
    diag = parse_log(log)
    result = {
        "stage": stage,
        "command": " ".join(cmd),
        "exit": p.returncode,
        **diag,
        "pass": p.returncode == 0 and diag["error_headers"] == 0 and not diag["panic_lines"],
        "log": str(log.relative_to(ROOT)),
    }
    (EVIDENCE / f"{stage}.json").write_text(
        json.dumps(result, indent=2, ensure_ascii=False) + "\n"
    )
    print(json.dumps(result, indent=2, ensure_ascii=False), flush=True)
    return result


def normalize_error_file(raw: str) -> Path | None:
    raw = raw.replace("\\", "/")
    marker = "PrimalitySheafVerification/"
    if marker in raw:
        raw = raw[raw.index(marker):]
    path = Path(raw)
    if (ROOT / path).is_file():
        return path
    return None


def duplicate_name(message: str) -> str | None:
    patterns = [
        r"declaration\s+['`\"](?P<n>[^'`\"]+)['`\"]\s+has already been declared",
        r"['`\"](?P<n>[^'`\"]+)['`\"]\s+has already been declared",
        r"already declared\s+['`\"](?P<n>[^'`\"]+)['`\"]",
        r"declaration\s+(?P<n>[A-Za-z0-9_'.]+)\s+has already been declared",
    ]
    for pattern in patterns:
        m = re.search(pattern, message, re.I)
        if m:
            return m.group("n")
    return None


def source_files() -> list[Path]:
    build_text = (ROOT / BUILDALL).read_text(encoding="utf-8")
    files = []
    for module in re.findall(r"(?m)^\s*import\s+(PrimalitySheafVerification\.[A-Za-z0-9_']+)\s*$", build_text):
        path = Path(*module.split(".")).with_suffix(".lean")
        if (ROOT / path).is_file() and path not in files:
            files.append(path)
    return files


def choose_duplicate_file(name: str, error_file: Path | None) -> tuple[Path, str, list[dict[str, Any]]]:
    local = name.split(".")[-1]
    declaration = re.compile(DECL_RE_TEMPLATE.format(name=re.escape(local)))
    candidates: list[dict[str, Any]] = []
    order = source_files()
    for index, path in enumerate(order):
        if path in PROTECTED:
            continue
        text = (ROOT / path).read_text(encoding="utf-8")
        for m in declaration.finditer(text):
            candidates.append({
                "path": path,
                "order": index,
                "line": text.count("\n", 0, m.start()) + 1,
                "local_name": local,
                "match": m.group(0),
            })
    if error_file and error_file not in PROTECTED:
        same = [x for x in candidates if x["path"] == error_file]
        if same:
            chosen = same[-1]
            return chosen["path"], local, candidates
    if len(candidates) < 2:
        raise RuntimeError(
            f"duplicate diagnostic named {name!r}, but only {len(candidates)} editable declaration candidate(s) found"
        )
    chosen = sorted(candidates, key=lambda x: (x["order"], x["line"]))[-1]
    return chosen["path"], local, candidates


def rename_local_declaration(path: Path, local: str) -> dict[str, Any]:
    full = ROOT / path
    text = full.read_text(encoding="utf-8")
    module_prefix = path.stem.replace("-", "_")
    new = f"{module_prefix}__{local}"
    if re.search(rf"\b{re.escape(new)}\b", text):
        raise RuntimeError(f"generated replacement name already exists: {new}")
    decl_re = re.compile(DECL_RE_TEMPLATE.format(name=re.escape(local)))
    decl_count = len(list(decl_re.finditer(text)))
    if decl_count != 1:
        raise RuntimeError(
            f"expected exactly one declaration of {local!r} in {path}, found {decl_count}"
        )
    # Rename all exact identifier occurrences in the selected module so local
    # references and axiom-audit commands remain synchronized. Qualified uses
    # also receive the unique suffix, while unrelated longer names are untouched.
    updated, count = re.subn(rf"(?<![A-Za-z0-9_']){re.escape(local)}(?![A-Za-z0-9_'])", new, text)
    if count < 1:
        raise RuntimeError(f"no occurrences replaced for {local!r} in {path}")
    full.write_text(updated, encoding="utf-8")
    return {
        "strategy": "rename_duplicate_declaration",
        "path": str(path),
        "old_local_name": local,
        "new_local_name": new,
        "replacement_count": count,
    }


def apply_known_idempotent_repairs() -> list[dict[str, Any]]:
    changes: list[dict[str, Any]] = []
    # Keep the already-verified Spt1 replacement idempotent.
    spt1 = ROOT / "PrimalitySheafVerification/Spt1.lean"
    if spt1.is_file():
        text = spt1.read_text(encoding="utf-8")
        old = "example : Fintype.card {x : ZMod 9 // (12 : ZMod 9) * x = 0} = 3 := by native_decide"
        new = """example : Fintype.card {x : ZMod 9 // (12 : ZMod 9) * x = 0} = 3 := by
  rw [← Nat.card_eq_fintype_card]
  change Nat.card (AddMonoidHom.mulLeft (12 : ZMod 9)).ker = 3
  simpa using (card_ker_mulLeft 9 12)"""
        if text.count(old) == 1:
            spt1.write_text(text.replace(old, new, 1), encoding="utf-8")
            changes.append({"strategy": "known_spt1_native_decide_replacement", "path": str(spt1.relative_to(ROOT))})
    return changes


def main() -> int:
    verify_protected("BEFORE")
    initial = compile_buildall("BUILDALL_BEFORE_REPAIR")
    if initial["pass"]:
        result = {"status": "ALREADY_PASS", "repairs": [], "final": initial, "pass": True}
        (EVIDENCE / "REPAIR_RESULT.json").write_text(json.dumps(result, indent=2) + "\n")
        return 0

    if initial["error_headers"] != 1:
        raise RuntimeError(
            f"authority expected exactly one BuildAll error, observed {initial['error_headers']}"
        )

    repairs = apply_known_idempotent_repairs()
    after_known = compile_buildall("BUILDALL_AFTER_KNOWN_REPAIRS") if repairs else initial
    if after_known["pass"]:
        verify_protected("AFTER")
        result = {"status": "REPAIRED", "repairs": repairs, "final": after_known, "pass": True}
        (EVIDENCE / "REPAIR_RESULT.json").write_text(json.dumps(result, indent=2, ensure_ascii=False) + "\n")
        return 0

    first = after_known["first_error"]
    assert first is not None
    dup = duplicate_name(first["message"])
    if not dup:
        result = {
            "status": "UNSUPPORTED_ONE_ERROR",
            "repairs": repairs,
            "first_error": first,
            "pass": False,
        }
        (EVIDENCE / "REPAIR_RESULT.json").write_text(json.dumps(result, indent=2, ensure_ascii=False) + "\n")
        return 2

    err_file = normalize_error_file(first["file"])
    path, local, candidates = choose_duplicate_file(dup, err_file)
    repair = rename_local_declaration(path, local)
    repair["diagnostic_name"] = dup
    repair["declaration_candidates"] = [
        {k: (str(v) if isinstance(v, Path) else v) for k, v in x.items() if k != "match"}
        for x in candidates
    ]
    repairs.append(repair)

    verify_protected("AFTER_PATCH")
    final = compile_buildall("BUILDALL_AFTER_REPAIR")
    result = {
        "status": "REPAIRED" if final["pass"] else "REPAIR_FAILED",
        "repairs": repairs,
        "final": final,
        "git_diff": git("diff", "--", "PrimalitySheafVerification", check=False),
        "pass": final["pass"],
    }
    (EVIDENCE / "REPAIR_RESULT.json").write_text(
        json.dumps(result, indent=2, ensure_ascii=False) + "\n"
    )
    verify_protected("FINAL")
    return 0 if final["pass"] else 3


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as exc:
        failure = {"status": "EXCEPTION", "type": type(exc).__name__, "message": str(exc), "pass": False}
        (EVIDENCE / "REPAIR_RESULT.json").write_text(
            json.dumps(failure, indent=2, ensure_ascii=False) + "\n"
        )
        print(json.dumps(failure, indent=2, ensure_ascii=False), file=sys.stderr)
        raise
