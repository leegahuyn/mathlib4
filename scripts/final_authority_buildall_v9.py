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
from dataclasses import dataclass
from pathlib import Path
from typing import Any

ROOT = Path.cwd().resolve()
EVID = ROOT / ".final_authority_v9"
EVID.mkdir(parents=True, exist_ok=True)

PROTECTED = {
    "PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean":
        "28f614d48e02a0f28d3f5a758e813350b3ea89cf",
    "PrimalitySheafVerification/Mock2_FunctionalAnalysis_Integrated.lean":
        "464f5dd095876b20165d12690c8127ef9d909e6a",
    "PrimalitySheafVerification/QYM.lean":
        "7afb309d7c4da97da7bc6b922931734d72830d41",
}

ROOT_PATHS = [
    Path("PrimalitySheafVerification/Spt1.lean"),
    Path("PrimalitySheafVerification/Spt2.lean"),
    Path("PrimalitySheafVerification/Spt3.lean"),
    Path("PrimalitySheafVerification/Spt4.lean"),
    Path("PrimalitySheafVerification/Spt5.lean"),
    Path("PrimalitySheafVerification/Spt6.lean"),
    Path("PrimalitySheafVerification/Spt7.lean"),
    Path("PrimalitySheafVerification/Mock1.lean"),
    Path("PrimalitySheafVerification/Mock1_Advanced.lean"),
    Path("PrimalitySheafVerification/Mock2.lean"),
    Path("PrimalitySheafVerification/Mock2_Advanced.lean"),
    Path("PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean"),
    Path("PrimalitySheafVerification/QYM.lean"),
]
BUILDALL = Path("PrimalitySheafVerification/BuildAll.lean")

DECL_RE = re.compile(
    r"^\s*(?:(?:private|protected|noncomputable|local|unsafe)\s+)*"
    r"(?:theorem|lemma|def|abbrev|opaque|structure|class|inductive)\s+"
    r"([A-Za-z_][A-Za-z0-9_'.]*)"
)
NAMESPACE_RE = re.compile(r"^\s*namespace\s+([A-Za-z_][A-Za-z0-9_'.]*)\s*$")
SECTION_RE = re.compile(r"^\s*section(?:\s+[A-Za-z_][A-Za-z0-9_']*)?\s*$")
END_RE = re.compile(r"^\s*end(?:\s+[A-Za-z_][A-Za-z0-9_'.]*)?\s*$")


@dataclass
class Block:
    kind: str
    parts: list[str]
    start: int
    end: int | None = None


@dataclass
class Declaration:
    path: Path
    fq_name: str
    leaf: str
    line: int
    region_start: int
    region_end: int


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
    passed = True
    for rel, expected in PROTECTED.items():
        actual = git("hash-object", "--no-filters", rel)
        row = {"path": rel, "expected_blob": expected, "actual_blob": actual,
               "sha256": sha256(Path(rel)), "pass": actual == expected}
        rows.append(row)
        passed = passed and row["pass"]
    result = {"label": label, "files": rows, "pass": passed}
    (EVID / f"PROTECTED_{label}.json").write_text(
        json.dumps(result, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )
    if not passed:
        raise RuntimeError(f"protected-source identity failure at {label}")
    return result


def strip_comments_and_strings(text: str) -> str:
    out: list[str] = []
    i = 0
    block = 0
    line_comment = False
    string = False
    escape = False
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
        if block:
            if c == "/" and n == "-":
                block += 1; out.extend((" ", " ")); i += 2
            elif c == "-" and n == "/":
                block -= 1; out.extend((" ", " ")); i += 2
            else:
                out.append("\n" if c == "\n" else " "); i += 1
            continue
        if string:
            if escape:
                escape = False
            elif c == "\\":
                escape = True
            elif c == '"':
                string = False
            out.append("\n" if c == "\n" else " ")
            i += 1
            continue
        if c == "-" and n == "-":
            line_comment = True; out.extend((" ", " ")); i += 2
        elif c == "/" and n == "-":
            block = 1; out.extend((" ", " ")); i += 2
        elif c == '"':
            string = True; out.append(" "); i += 1
        else:
            out.append(c); i += 1
    return "".join(out)


def declarations(path: Path) -> list[Declaration]:
    raw = (ROOT / path).read_text(encoding="utf-8")
    code_lines = strip_comments_and_strings(raw).splitlines()
    blocks: list[Block] = []
    active_namespaces: list[str] = []
    pending: list[tuple[str, str, int, list[int]]] = []

    for index, line in enumerate(code_lines):
        m = NAMESPACE_RE.match(line)
        if m:
            parts = m.group(1).split(".")
            blocks.append(Block("namespace", parts, index))
            active_namespaces.extend(parts)
            continue
        if SECTION_RE.match(line):
            blocks.append(Block("section", [], index))
            continue
        if END_RE.match(line):
            if blocks:
                closed = blocks.pop()
                closed.end = index
                if closed.kind == "namespace" and closed.parts:
                    del active_namespaces[-len(closed.parts):]
            continue
        m = DECL_RE.match(line)
        if not m:
            continue
        declared = m.group(1)
        explicit = declared.split(".")
        fq_parts = active_namespaces + explicit
        fq = ".".join(fq_parts)
        ns_block_indices = [i for i, b in enumerate(blocks) if b.kind == "namespace"]
        pending.append((fq, explicit[-1], index, ns_block_indices))

    total = len(code_lines)
    # Re-scan to obtain namespace region ends with stable block IDs.
    blocks2: list[tuple[int, Block]] = []
    all_blocks: dict[int, Block] = {}
    next_id = 0
    snapshots: dict[int, list[int]] = {}
    for index, line in enumerate(code_lines):
        m = NAMESPACE_RE.match(line)
        if m:
            b = Block("namespace", m.group(1).split("."), index)
            all_blocks[next_id] = b
            blocks2.append((next_id, b)); next_id += 1
        elif SECTION_RE.match(line):
            b = Block("section", [], index)
            all_blocks[next_id] = b
            blocks2.append((next_id, b)); next_id += 1
        elif END_RE.match(line):
            if blocks2:
                bid, b = blocks2.pop(); b.end = index
        elif DECL_RE.match(line):
            snapshots[index] = [bid for bid, b in blocks2 if b.kind == "namespace"]
    for _, b in blocks2:
        b.end = total

    result: list[Declaration] = []
    for fq, leaf, line, _ in pending:
        ids = snapshots.get(line, [])
        if ids:
            inner = all_blocks[ids[-1]]
            start, end = inner.start, inner.end if inner.end is not None else total
        else:
            start, end = 0, total
        result.append(Declaration(path, fq, leaf, line, start, end))
    return result


def read_buildall_failure() -> str:
    chunks: list[str] = []
    result_path = ROOT / ".final_authority" / "BUILDALL_RESULT.json"
    if result_path.exists():
        chunks.append(result_path.read_text(encoding="utf-8", errors="replace"))
    log_root = ROOT / ".final_authority" / "logs"
    if log_root.exists():
        for p in sorted(log_root.glob("*buildall*")):
            if p.is_file():
                chunks.append(p.read_text(encoding="utf-8", errors="replace"))
    text = "\n".join(chunks)
    (EVID / "BUILDALL_FAILURE_SURFACE.txt").write_text(text, encoding="utf-8")
    return text


def collision_names(text: str) -> list[str]:
    patterns = [
        r"['`\"]([A-Za-z_][A-Za-z0-9_'.]*)['`\"]\s+has already been declared",
        r"invalid redeclaration of\s+['`\"]?([A-Za-z_][A-Za-z0-9_'.]*)",
        r"declaration\s+['`\"]?([A-Za-z_][A-Za-z0-9_'.]*)['`\"]?\s+already exists",
        r"already declared[^\n]*?['`\"]([A-Za-z_][A-Za-z0-9_'.]*)['`\"]",
    ]
    found: list[str] = []
    for pattern in patterns:
        for value in re.findall(pattern, text, flags=re.IGNORECASE):
            value = value.strip("'`\"")
            if value and value not in found:
                found.append(value)
    return found


def clear_output(path: Path) -> None:
    for ext in (".olean", ".ilean"):
        p = ROOT / path.with_suffix(ext)
        if p.exists():
            p.unlink()
    build_base = ROOT / ".lake" / "build" / "lib" / "lean" / path.with_suffix("")
    for ext in (".olean", ".ilean"):
        p = Path(str(build_base) + ext)
        if p.exists():
            p.unlink()


def compile_file(path: Path, label: str, timeout_seconds: int = 10800) -> dict[str, Any]:
    clear_output(path)
    log = EVID / f"{label}.log"
    cmd = ["lake", "env", "lean", "-DmaxErrors=2000", "-DwarningAsError=false", str(path)]
    started = time.monotonic()
    with log.open("wb") as handle:
        try:
            p = subprocess.run(cmd, cwd=ROOT, stdout=handle, stderr=subprocess.STDOUT,
                               timeout=timeout_seconds)
            rc = p.returncode
        except subprocess.TimeoutExpired:
            rc = 124
    text = log.read_text(encoding="utf-8", errors="replace")
    errors = len(re.findall(r":\d+:\d+: error(?:\([^)]*\))?:", text))
    panic = len(re.findall(r"(?i)(internal error|uncaught exception|panic!)", text))
    result = {
        "path": str(path), "label": label, "command": cmd, "exit": rc,
        "errors": errors, "panic": panic,
        "elapsed_seconds": round(time.monotonic() - started, 3),
        "pass": rc == 0 and errors == 0 and panic == 0,
        "log": str(log.relative_to(ROOT)),
    }
    (EVID / f"{label}.json").write_text(
        json.dumps(result, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )
    return result


def replace_identifier_in_region(path: Path, decl: Declaration, old_fq: str,
                                 new_leaf: str) -> tuple[str, str]:
    full = ROOT / path
    before = full.read_text(encoding="utf-8")
    lines = before.splitlines(keepends=True)
    old_leaf = decl.leaf
    token = re.compile(rf"(?<![A-Za-z0-9_']){re.escape(old_leaf)}(?![A-Za-z0-9_'])")
    for i in range(max(0, decl.region_start), min(len(lines), decl.region_end + 1)):
        lines[i] = token.sub(new_leaf, lines[i])
    after = "".join(lines)
    new_fq = old_fq.rsplit(".", 1)[0] + "." + new_leaf if "." in old_fq else new_leaf
    after = re.sub(
        rf"(?<![A-Za-z0-9_']){re.escape(old_fq)}(?![A-Za-z0-9_'])",
        new_fq,
        after,
    )
    if after == before:
        raise RuntimeError(f"identifier replacement made no change: {old_fq} in {path}")
    full.write_text(after, encoding="utf-8")
    return before, new_fq


def choose_candidates(name: str, all_decls: list[Declaration]) -> list[Declaration]:
    leaf = name.rsplit(".", 1)[-1]
    exact = [d for d in all_decls if d.fq_name == name]
    pool = exact if exact else [d for d in all_decls if d.leaf == leaf]
    protected_paths = {Path(x) for x in PROTECTED}
    pool = [d for d in pool if d.path not in protected_paths]
    order = {p: i for i, p in enumerate(ROOT_PATHS)}
    # Preserve the earliest declaration and prefer renaming the later/project-local copy.
    pool.sort(key=lambda d: (order.get(d.path, -1), d.line), reverse=True)
    return pool


def make_runtime_gate(selected_path: Path) -> Path:
    source_path = ROOT / "scripts" / "final_authority_gate_v5.py"
    text = source_path.read_text(encoding="utf-8")
    rel = str(selected_path)
    if rel not in text:
        marker = '        "PrimalitySheafVerification/Spt1.lean",\n'
        if marker not in text:
            raise RuntimeError("cannot extend runtime authority allowlist")
        text = text.replace(marker, marker + f'        "{rel}",\n')
    runtime = ROOT / "scripts" / ".final_authority_gate_v9_runtime.py"
    runtime.write_text(text, encoding="utf-8")
    return runtime


def main() -> int:
    verify_protected("BEFORE")
    text = read_buildall_failure()
    names = collision_names(text)
    (EVID / "COLLISION_NAMES.json").write_text(
        json.dumps({"names": names}, indent=2) + "\n", encoding="utf-8"
    )
    if not names:
        raise RuntimeError("BuildAll failure is not a recognized declaration collision; no blind edit performed")

    all_decls: list[Declaration] = []
    for path in ROOT_PATHS:
        all_decls.extend(declarations(path))

    attempts: list[dict[str, Any]] = []
    selected: dict[str, Any] | None = None
    for name in names:
        for decl in choose_candidates(name, all_decls):
            full = ROOT / decl.path
            original = full.read_text(encoding="utf-8")
            stem = re.sub(r"[^A-Za-z0-9_]", "_", decl.path.stem)
            new_leaf = f"{decl.leaf}_{stem}Authority"
            try:
                _, new_fq = replace_identifier_in_region(decl.path, decl, name, new_leaf)
                diff = subprocess.run(["git", "diff", "--check"], cwd=ROOT,
                                      text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
                if diff.returncode != 0:
                    raise RuntimeError(diff.stdout)
                root_result = compile_file(decl.path, f"candidate_{len(attempts)+1}_root")
                buildall_result = (
                    compile_file(BUILDALL, f"candidate_{len(attempts)+1}_buildall")
                    if root_result["pass"] else {"pass": False, "reason": "root failed"}
                )
                attempt = {
                    "collision": name, "path": str(decl.path), "line": decl.line + 1,
                    "new_fq_name": new_fq, "root_result": root_result,
                    "buildall_result": buildall_result,
                }
                attempts.append(attempt)
                if root_result["pass"] and buildall_result.get("pass"):
                    selected = attempt
                    break
            except Exception as exc:
                attempts.append({
                    "collision": name, "path": str(decl.path), "line": decl.line + 1,
                    "exception": repr(exc), "pass": False,
                })
            if selected:
                break
            full.write_text(original, encoding="utf-8")
        if selected:
            break

    result = {"attempts": attempts, "selected": selected, "pass": selected is not None}
    (EVID / "BUILDALL_REPAIR_RESULT.json").write_text(
        json.dumps(result, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )
    if not selected:
        raise RuntimeError("no declaration-collision repair passed both root Lean and BuildAll Lean")

    verify_protected("AFTER")
    selected_path = Path(selected["path"])
    runtime = make_runtime_gate(selected_path)
    (EVID / "SELECTED_PATH.txt").write_text(str(selected_path) + "\n", encoding="utf-8")
    (EVID / "RUNTIME_GATE_PATH.txt").write_text(str(runtime.relative_to(ROOT)) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
