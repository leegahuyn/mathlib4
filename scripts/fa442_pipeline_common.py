from __future__ import annotations

import hashlib
import json
import os
import re
import subprocess
from pathlib import Path
from typing import Any, Iterable

REPO = Path(__file__).resolve().parents[1]
FA_PATH = REPO / "PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean"
MOCK2_PATH = REPO / "PrimalitySheafVerification/Mock2.lean"
MOCK2_ADV_PATH = REPO / "PrimalitySheafVerification/Mock2_Advanced.lean"
BASELINE_SHA256 = "71dc36f16ebea92d537aa40a5d420443e4bcb93ccb76fea31efb40a6cb5c3aa0"
BASELINE_LINE_COUNT = 60453
BLOCKER = "actualEdgeAmbientParam_hasDerivAt"
FA442_RUN_ID = 31345045760
FA423_RUN_ID = 31317392557

DECL_RE = re.compile(
    r"^\s*(?:noncomputable\s+)?(?:private\s+|protected\s+)?"
    r"(theorem|lemma|def|abbrev|instance|structure|class|inductive)\s+"
    r"([A-Za-z_][A-Za-z0-9_'.]*)",
    re.MULTILINE,
)
ERROR_RE = re.compile(
    r"Mock2_FunctionalAnalysis\.lean:(\d+):(\d+):\s+"
    r"error(?:\([^)]*\))?:\s*(.*)"
)


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def line_count_bytes(data: bytes) -> int:
    return data.count(b"\n") + (0 if data.endswith(b"\n") else 1)


def run(command: list[str], *, cwd: Path = REPO, check: bool = True,
        stdout: Any = subprocess.PIPE, stderr: Any = subprocess.STDOUT,
        text: bool = True, env: dict[str, str] | None = None) -> subprocess.CompletedProcess:
    merged = os.environ.copy()
    if env:
        merged.update(env)
    return subprocess.run(
        command,
        cwd=cwd,
        check=check,
        stdout=stdout,
        stderr=stderr,
        text=text,
        env=merged,
    )


def git(*args: str, check: bool = True) -> str:
    cp = run(["git", *args], check=check)
    return (cp.stdout or "").strip()


def slugify(value: str) -> str:
    value = re.sub(r"[^A-Za-z0-9._-]+", "-", value).strip("-._")
    return value[:120] or "variant"


def extract_blocker_header(data: bytes) -> bytes:
    marker = f"theorem {BLOCKER}".encode()
    start = data.find(marker)
    if start < 0:
        raise RuntimeError(f"missing blocker theorem: {BLOCKER}")
    end_marker = b":= by"
    end = data.find(end_marker, start)
    if end < 0:
        raise RuntimeError(f"missing ':= by' for blocker theorem: {BLOCKER}")
    return data[start:end + len(end_marker)]


def declarations(text: str) -> list[dict[str, Any]]:
    out: list[dict[str, Any]] = []
    for index, match in enumerate(DECL_RE.finditer(text)):
        line = text.count("\n", 0, match.start()) + 1
        out.append({
            "index": index,
            "kind": match.group(1),
            "name": match.group(2),
            "line": line,
        })
    return out


def declaration_sequence_sha(text: str) -> str:
    seq = "\n".join(f"{d['kind']} {d['name']}" for d in declarations(text))
    return sha256_bytes(seq.encode())


def declaration_at_line(text: str, line: int) -> dict[str, Any]:
    ds = declarations(text)
    current = {"index": -1, "kind": "", "name": "<file-prefix>", "line": 0}
    for item in ds:
        if item["line"] > line:
            break
        current = item
    return current


def strip_comments_and_literals(text: str) -> str:
    out: list[str] = []
    i = 0
    block_depth = 0
    in_line = False
    in_string = False
    in_char = False
    escaped = False
    n = len(text)
    while i < n:
        ch = text[i]
        nxt = text[i + 1] if i + 1 < n else ""
        if in_line:
            if ch == "\n":
                in_line = False
                out.append("\n")
            else:
                out.append(" ")
            i += 1
            continue
        if block_depth:
            if ch == "/" and nxt == "-":
                block_depth += 1
                out.extend((" ", " "))
                i += 2
            elif ch == "-" and nxt == "/":
                block_depth -= 1
                out.extend((" ", " "))
                i += 2
            else:
                out.append("\n" if ch == "\n" else " ")
                i += 1
            continue
        if in_string:
            out.append("\n" if ch == "\n" else " ")
            if escaped:
                escaped = False
            elif ch == "\\":
                escaped = True
            elif ch == '"':
                in_string = False
            i += 1
            continue
        if in_char:
            out.append("\n" if ch == "\n" else " ")
            if escaped:
                escaped = False
            elif ch == "\\":
                escaped = True
            elif ch == "'":
                in_char = False
            i += 1
            continue
        if ch == "-" and nxt == "-":
            in_line = True
            out.extend((" ", " "))
            i += 2
        elif ch == "/" and nxt == "-":
            block_depth = 1
            out.extend((" ", " "))
            i += 2
        elif ch == '"':
            in_string = True
            out.append(" ")
            i += 1
        elif ch == "'" and nxt and (nxt.isalnum() or nxt == "\\"):
            in_char = True
            out.append(" ")
            i += 1
        else:
            out.append(ch)
            i += 1
    return "".join(out)


def trust_audit(text: str) -> dict[str, int]:
    code = strip_comments_and_literals(text)
    return {
        "sorry": len(re.findall(r"\bsorry\b", code)),
        "admit": len(re.findall(r"\badmit\b", code)),
        "global_axiom": len(re.findall(r"(?m)^\s*axiom\b", code)),
        "unsafe": len(re.findall(r"\bunsafe\b", code)),
        "native_decide": len(re.findall(r"\bnative_decide\b", code)),
        "Lean.ofReduceBool": len(re.findall(r"\bLean\.ofReduceBool\b", code)),
    }


def audit_clean(audit: dict[str, int]) -> bool:
    return all(value == 0 for value in audit.values())


def parse_first_error(log_text: str, source_text: str) -> dict[str, Any]:
    lines = log_text.splitlines()
    for i, raw in enumerate(lines):
        match = ERROR_RE.search(raw)
        if not match:
            continue
        line = int(match.group(1))
        col = int(match.group(2))
        message_lines = [match.group(3).strip()]
        for tail in lines[i + 1:i + 20]:
            if re.search(r"\.lean:\d+:\d+:\s+(?:error|warning)", tail):
                break
            message_lines.append(tail.rstrip())
        message = "\n".join(message_lines).strip()
        decl = declaration_at_line(source_text, line)
        return {
            "line": line,
            "column": col,
            "message": message,
            "declaration": decl["name"],
            "declaration_kind": decl["kind"],
            "declaration_index": decl["index"],
            "declaration_start_line": decl["line"],
        }
    return {
        "line": 0,
        "column": 0,
        "message": "",
        "declaration": "",
        "declaration_kind": "",
        "declaration_index": -1,
        "declaration_start_line": 0,
    }


def error_header_count(log_text: str) -> int:
    return len(re.findall(
        r"Mock2_FunctionalAnalysis\.lean:\d+:\d+:\s+error(?:\([^)]*\))?:",
        log_text,
    ))


def write_json(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


def read_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def append_github_output(**values: Any) -> None:
    output = os.environ.get("GITHUB_OUTPUT")
    if not output:
        return
    with open(output, "a", encoding="utf-8") as fh:
        for key, value in values.items():
            if isinstance(value, bool):
                rendered = str(value).lower()
            elif isinstance(value, (dict, list)):
                rendered = json.dumps(value, separators=(",", ":"))
            else:
                rendered = str(value)
            fh.write(f"{key}={rendered}\n")


def exact_command(command: Iterable[str]) -> str:
    import shlex
    return " ".join(shlex.quote(str(x)) for x in command)


def source_metadata(data: bytes) -> dict[str, Any]:
    text = data.decode("utf-8")
    header = extract_blocker_header(data)
    return {
        "sha256": sha256_bytes(data),
        "line_count": line_count_bytes(data),
        "blocker_header_sha256": sha256_bytes(header),
        "blocker_header": header.decode("utf-8"),
        "declaration_sequence_sha256": declaration_sequence_sha(text),
        "trust_audit": trust_audit(text),
    }
