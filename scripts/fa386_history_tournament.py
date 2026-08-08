from __future__ import annotations

import argparse
import concurrent.futures
import hashlib
import json
import os
import re
import shutil
import subprocess
import tempfile
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
ERROR_HEADER = re.compile(r"[^\n:]*\.lean:(?P<line>\d+):(?P<col>\d+):\s*error:")
FORBIDDEN = {
    "sorry": re.compile(r"\bsorry\b"),
    "admit": re.compile(r"\badmit\b"),
    "global_axiom": re.compile(r"(?m)^\s*(?:public\s+)?axiom\b"),
    "unsafe": re.compile(r"(?m)^\s*unsafe\b"),
    "native_decide": re.compile(r"\bnative_decide\b"),
    "Lean.ofReduceBool": re.compile(r"\bLean\.ofReduceBool\b"),
}


@dataclass(frozen=True)
class Metric:
    exit_code: int
    errors: int
    first_line: int | None
    sha256: str
    source_label: str

    def score(self) -> tuple[int, int, int]:
        return (
            1 if self.exit_code == 0 and self.errors == 0 else 0,
            -self.errors,
            self.first_line if self.first_line is not None else 10**9,
        )


def run(
    args: list[str],
    *,
    cwd: Path = ROOT,
    timeout: int | None = None,
    input_bytes: bytes | None = None,
) -> subprocess.CompletedProcess:
    return subprocess.run(
        args,
        cwd=cwd,
        input=input_bytes,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=timeout,
        check=False,
    )


def strip_comments_and_strings(text: str) -> str:
    out: list[str] = []
    i = 0
    depth = 0
    string = False
    escaped = False
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1
                out.extend("  ")
                i += 2
                continue
            if text.startswith("-/", i):
                depth -= 1
                out.extend("  ")
                i += 2
                continue
            out.append("\n" if text[i] == "\n" else " ")
            i += 1
            continue
        if string:
            ch = text[i]
            out.append("\n" if ch == "\n" else " ")
            if escaped:
                escaped = False
            elif ch == "\\":
                escaped = True
            elif ch == '"':
                string = False
            i += 1
            continue
        if text.startswith("/-", i):
            depth = 1
            out.extend("  ")
            i += 2
            continue
        if text.startswith("--", i):
            while i < len(text) and text[i] != "\n":
                out.append(" ")
                i += 1
            continue
        if text[i] == '"':
            string = True
            out.append(" ")
            i += 1
            continue
        out.append(text[i])
        i += 1
    return "".join(out)


def declaration_headers(text: str) -> dict[str, str]:
    code = strip_comments_and_strings(text)
    pattern = re.compile(
        r"(?m)^(?P<indent>\s*)"
        r"(?P<prefix>(?:(?:private|public|protected|noncomputable)\s+)*)"
        r"(?P<kind>theorem|lemma|corollary)\s+(?P<name>[^\s(:{\[]+)"
    )
    result: dict[str, str] = {}
    for match in pattern.finditer(code):
        if "private" in match.group("prefix").split():
            continue
        i = match.end()
        paren = bracket = brace = 0
        delimiter = None
        while i < len(code):
            ch = code[i]
            if ch == "(":
                paren += 1
            elif ch == ")":
                paren = max(0, paren - 1)
            elif ch == "[":
                bracket += 1
            elif ch == "]":
                bracket = max(0, bracket - 1)
            elif ch == "{":
                brace += 1
            elif ch == "}":
                brace = max(0, brace - 1)
            elif (
                ch == ":"
                and i + 1 < len(code)
                and code[i + 1] == "="
                and paren == bracket == brace == 0
            ):
                delimiter = i
                break
            i += 1
        if delimiter is None:
            continue
        result[match.group("name")] = re.sub(
            r"\s+", " ", code[match.start() : delimiter].strip()
        )
    return result


def candidate_is_safe(candidate: bytes, baseline_headers: dict[str, str]) -> tuple[bool, str]:
    try:
        text = candidate.decode("utf-8")
    except UnicodeDecodeError as exc:
        return False, f"non-UTF8 source: {exc}"
    code = strip_comments_and_strings(text)
    counts = {name: len(pattern.findall(code)) for name, pattern in FORBIDDEN.items()}
    if any(counts.values()):
        return False, f"forbidden executable tokens: {counts}"
    headers = declaration_headers(text)
    missing = sorted(set(baseline_headers) - set(headers))
    changed = sorted(
        name
        for name in baseline_headers.keys() & headers.keys()
        if baseline_headers[name] != headers[name]
    )
    if missing or changed:
        return False, f"public statement change: missing={missing[:8]} changed={changed[:8]}"
    return True, "ok"


def remote_refs() -> list[str]:
    proc = run(
        [
            "git",
            "for-each-ref",
            "--sort=-committerdate",
            "--format=%(refname)",
            "refs/remotes/origin/fix/fa*",
        ]
    )
    return [line.strip() for line in proc.stdout.decode().splitlines() if line.strip()]


def paths_for_ref(ref: str) -> list[str]:
    proc = run(["git", "ls-tree", "-r", "--name-only", ref], timeout=120)
    paths = []
    for line in proc.stdout.decode(errors="replace").splitlines():
        if line == "PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean":
            paths.append(line)
        elif line.endswith("best-source.lean") and "fa" in line.lower():
            paths.append(line)
        elif (
            "Mock2_FunctionalAnalysis-pass" in line
            and line.endswith(".lean")
            and ("build-logs" in line or "source" in line)
        ):
            paths.append(line)
    # Prefer the checked-in source, then latest agent best sources.
    return paths[:20]


def git_show(ref: str, path: str) -> bytes | None:
    proc = run(["git", "show", f"{ref}:{path}"], timeout=120)
    return proc.stdout if proc.returncode == 0 and proc.stdout else None


def collect_candidates(
    output: Path,
    max_refs: int,
    baseline_headers: dict[str, str],
) -> list[dict[str, str]]:
    candidates_dir = output / "candidates"
    candidates_dir.mkdir(parents=True, exist_ok=True)
    seen: set[str] = set()
    manifest: list[dict[str, str]] = []

    def add(data: bytes, label: str, ref: str, source_path: str) -> None:
        digest = hashlib.sha256(data).hexdigest()
        if digest in seen:
            return
        safe, reason = candidate_is_safe(data, baseline_headers)
        if not safe:
            manifest.append(
                {
                    "sha256": digest,
                    "label": label,
                    "ref": ref,
                    "source_path": source_path,
                    "accepted_for_compile": "false",
                    "rejection": reason,
                }
            )
            return
        seen.add(digest)
        file_path = candidates_dir / f"candidate-{len(seen):04d}-{digest[:12]}.lean"
        file_path.write_bytes(data)
        manifest.append(
            {
                "sha256": digest,
                "label": label,
                "ref": ref,
                "source_path": source_path,
                "accepted_for_compile": "true",
                "local_path": str(file_path),
            }
        )

    baseline_data = TARGET.read_bytes()
    add(baseline_data, "current-branch-source", "HEAD", str(TARGET.relative_to(ROOT)))
    for ref in remote_refs()[:max_refs]:
        for path in paths_for_ref(ref):
            data = git_show(ref, path)
            if data is not None:
                add(data, f"{ref}:{path}", ref, path)
    (output / "candidate-manifest.json").write_text(
        json.dumps(manifest, indent=2), encoding="utf-8"
    )
    return [item for item in manifest if item.get("accepted_for_compile") == "true"]


def compile_candidate(item: dict[str, str], output: Path) -> dict[str, object]:
    path = Path(item["local_path"])
    digest = item["sha256"]
    # Keep the temporary source inside the project tree so all project imports resolve exactly.
    temp_path = ROOT / "PrimalitySheafVerification" / f"_FA386Candidate_{digest[:16]}.lean"
    temp_path.write_bytes(path.read_bytes())
    try:
        proc = run(
            [
                "lake",
                "env",
                "lean",
                "-DmaxErrors=160",
                str(temp_path.relative_to(ROOT)),
            ],
            timeout=2400,
        )
        log = proc.stdout.decode("utf-8", errors="replace")
        matches = list(ERROR_HEADER.finditer(log))
        result = {
            **item,
            "exit_code": proc.returncode,
            "errors": len(matches),
            "first_line": int(matches[0].group("line")) if matches else None,
            "log_path": str(output / "logs" / f"{digest}.log"),
        }
        logs = output / "logs"
        logs.mkdir(parents=True, exist_ok=True)
        Path(result["log_path"]).write_text(log, encoding="utf-8")
        return result
    except subprocess.TimeoutExpired as exc:
        log = (exc.stdout or b"").decode("utf-8", errors="replace") if isinstance(exc.stdout, bytes) else str(exc.stdout or "")
        logs = output / "logs"
        logs.mkdir(parents=True, exist_ok=True)
        log_path = logs / f"{digest}.log"
        log_path.write_text(log + "\n[TIMEOUT]\n", encoding="utf-8")
        return {
            **item,
            "exit_code": 124,
            "errors": 10**6,
            "first_line": None,
            "log_path": str(log_path),
            "timeout": True,
        }
    finally:
        temp_path.unlink(missing_ok=True)
        temp_path.with_suffix(".olean").unlink(missing_ok=True)
        temp_path.with_suffix(".ilean").unlink(missing_ok=True)


def result_score(item: dict[str, object]) -> tuple[int, int, int]:
    exit_code = int(item.get("exit_code", 1))
    errors = int(item.get("errors", 10**6))
    first_line = item.get("first_line")
    return (
        1 if exit_code == 0 and errors == 0 else 0,
        -errors,
        int(first_line) if first_line is not None else -1,
    )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output-dir", required=True)
    parser.add_argument("--max-refs", type=int, default=80)
    parser.add_argument("--max-candidates", type=int, default=80)
    parser.add_argument("--workers", type=int, default=2)
    args = parser.parse_args()

    output = Path(args.output_dir)
    output.mkdir(parents=True, exist_ok=True)
    baseline_headers = declaration_headers(TARGET.read_text(encoding="utf-8"))
    candidates = collect_candidates(output, args.max_refs, baseline_headers)
    candidates = candidates[: args.max_candidates]
    results: list[dict[str, object]] = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as pool:
        futures = [pool.submit(compile_candidate, item, output) for item in candidates]
        for future in concurrent.futures.as_completed(futures):
            result = future.result()
            results.append(result)
            (output / "partial-results.json").write_text(
                json.dumps(results, indent=2), encoding="utf-8"
            )
            print(
                f"[fa386] {result.get('sha256')} exit={result.get('exit_code')} "
                f"errors={result.get('errors')} first={result.get('first_line')}"
            )
    if not results:
        raise RuntimeError("no safe historical candidates were collected")
    results.sort(key=result_score, reverse=True)
    best = results[0]
    best_source = Path(str(best["local_path"]))
    shutil.copy2(best_source, output / "best-source.lean")
    metric = {
        "exit_code": int(best["exit_code"]),
        "errors": int(best["errors"]),
        "first_line": best.get("first_line"),
        "source_sha256": str(best["sha256"]),
    }
    (output / "best-metric.json").write_text(
        json.dumps(metric, indent=2), encoding="utf-8"
    )
    (output / "tournament-results.json").write_text(
        json.dumps(results, indent=2), encoding="utf-8"
    )
    (output / "state.json").write_text(
        json.dumps(
            {
                "candidate_count": len(candidates),
                "compiled_count": len(results),
                "best": best,
                "complete_fa": metric["exit_code"] == 0 and metric["errors"] == 0,
            },
            indent=2,
        ),
        encoding="utf-8",
    )
    return 0 if metric["exit_code"] == 0 and metric["errors"] == 0 else 2


if __name__ == "__main__":
    raise SystemExit(main())
