from __future__ import annotations

import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from dataclasses import asdict, dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PSV = ROOT / "PrimalitySheafVerification"
TARGET = PSV / "Mock2_FunctionalAnalysis.lean"
OUT = ROOT / "build-logs" / "fa414-full-script-tournament"
OUT.mkdir(parents=True, exist_ok=True)

BASE_SHA = "07f6efd3309c3cc23b86adf5811918b752b72c33a3f7a76213ce9beb10796da4"
BASE_LINE = 31725
DONOR_BRANCHES = (
    "origin/fix/fa411-from-pass376-champion-20260809",
    "origin/fix/fa412-broad-from-pass376-20260809",
)
ERROR_RE = re.compile(
    r"Mock2_FunctionalAnalysis\.lean:(?P<line>\d+):(?P<col>\d+):\s*"
    r"error(?:\([^)]*\))?:\s*(?P<message>[^\n]*)"
)
DECL_RE = re.compile(
    r"^\s*(?:(?:public|private|protected|noncomputable|local|scoped)\s+)*"
    r"(?P<kind>theorem|lemma|corollary|def|abbrev|instance|structure|class)\b"
    r"(?:\s+(?P<name>[^\s:{(\[]+))?"
)
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
    first_col: int | None
    first_message: str
    artifacts_ok: bool
    sha256: str
    line_count: int
    line_delta: int
    normalized_first_line: int | None
    log: str

    @property
    def passed(self) -> bool:
        return self.exit_code == 0 and self.errors == 0 and self.artifacts_ok


def run(args: list[str], *, cwd: Path = ROOT, timeout: int = 600) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        args,
        cwd=cwd,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=timeout,
        check=False,
    )


def sha(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def normalize_ws(text: str) -> str:
    return re.sub(r"\s+", " ", text).strip()


def imports(text: str) -> tuple[str, ...]:
    return tuple(
        line.strip()
        for line in text.splitlines()
        if re.match(r"^\s*(?:public\s+)?import\s+", line)
    )


def strip_comments_and_strings(text: str) -> str:
    out: list[str] = []
    i = 0
    depth = 0
    in_string = False
    escaped = False
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1; out.extend("  "); i += 2; continue
            if text.startswith("-/", i):
                depth -= 1; out.extend("  "); i += 2; continue
            out.append("\n" if text[i] == "\n" else " "); i += 1; continue
        if in_string:
            ch = text[i]; out.append("\n" if ch == "\n" else " ")
            if escaped: escaped = False
            elif ch == "\\": escaped = True
            elif ch == '"': in_string = False
            i += 1; continue
        if text.startswith("/-", i):
            depth = 1; out.extend("  "); i += 2; continue
        if text.startswith("--", i):
            while i < len(text) and text[i] != "\n": out.append(" "); i += 1
            continue
        if text[i] == '"':
            in_string = True; out.append(" "); i += 1; continue
        out.append(text[i]); i += 1
    return "".join(out)


def forbidden(text: str) -> dict[str, int]:
    code = strip_comments_and_strings(text)
    return {name: len(pattern.findall(code)) for name, pattern in FORBIDDEN.items()}


def header(block: list[str]) -> str:
    prefix: list[str] = []
    for line in block:
        stripped = line.strip()
        if ":= by" in line:
            prefix.append(line.split(":= by", 1)[0]); break
        if ":=" in line:
            prefix.append(line.split(":=", 1)[0]); break
        if stripped == "by" or stripped.startswith("by "):
            break
        prefix.append(line)
        if stripped.endswith(" where") or stripped == "where":
            break
    return normalize_ws("\n".join(prefix))


def declaration_manifest(text: str) -> tuple[tuple[str, str | None, str], ...]:
    lines = text.splitlines()
    starts: list[tuple[int, re.Match[str]]] = []
    for i, line in enumerate(lines):
        m = DECL_RE.match(line)
        if m: starts.append((i, m))
    result: list[tuple[str, str | None, str]] = []
    for pos, (start, m) in enumerate(starts):
        end = starts[pos + 1][0] if pos + 1 < len(starts) else len(lines)
        result.append((m.group("kind"), m.group("name"), header(lines[start:end])))
    return tuple(result)


def remove_artifacts(stem: str) -> tuple[Path, Path]:
    out = ROOT / ".lake" / "build" / "lib" / "lean" / "PrimalitySheafVerification"
    out.mkdir(parents=True, exist_ok=True)
    olean = out / f"{stem}.olean"
    ilean = out / f"{stem}.ilean"
    for p in (olean, ilean, PSV / f"{stem}.olean", PSV / f"{stem}.ilean"):
        p.unlink(missing_ok=True)
    return olean, ilean


def compile_path(path: Path, label: str, base_lines: int, max_errors: int = 500) -> Metric:
    olean, ilean = remove_artifacts(path.stem)
    proc = run(
        [
            "lake", "env", "lean", f"-DmaxErrors={max_errors}",
            "-DwarningAsError=false", "-o", str(olean), "-i", str(ilean),
            str(path.relative_to(ROOT)),
        ],
        timeout=3600,
    )
    log_path = OUT / f"{label}.log"
    log_path.write_text(proc.stdout, encoding="utf-8")
    pattern = ERROR_RE if path == TARGET else re.compile(
        rf"{re.escape(path.name)}:(?P<line>\d+):(?P<col>\d+):\s*"
        r"error(?:\([^)]*\))?:\s*(?P<message>[^\n]*)"
    )
    matches = list(pattern.finditer(proc.stdout))
    first = matches[0] if matches else None
    text = path.read_text(encoding="utf-8")
    count = len(text.splitlines())
    delta = count - base_lines
    raw = int(first.group("line")) if first else None
    normalized = None if raw is None else raw - max(0, delta)
    return Metric(
        exit_code=proc.returncode,
        errors=len(matches),
        first_line=raw,
        first_col=int(first.group("col")) if first else None,
        first_message=first.group("message").strip() if first else "",
        artifacts_ok=proc.returncode == 0 and olean.exists() and olean.stat().st_size > 0
        and ilean.exists() and ilean.stat().st_size > 0,
        sha256=sha(text),
        line_count=count,
        line_delta=delta,
        normalized_first_line=normalized,
        log=str(log_path.relative_to(ROOT)),
    )


def strict_better(candidate: Metric, champion: Metric) -> bool:
    if candidate.passed:
        return True
    return (
        candidate.first_line is not None
        and candidate.normalized_first_line is not None
        and champion.first_line is not None
        and champion.normalized_first_line is not None
        and candidate.first_line > champion.first_line
        and candidate.normalized_first_line > champion.normalized_first_line
    )


def changed_scripts(ref: str) -> list[str]:
    base = "origin/champion/fa-pass376-31725-07f6efd-immutable"
    proc = run(["git", "diff", "--name-only", base, ref, "--", "scripts"], timeout=180)
    if proc.returncode != 0: return []
    return [p for p in proc.stdout.splitlines() if p.endswith(".py")]


def materialize(ref: str) -> list[tuple[str, str]]:
    donors: list[tuple[str, str]] = []
    temp_root = Path(tempfile.mkdtemp(prefix="fa414-donor-"))
    worktree = temp_root / "worktree"
    added = False
    try:
        proc = run(["git", "worktree", "add", "--detach", str(worktree), ref], timeout=300)
        if proc.returncode != 0: return donors
        added = True
        path = worktree / "PrimalitySheafVerification" / TARGET.name
        initial = path.read_bytes()
        donors.append((f"{ref}:checked-in-source", path.read_text(encoding="utf-8")))
        scripts = changed_scripts(ref)
        for script in scripts:
            path.write_bytes(initial)
            result = run([sys.executable, script], cwd=worktree, timeout=240)
            if result.returncode == 0:
                donors.append((f"{ref}:{script}", path.read_text(encoding="utf-8")))
        path.write_bytes(initial)
        ok = True
        for script in scripts:
            result = run([sys.executable, script], cwd=worktree, timeout=240)
            if result.returncode != 0:
                ok = False; break
        if ok and scripts:
            donors.append((f"{ref}:all-changed-scripts", path.read_text(encoding="utf-8")))
    finally:
        if added:
            run(["git", "worktree", "remove", "--force", str(worktree)], timeout=300)
        shutil.rmtree(temp_root, ignore_errors=True)
    return donors


def compile_prerequisites() -> dict[str, dict[str, object]]:
    rows: dict[str, dict[str, object]] = {}
    for stem in ("Mock2", "Mock2_Advanced"):
        path = PSV / f"{stem}.lean"
        metric = compile_path(path, f"{stem}-prerequisite", len(path.read_text().splitlines()), 500)
        rows[stem] = asdict(metric)
        if not metric.passed:
            raise RuntimeError(f"prerequisite {stem} failed: {metric}")
    return rows


def verify_twice(base_lines: int) -> dict[str, list[dict[str, object]]]:
    integrated = PSV / "Mock2_FunctionalAnalysis_Integrated.lean"
    mock3 = sorted(PSV.glob("Mock3*.lean"))
    qym = PSV / "QYM.lean"
    if not integrated.exists(): raise RuntimeError("Integrated source missing")
    if not mock3: raise RuntimeError("Mock3*.lean source missing")
    if not qym.exists(): raise RuntimeError("QYM.lean source missing")
    paths = [TARGET, integrated, *mock3, qym]
    rows: dict[str, list[dict[str, object]]] = {}
    for path in paths:
        plines = base_lines if path == TARGET else len(path.read_text().splitlines())
        runs = []
        for n in (1, 2):
            metric = compile_path(path, f"{path.stem}-run{n}", plines, 500)
            runs.append(asdict(metric))
            if not metric.passed:
                raise RuntimeError(f"{path.name} run {n} failed: {metric}")
        rows[path.stem] = runs
    (OUT / "ALL_REQUIRED_TARGETS_2X_PASS").write_text(
        "\n".join(f"{name}=PASSx2" for name in rows) + "\n", encoding="utf-8"
    )
    return rows


def main() -> int:
    baseline = TARGET.read_text(encoding="utf-8")
    if sha(baseline) != BASE_SHA:
        raise SystemExit(f"baseline SHA mismatch: {sha(baseline)}")
    base_lines = len(baseline.splitlines())
    base_imports = imports(baseline)
    base_manifest = declaration_manifest(baseline)
    if any(forbidden(baseline).values()):
        raise SystemExit(f"baseline forbidden-token failure: {forbidden(baseline)}")

    fetch = run(["git", "fetch", "origin", "+refs/heads/*:refs/remotes/origin/*", "--prune"], timeout=900)
    if fetch.returncode != 0: raise SystemExit(fetch.stdout[-5000:])
    prerequisites = compile_prerequisites()
    champion = compile_path(TARGET, "baseline-authoritative", base_lines, 500)
    if champion.passed or champion.first_line != BASE_LINE:
        raise SystemExit(f"unexpected immutable metric: {champion}")

    donor_rows: list[dict[str, object]] = []
    seen = {BASE_SHA}
    best_text = baseline
    best_metric = champion
    best_label = "immutable-pass376"

    donors: list[tuple[str, str]] = []
    for ref in DONOR_BRANCHES:
        donors.extend(materialize(ref))

    for index, (label, candidate) in enumerate(donors, 1):
        digest = sha(candidate)
        if digest in seen: continue
        seen.add(digest)
        rejection = None
        if imports(candidate) != base_imports:
            rejection = "import manifest changed"
        elif declaration_manifest(candidate) != base_manifest:
            rejection = "declaration header manifest changed"
        elif any(forbidden(candidate).values()):
            rejection = f"forbidden tokens: {forbidden(candidate)}"
        if rejection:
            donor_rows.append({"label": label, "sha256": digest, "rejected": rejection})
            continue

        TARGET.write_text(candidate, encoding="utf-8")
        metric = compile_path(TARGET, f"candidate-{index:02d}", base_lines, 500)
        better = strict_better(metric, best_metric)
        donor_rows.append({"label": label, "metric": asdict(metric), "strict_better": better})
        if better:
            best_text = candidate
            best_metric = metric
            best_label = label
        TARGET.write_text(baseline, encoding="utf-8")

    TARGET.write_text(best_text, encoding="utf-8")
    authoritative = compile_path(TARGET, "selected-authoritative", base_lines, 500)
    if best_label != "immutable-pass376" and not strict_better(authoritative, champion):
        TARGET.write_text(baseline, encoding="utf-8")
        raise SystemExit(f"selected source failed strict authoritative replay: {authoritative}")

    complete = False
    two_pass: dict[str, list[dict[str, object]]] = {}
    downstream_failure = None
    if authoritative.passed:
        try:
            two_pass = verify_twice(base_lines)
            complete = True
        except Exception as exc:
            downstream_failure = repr(exc)

    first = authoritative.first_line or 1
    lines = TARGET.read_text(encoding="utf-8").splitlines()
    start, end = max(1, first - 50), min(len(lines), first + 80)
    (OUT / "FIRST_ERROR_CONTEXT.txt").write_text(
        "\n".join(f"{i}: {lines[i-1]}" for i in range(start, end + 1)),
        encoding="utf-8",
    )
    status = {
        "complete": complete,
        "stage": "ALL_REQUIRED_TARGETS_2X_PASS" if complete else "Mock2_FunctionalAnalysis",
        "immutable_baseline": {"sha256": BASE_SHA, "first_error_line": BASE_LINE},
        "promotion_rule": "exit 0, or both raw and positive-line-delta-normalized first error strictly later; never error-count-only",
        "prerequisites": prerequisites,
        "baseline_metric": asdict(champion),
        "selected_label": best_label,
        "selected_metric": asdict(authoritative),
        "candidate_results": donor_rows,
        "declaration_manifest_unchanged": declaration_manifest(TARGET.read_text()) == base_manifest,
        "forbidden_token_audit": forbidden(TARGET.read_text()),
        "two_pass": two_pass,
        "downstream_failure": downstream_failure,
    }
    (OUT / "CURRENT.json").write_text(json.dumps(status, indent=2), encoding="utf-8")
    (OUT / "CURRENT.txt").write_text(
        f"complete={complete}\nstage={status['stage']}\nselected={best_label}\n"
        f"fa_exit={authoritative.exit_code}\nfa_first={authoritative.first_line}:{authoritative.first_col}\n"
        f"fa_normalized_first={authoritative.normalized_first_line}\nfa_sha256={authoritative.sha256}\n",
        encoding="utf-8",
    )
    print(json.dumps(status, indent=2))
    return 0 if complete else 2


if __name__ == "__main__":
    raise SystemExit(main())
