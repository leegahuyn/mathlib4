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
from typing import Iterable

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
PSV = ROOT / "PrimalitySheafVerification"
OUT = ROOT / "build-logs" / "fa413-strict-transplant"
OUT.mkdir(parents=True, exist_ok=True)

EXPECTED_INITIAL_SHA256 = "07f6efd3309c3cc23b86adf5811918b752b72c33a3f7a76213ce9beb10796da4"
INITIAL_CHAMPION_LINE = 31725
MAX_FRONTIERS = int(os.environ.get("FA413_MAX_FRONTIERS", "8"))
MAX_CANDIDATES = int(os.environ.get("FA413_MAX_CANDIDATES", "28"))

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
    source_sha256: str
    log_path: str

    @property
    def passed(self) -> bool:
        return self.exit_code == 0 and self.errors == 0 and self.artifacts_ok


@dataclass(frozen=True)
class Declaration:
    start: int
    end: int
    kind: str
    name: str | None
    header: str

    @property
    def lines(self) -> int:
        return self.end - self.start


def run(
    args: list[str],
    *,
    cwd: Path = ROOT,
    timeout: int | None = None,
    check: bool = False,
) -> subprocess.CompletedProcess[str]:
    proc = subprocess.run(
        args,
        cwd=cwd,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=timeout,
        check=False,
    )
    if check and proc.returncode != 0:
        raise RuntimeError(f"command failed ({proc.returncode}): {' '.join(args)}\n{proc.stdout[-5000:]}")
    return proc


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def strip_comments_and_strings(text: str) -> str:
    out: list[str] = []
    i = 0
    depth = 0
    in_string = False
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
        if in_string:
            ch = text[i]
            out.append("\n" if ch == "\n" else " ")
            if escaped:
                escaped = False
            elif ch == "\\":
                escaped = True
            elif ch == '"':
                in_string = False
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
            in_string = True
            out.append(" ")
            i += 1
            continue
        out.append(text[i])
        i += 1
    return "".join(out)


def forbidden_hits(text: str) -> dict[str, int]:
    code = strip_comments_and_strings(text)
    return {name: len(pattern.findall(code)) for name, pattern in FORBIDDEN.items()}


def imports(text: str) -> tuple[str, ...]:
    return tuple(
        line.strip()
        for line in text.splitlines()
        if re.match(r"^\s*(?:public\s+)?import\s+", line)
    )


def normalize_ws(text: str) -> str:
    return re.sub(r"\s+", " ", text).strip()


def header_of(block: list[str]) -> str:
    prefix: list[str] = []
    for line in block:
        stripped = line.strip()
        if ":= by" in line:
            prefix.append(line.split(":= by", 1)[0])
            break
        if ":=" in line:
            prefix.append(line.split(":=", 1)[0])
            break
        if stripped == "by" or stripped.startswith("by "):
            break
        prefix.append(line)
        if stripped.endswith(" where") or stripped == "where":
            break
    return normalize_ws("\n".join(prefix))


def declarations(text: str) -> list[Declaration]:
    lines = text.splitlines()
    starts: list[tuple[int, re.Match[str]]] = []
    for i, line in enumerate(lines):
        match = DECL_RE.match(line)
        if match:
            starts.append((i, match))
    result: list[Declaration] = []
    for pos, (start, match) in enumerate(starts):
        end = starts[pos + 1][0] if pos + 1 < len(starts) else len(lines)
        result.append(
            Declaration(
                start=start,
                end=end,
                kind=match.group("kind"),
                name=match.group("name"),
                header=header_of(lines[start:end]),
            )
        )
    return result


def declaration_at(text: str, one_based_line: int) -> Declaration | None:
    idx = max(0, one_based_line - 1)
    found: Declaration | None = None
    for decl in declarations(text):
        if decl.start <= idx < decl.end:
            return decl
        if decl.start <= idx:
            found = decl
    return found


def matching_declaration(text: str, wanted: Declaration) -> Declaration | None:
    ds = declarations(text)
    exact = [
        d
        for d in ds
        if d.kind == wanted.kind and d.name == wanted.name and d.header == wanted.header
    ]
    if len(exact) == 1:
        return exact[0]
    same_header = [d for d in ds if d.kind == wanted.kind and d.header == wanted.header]
    if len(same_header) == 1:
        return same_header[0]
    return None


def replace_declaration_same_height(
    base: str, base_decl: Declaration, donor: str, donor_decl: Declaration
) -> str | None:
    base_lines = base.splitlines()
    donor_lines = donor.splitlines()[donor_decl.start : donor_decl.end]
    if len(donor_lines) > base_decl.lines:
        return None
    donor_lines = donor_lines + [""] * (base_decl.lines - len(donor_lines))
    rebuilt = (
        base_lines[: base_decl.start]
        + donor_lines
        + base_lines[base_decl.end :]
    )
    return "\n".join(rebuilt) + ("\n" if base.endswith("\n") else "")


def remove_artifacts(stem: str) -> None:
    for suffix in ("olean", "ilean"):
        for path in (
            PSV / f"{stem}.{suffix}",
            ROOT / ".lake" / "build" / "lib" / "lean" / "PrimalitySheafVerification" / f"{stem}.{suffix}",
        ):
            path.unlink(missing_ok=True)


def compile_fa(label: str, max_errors: int = 80) -> Metric:
    stem = TARGET.stem
    remove_artifacts(stem)
    out_dir = ROOT / ".lake" / "build" / "lib" / "lean" / "PrimalitySheafVerification"
    out_dir.mkdir(parents=True, exist_ok=True)
    olean = out_dir / f"{stem}.olean"
    ilean = out_dir / f"{stem}.ilean"
    proc = run(
        [
            "lake",
            "env",
            "lean",
            f"-DmaxErrors={max_errors}",
            "-DwarningAsError=false",
            "-o",
            str(olean),
            "-i",
            str(ilean),
            str(TARGET.relative_to(ROOT)),
        ],
        timeout=2700,
    )
    log_path = OUT / f"{label}.log"
    log_path.write_text(proc.stdout, encoding="utf-8")
    matches = list(ERROR_RE.finditer(proc.stdout))
    first = matches[0] if matches else None
    return Metric(
        exit_code=proc.returncode,
        errors=len(matches),
        first_line=int(first.group("line")) if first else None,
        first_col=int(first.group("col")) if first else None,
        first_message=first.group("message").strip() if first else "",
        artifacts_ok=proc.returncode == 0 and olean.exists() and olean.stat().st_size > 0
        and ilean.exists() and ilean.stat().st_size > 0,
        source_sha256=sha256_file(TARGET),
        log_path=str(log_path.relative_to(ROOT)),
    )


def compile_module(path: Path, label: str, run_number: int) -> Metric:
    stem = path.stem
    remove_artifacts(stem)
    out_dir = ROOT / ".lake" / "build" / "lib" / "lean" / "PrimalitySheafVerification"
    out_dir.mkdir(parents=True, exist_ok=True)
    olean = out_dir / f"{stem}.olean"
    ilean = out_dir / f"{stem}.ilean"
    proc = run(
        [
            "lake",
            "env",
            "lean",
            "-DmaxErrors=500",
            "-DwarningAsError=false",
            "-o",
            str(olean),
            "-i",
            str(ilean),
            str(path.relative_to(ROOT)),
        ],
        timeout=3600,
    )
    log_path = OUT / f"{label}-run{run_number}.log"
    log_path.write_text(proc.stdout, encoding="utf-8")
    pattern = re.compile(
        rf"{re.escape(path.name)}:(?P<line>\d+):(?P<col>\d+):\s*"
        r"error(?:\([^)]*\))?:\s*(?P<message>[^\n]*)"
    )
    matches = list(pattern.finditer(proc.stdout))
    first = matches[0] if matches else None
    return Metric(
        exit_code=proc.returncode,
        errors=len(matches),
        first_line=int(first.group("line")) if first else None,
        first_col=int(first.group("col")) if first else None,
        first_message=first.group("message").strip() if first else "",
        artifacts_ok=proc.returncode == 0 and olean.exists() and olean.stat().st_size > 0
        and ilean.exists() and ilean.stat().st_size > 0,
        source_sha256=sha256_file(path),
        log_path=str(log_path.relative_to(ROOT)),
    )


def strict_better(candidate: Metric, champion: Metric) -> bool:
    if candidate.passed:
        return True
    return (
        candidate.first_line is not None
        and champion.first_line is not None
        and candidate.first_line > champion.first_line
    )


def branch_priority(name: str) -> tuple[int, int, str]:
    preferred = 1 if ("fa411" in name or "fa412" in name) else 0
    numbers = [int(x) for x in re.findall(r"fa(\d+)", name)]
    number = max(numbers) if numbers else -1
    return (preferred, number, name)


def remote_branches() -> list[str]:
    run(
        ["git", "fetch", "origin", "+refs/heads/*:refs/remotes/origin/*", "--prune"],
        timeout=900,
        check=True,
    )
    proc = run(
        ["git", "for-each-ref", "--format=%(refname:short)", "refs/remotes/origin"],
        check=True,
    )
    names = []
    for line in proc.stdout.splitlines():
        if line.endswith("/HEAD"):
            continue
        short = line.removeprefix("origin/")
        if re.search(r"(?:^|/)(?:fix|probe|materialized|champion)/", short) or "fa" in short.lower():
            names.append(line)
    return sorted(set(names), key=branch_priority, reverse=True)


def git_show(ref: str, path: str) -> str | None:
    proc = run(["git", "show", f"{ref}:{path}"], timeout=120)
    return proc.stdout if proc.returncode == 0 else None


def changed_python_scripts(ref: str) -> list[str]:
    base = "origin/champion/fa-pass376-31725-07f6efd-immutable"
    proc = run(["git", "diff", "--name-only", base, ref, "--", "scripts"], timeout=120)
    if proc.returncode != 0:
        return []
    return [
        p
        for p in proc.stdout.splitlines()
        if p.endswith(".py")
        and any(token in Path(p).name.lower() for token in ("411", "412", "pass376", "champion", "broad"))
    ]


def scripted_donors(ref: str) -> Iterable[tuple[str, str]]:
    if "fa411" not in ref and "fa412" not in ref:
        return []
    scripts = changed_python_scripts(ref)
    if not scripts:
        return []
    donors: list[tuple[str, str]] = []
    with tempfile.TemporaryDirectory(prefix="fa413-donor-") as td:
        work = Path(td)
        archive = run(["git", "archive", ref], timeout=300)
        if archive.returncode != 0:
            return donors
        # git archive is binary; use a detached worktree instead.
    worktree = Path(tempfile.mkdtemp(prefix="fa413-worktree-"))
    try:
        add = run(["git", "worktree", "add", "--detach", str(worktree), ref], timeout=300)
        if add.returncode != 0:
            return donors
        donor_target = worktree / "PrimalitySheafVerification" / TARGET.name
        initial = donor_target.read_bytes()
        for script in scripts:
            donor_target.write_bytes(initial)
            proc = run([sys.executable, script], cwd=worktree, timeout=180)
            if proc.returncode == 0 and donor_target.exists():
                donors.append((f"{ref}:{script}", donor_target.read_text(encoding="utf-8")))
        donor_target.write_bytes(initial)
        cumulative_ok = True
        for script in scripts:
            proc = run([sys.executable, script], cwd=worktree, timeout=180)
            if proc.returncode != 0:
                cumulative_ok = False
                break
        if cumulative_ok:
            donors.append((f"{ref}:cumulative-scripts", donor_target.read_text(encoding="utf-8")))
    finally:
        run(["git", "worktree", "remove", "--force", str(worktree)], timeout=300)
        shutil.rmtree(worktree, ignore_errors=True)
    return donors


def donor_sources(branches: list[str]) -> Iterable[tuple[str, str]]:
    path = str(TARGET.relative_to(ROOT))
    for ref in branches:
        source = git_show(ref, path)
        if source is not None:
            yield ref, source
        for item in scripted_donors(ref):
            yield item


def valid_donor(text: str, expected_imports: tuple[str, ...]) -> bool:
    if imports(text) != expected_imports:
        return False
    return not any(forbidden_hits(text).values())


def generic_candidates(base: str, decl: Declaration) -> Iterable[tuple[str, str]]:
    lines = base.splitlines()
    block = lines[decl.start : decl.end]
    variants: dict[str, list[str]] = {}

    variants["remove-local-complex-addcommgroup"] = [
        line
        for line in block
        if not re.match(r"^\s*(?:letI|haveI)\s*:\s*AddCommGroup\s+ℂ\s*:=", line)
    ]
    variants["remove-local-complex-real-module"] = [
        line
        for line in block
        if not re.match(r"^\s*(?:letI|haveI)\s*:\s*Module\s+ℝ\s+ℂ\s*:=", line)
    ]
    variants["replace-legacy-complex-addcommgroup"] = [
        line.replace(
            "Complex.addCommGroup",
            "Complex.instNormedAddCommGroup.toAddCommGroup",
        )
        for line in block
    ]
    variants["replace-inferred-complex-addcommgroup"] = [
        line.replace(
            "(inferInstance : AddCommGroup ℂ)",
            "Complex.instNormedAddCommGroup.toAddCommGroup",
        )
        for line in block
    ]

    for label, candidate_block in variants.items():
        if candidate_block == block or len(candidate_block) > len(block):
            continue
        padded = candidate_block + [""] * (len(block) - len(candidate_block))
        candidate = lines[: decl.start] + padded + lines[decl.end :]
        yield label, "\n".join(candidate) + ("\n" if base.endswith("\n") else "")


def write_frontier_context(source: str, metric: Metric, frontier: int) -> None:
    lines = source.splitlines()
    line = metric.first_line or 1
    start = max(1, line - 45)
    end = min(len(lines), line + 65)
    context = "\n".join(f"{i}: {lines[i - 1]}" for i in range(start, end + 1))
    (OUT / f"frontier-{frontier:02d}-context.txt").write_text(context, encoding="utf-8")
    log = ROOT / metric.log_path
    text = log.read_text(encoding="utf-8", errors="replace") if log.exists() else ""
    first = ERROR_RE.search(text)
    block = text[first.start() : first.start() + 14000] if first else text[-14000:]
    (OUT / f"frontier-{frontier:02d}-first-error.txt").write_text(block, encoding="utf-8")


def verify_prerequisites() -> dict[str, dict[str, object]]:
    rows: dict[str, dict[str, object]] = {}
    for stem in ("Mock2", "Mock2_Advanced"):
        path = PSV / f"{stem}.lean"
        metric = compile_module(path, stem, 1)
        rows[stem] = asdict(metric)
        if not metric.passed:
            raise RuntimeError(f"required prerequisite {stem} failed: {metric}")
    return rows


def verify_all_twice() -> dict[str, list[dict[str, object]]]:
    paths: list[Path] = [TARGET]
    integrated = PSV / "Mock2_FunctionalAnalysis_Integrated.lean"
    if not integrated.exists():
        raise RuntimeError("Mock2_FunctionalAnalysis_Integrated.lean is missing")
    paths.append(integrated)
    mock3 = sorted(PSV.glob("Mock3*.lean"))
    if not mock3:
        raise RuntimeError("no Mock3*.lean source exists")
    paths.extend(mock3)
    qym = PSV / "QYM.lean"
    if not qym.exists():
        raise RuntimeError("QYM.lean is missing")
    paths.append(qym)

    rows: dict[str, list[dict[str, object]]] = {}
    for path in paths:
        runs: list[dict[str, object]] = []
        for run_number in (1, 2):
            metric = compile_module(path, path.stem, run_number)
            runs.append(asdict(metric))
            if not metric.passed:
                raise RuntimeError(f"{path.name} direct run {run_number} failed: {metric}")
        rows[path.stem] = runs
    (OUT / "ALL_REQUIRED_TARGETS_2X_PASS").write_text(
        "\n".join(f"{name}=PASSx2" for name in rows) + "\n",
        encoding="utf-8",
    )
    return rows


def main() -> int:
    initial_sha = sha256_file(TARGET)
    prior_status = OUT / "CURRENT.json"
    if initial_sha != EXPECTED_INITIAL_SHA256 and not prior_status.exists():
        raise SystemExit(
            f"untrusted initial source SHA256 {initial_sha}; expected immutable champion {EXPECTED_INITIAL_SHA256}"
        )

    source = TARGET.read_text(encoding="utf-8")
    if any(forbidden_hits(source).values()):
        raise SystemExit(f"champion contains forbidden executable tokens: {forbidden_hits(source)}")
    expected_imports = imports(source)
    prereq = verify_prerequisites()
    branches = remote_branches()

    history: list[dict[str, object]] = []
    metric = compile_fa("frontier-00-baseline", max_errors=500)
    if not metric.passed and (metric.first_line is None or metric.first_line < INITIAL_CHAMPION_LINE):
        raise SystemExit(f"baseline regressed below immutable champion: {metric}")

    for frontier in range(1, MAX_FRONTIERS + 1):
        source = TARGET.read_text(encoding="utf-8")
        write_frontier_context(source, metric, frontier)
        if metric.passed:
            break
        assert metric.first_line is not None
        current_decl = declaration_at(source, metric.first_line)
        if current_decl is None:
            history.append(
                {
                    "frontier": frontier,
                    "champion": asdict(metric),
                    "reason": "no enclosing declaration found",
                    "candidates": [],
                }
            )
            break

        candidates: list[tuple[str, str]] = []
        seen = {sha256_bytes(source.encode("utf-8"))}
        for label, donor in donor_sources(branches):
            if len(candidates) >= MAX_CANDIDATES:
                break
            if not valid_donor(donor, expected_imports):
                continue
            donor_decl = matching_declaration(donor, current_decl)
            if donor_decl is None:
                continue
            candidate = replace_declaration_same_height(source, current_decl, donor, donor_decl)
            if candidate is None:
                continue
            digest = sha256_bytes(candidate.encode("utf-8"))
            if digest in seen:
                continue
            seen.add(digest)
            candidates.append((label, candidate))

        for label, candidate in generic_candidates(source, current_decl):
            digest = sha256_bytes(candidate.encode("utf-8"))
            if digest not in seen:
                seen.add(digest)
                candidates.append((f"generic:{label}", candidate))

        tested: list[dict[str, object]] = []
        improved = False
        original = TARGET.read_bytes()
        for index, (label, candidate) in enumerate(candidates[:MAX_CANDIDATES], 1):
            if any(forbidden_hits(candidate).values()) or imports(candidate) != expected_imports:
                continue
            TARGET.write_text(candidate, encoding="utf-8")
            candidate_metric = compile_fa(
                f"frontier-{frontier:02d}-candidate-{index:02d}", max_errors=120
            )
            tested.append({"label": label, "metric": asdict(candidate_metric)})
            if strict_better(candidate_metric, metric):
                metric = candidate_metric
                source = candidate
                improved = True
                (OUT / f"frontier-{frontier:02d}-PROMOTED.txt").write_text(
                    f"label={label}\nsource_sha256={candidate_metric.source_sha256}\n"
                    f"first_error_line={candidate_metric.first_line}\nexit_code={candidate_metric.exit_code}\n",
                    encoding="utf-8",
                )
                break
            TARGET.write_bytes(original)

        if not improved:
            TARGET.write_bytes(original)
        history.append(
            {
                "frontier": frontier,
                "declaration": asdict(current_decl),
                "champion_before": asdict(compile_fa(f"frontier-{frontier:02d}-record", max_errors=120))
                if not improved
                else None,
                "champion_after": asdict(metric),
                "promoted": improved,
                "tested": tested,
            }
        )
        if not improved:
            break

    final_metric = compile_fa("final-fa-authoritative", max_errors=500)
    complete = False
    two_pass: dict[str, list[dict[str, object]]] = {}
    failure: str | None = None
    if final_metric.passed:
        try:
            two_pass = verify_all_twice()
            complete = True
        except Exception as exc:  # evidence must survive downstream failure
            failure = repr(exc)
    else:
        failure = (
            f"FA not yet complete; first error {final_metric.first_line}:{final_metric.first_col}: "
            f"{final_metric.first_message}"
        )

    status = {
        "complete": complete,
        "stage": "ALL_REQUIRED_TARGETS_2X_PASS" if complete else "Mock2_FunctionalAnalysis",
        "immutable_baseline_sha256": EXPECTED_INITIAL_SHA256,
        "immutable_baseline_first_error": INITIAL_CHAMPION_LINE,
        "strict_rule": "promote only exit 0 or first_error_line strictly greater; error-count reduction alone is ignored",
        "prerequisites": prereq,
        "final_fa_metric": asdict(final_metric),
        "history": history,
        "two_pass": two_pass,
        "failure": failure,
        "forbidden_token_audit": forbidden_hits(TARGET.read_text(encoding="utf-8")),
    }
    (OUT / "CURRENT.json").write_text(json.dumps(status, indent=2), encoding="utf-8")
    (OUT / "CURRENT.txt").write_text(
        f"complete={complete}\n"
        f"stage={status['stage']}\n"
        f"fa_exit={final_metric.exit_code}\n"
        f"fa_errors={final_metric.errors}\n"
        f"fa_first={final_metric.first_line}:{final_metric.first_col}\n"
        f"fa_sha256={final_metric.source_sha256}\n"
        f"failure={failure}\n",
        encoding="utf-8",
    )
    print(json.dumps(status, indent=2))
    return 0 if complete else 2


if __name__ == "__main__":
    raise SystemExit(main())
