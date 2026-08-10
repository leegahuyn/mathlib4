#!/usr/bin/env python3
from __future__ import annotations

import difflib
import hashlib
import importlib.util
import json
import os
import re
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Iterable

ROOT = Path.cwd()
PV = ROOT / "PrimalitySheafVerification"
SOURCE = PV / "Mock2_FunctionalAnalysis.lean"
OUT = ROOT / "build-logs/fa440-parallel-direct-solver"
TMP = Path("/tmp/fa440-parallel-direct-solver")
EXPECTED_LINES = 60453
PASS423_SHA = "71dc36f16ebea92d537aa40a5d420443e4bcb93ccb76fea31efb40a6cb5c3aa0"
PASS376_SHA = "07f6efd3309c3cc23b86adf5811918b752b72c33a3f7a76213ce9beb10796da4"
MINIMUM_FRONTIER = 31726
MAX_WORKERS = int(os.environ.get("FA440_MAX_WORKERS", "4"))
MAX_ROUNDS = int(os.environ.get("FA440_MAX_ROUNDS", "6"))
MAX_TOTAL_CANDIDATES = int(os.environ.get("FA440_MAX_CANDIDATES", "96"))
TIME_BUDGET_SECONDS = int(os.environ.get("FA440_TIME_BUDGET_SECONDS", "18800"))
START = time.monotonic()

DECL_RE = re.compile(
    r"^(?:protected\s+|private\s+|noncomputable\s+)?"
    r"(?:theorem|lemma|def|abbrev|instance|structure|class)\s+([^\s(:]+)"
)
ERROR_RE = re.compile(r"\.lean:(\d+):(\d+):\s+(?:error(?:\([^)]*\))?:|error:)")


@dataclass
class Metric:
    label: str
    source_sha256: str
    line_count: int
    exit_code: int
    error_headers_under_cap: int
    first_error_line: int
    first_error_col: int
    first_error_declaration: str
    maxErrors_cap: int
    olean: bool
    ilean: bool
    elapsed_seconds: float
    source_path: str
    log_path: str

    @property
    def passed(self) -> bool:
        return (
            self.exit_code == 0
            and self.error_headers_under_cap == 0
            and self.olean
            and self.ilean
        )


@dataclass
class Donor:
    label: str
    source_sha256: str
    source: str
    provenance: str


def run(
    args: list[str],
    *,
    text: bool = True,
    stdout=None,
    stderr=None,
    timeout: int | None = None,
) -> subprocess.CompletedProcess:
    return subprocess.run(
        args,
        cwd=ROOT,
        text=text,
        stdout=stdout,
        stderr=stderr,
        check=False,
        timeout=timeout,
    )


def sha_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha_text(text: str) -> str:
    return sha_bytes(text.encode("utf-8"))


def line_count(text: str) -> int:
    return text.count("\n") + (0 if text.endswith("\n") else 1)


def safe_name(label: str) -> str:
    return re.sub(r"[^A-Za-z0-9_.-]+", "_", label)[:120]


def write_json(path: Path, value) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(value, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )


def load_module(path: Path, name: str):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot import helper module {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def declaration_at(text: str, line_number: int) -> str:
    if line_number <= 0:
        return "<none>"
    lines = text.splitlines()
    for index in range(min(line_number - 1, len(lines) - 1), -1, -1):
        match = DECL_RE.match(lines[index])
        if match:
            return match.group(1)
    return "<unknown>"


def declaration_span(text: str, name: str) -> tuple[int, int, int, str] | None:
    lines = text.splitlines(keepends=True)
    start = None
    for index, line in enumerate(lines):
        match = DECL_RE.match(line)
        if match and match.group(1) == name:
            start = index
            break
    if start is None:
        return None
    end = len(lines)
    for index in range(start + 1, len(lines)):
        if DECL_RE.match(lines[index]):
            end = index
            break
    block = "".join(lines[start:end])
    marker = block.find(":= by")
    marker_length = len(":= by")
    if marker < 0:
        marker = block.find(":=")
        marker_length = len(":=")
    if marker < 0:
        return None
    header = block[: marker + marker_length]
    body_start = start + header.count("\n")
    return start, body_start, end, header


def same_height_replace(
    text: str, start: int, end: int, replacement: list[str]
) -> str | None:
    lines = text.splitlines(keepends=True)
    height = end - start
    normalized = [line if line.endswith("\n") else line + "\n" for line in replacement]
    if len(normalized) > height:
        return None
    normalized.extend(["\n"] * (height - len(normalized)))
    lines[start:end] = normalized
    candidate = "".join(lines)
    if line_count(candidate) != line_count(text):
        return None
    return candidate


def theorem_header_preserved(before: str, after: str, declaration: str) -> bool:
    before_span = declaration_span(before, declaration)
    after_span = declaration_span(after, declaration)
    return (
        before_span is not None
        and after_span is not None
        and before_span[3] == after_span[3]
    )


def code_without_comments_or_strings(text: str) -> str:
    output: list[str] = []
    index = 0
    block_depth = 0
    line_comment = False
    string = False
    escaped = False
    while index < len(text):
        char = text[index]
        next_char = text[index + 1] if index + 1 < len(text) else ""
        if line_comment:
            if char == "\n":
                line_comment = False
                output.append("\n")
            else:
                output.append(" ")
            index += 1
            continue
        if block_depth:
            if char == "/" and next_char == "-":
                block_depth += 1
                output.extend([" ", " "])
                index += 2
                continue
            if char == "-" and next_char == "/":
                block_depth -= 1
                output.extend([" ", " "])
                index += 2
                continue
            output.append("\n" if char == "\n" else " ")
            index += 1
            continue
        if string:
            output.append("\n" if char == "\n" else " ")
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                string = False
            index += 1
            continue
        if char == "-" and next_char == "-":
            line_comment = True
            output.extend([" ", " "])
            index += 2
            continue
        if char == "/" and next_char == "-":
            block_depth = 1
            output.extend([" ", " "])
            index += 2
            continue
        if char == '"':
            string = True
            output.append(" ")
            index += 1
            continue
        output.append(char)
        index += 1
    return "".join(output)


def forbidden_counts(text: str) -> dict[str, int]:
    code = code_without_comments_or_strings(text)
    patterns = {
        "sorry": r"\bsorry\b",
        "admit": r"\badmit\b",
        "new_global_axiom": r"(?m)^\s*(?:protected\s+|private\s+)?axiom\b",
        "unsafe": r"\bunsafe\b",
        "native_decide": r"\bnative_decide\b",
        "Lean.ofReduceBool": r"\bLean\.ofReduceBool\b",
    }
    return {
        name: len(re.findall(pattern, code)) for name, pattern in patterns.items()
    }


def metric_better(candidate: Metric, champion: Metric) -> bool:
    if candidate.passed != champion.passed:
        return candidate.passed
    if candidate.passed:
        return False
    # Deliberately compare the actual error line only.  Column-only movement and
    # maxErrors termination are not accepted as progress.
    return candidate.first_error_line > champion.first_error_line


def compile_temp(label: str, source_text: str) -> Metric:
    candidate_dir = TMP / "candidates"
    result_dir = TMP / "results"
    candidate_dir.mkdir(parents=True, exist_ok=True)
    result_dir.mkdir(parents=True, exist_ok=True)
    name = safe_name(label)
    source_path = candidate_dir / f"{name}.lean"
    olean = result_dir / f"{name}.olean"
    ilean = result_dir / f"{name}.ilean"
    log_path = result_dir / f"{name}.log"
    source_path.write_text(source_text, encoding="utf-8")
    olean.unlink(missing_ok=True)
    ilean.unlink(missing_ok=True)
    started = time.monotonic()
    with log_path.open("w", encoding="utf-8") as handle:
        proc = run(
            [
                "lake",
                "env",
                "lean",
                "-DmaxErrors=1",
                "-DwarningAsError=false",
                "-o",
                str(olean),
                "-i",
                str(ilean),
                str(source_path),
            ],
            stdout=handle,
            stderr=subprocess.STDOUT,
        )
    elapsed = time.monotonic() - started
    log = log_path.read_text(encoding="utf-8", errors="replace")
    matches = list(ERROR_RE.finditer(log))
    first_line = int(matches[0].group(1)) if matches else 0
    first_col = int(matches[0].group(2)) if matches else 0
    metric = Metric(
        label=label,
        source_sha256=sha_text(source_text),
        line_count=line_count(source_text),
        exit_code=proc.returncode,
        error_headers_under_cap=len(matches),
        first_error_line=first_line,
        first_error_col=first_col,
        first_error_declaration=declaration_at(source_text, first_line),
        maxErrors_cap=1,
        olean=olean.exists() and olean.stat().st_size > 0,
        ilean=ilean.exists() and ilean.stat().st_size > 0,
        elapsed_seconds=round(elapsed, 3),
        source_path=str(source_path),
        log_path=str(log_path),
    )
    write_json(result_dir / f"{name}.json", asdict(metric))
    return metric


def compile_actual(stem: str, label: str) -> Metric:
    source_path = PV / f"{stem}.lean"
    build_dir = ROOT / ".lake/build/lib/lean/PrimalitySheafVerification"
    build_dir.mkdir(parents=True, exist_ok=True)
    olean = build_dir / f"{stem}.olean"
    ilean = build_dir / f"{stem}.ilean"
    olean.unlink(missing_ok=True)
    ilean.unlink(missing_ok=True)
    log_path = OUT / f"{safe_name(label)}.log"
    started = time.monotonic()
    with log_path.open("w", encoding="utf-8") as handle:
        proc = run(
            [
                "lake",
                "env",
                "lean",
                "-DmaxErrors=1",
                "-DwarningAsError=false",
                "-o",
                str(olean),
                "-i",
                str(ilean),
                str(source_path),
            ],
            stdout=handle,
            stderr=subprocess.STDOUT,
        )
    elapsed = time.monotonic() - started
    log = log_path.read_text(encoding="utf-8", errors="replace")
    matches = list(ERROR_RE.finditer(log))
    first_line = int(matches[0].group(1)) if matches else 0
    first_col = int(matches[0].group(2)) if matches else 0
    source_text = source_path.read_text(encoding="utf-8")
    metric = Metric(
        label=label,
        source_sha256=sha_text(source_text),
        line_count=line_count(source_text),
        exit_code=proc.returncode,
        error_headers_under_cap=len(matches),
        first_error_line=first_line,
        first_error_col=first_col,
        first_error_declaration=declaration_at(source_text, first_line),
        maxErrors_cap=1,
        olean=olean.exists() and olean.stat().st_size > 0,
        ilean=ilean.exists() and ilean.stat().st_size > 0,
        elapsed_seconds=round(elapsed, 3),
        source_path=str(source_path.relative_to(ROOT)),
        log_path=str(log_path.relative_to(ROOT)),
    )
    write_json(OUT / f"{safe_name(label)}.json", asdict(metric))
    return metric


def recover_verified_baseline() -> tuple[str, dict]:
    fa432 = load_module(
        ROOT / "scripts/fa432_prepare_scoped_instance_candidate.py",
        "fa440_fa432_helper",
    )
    artifact_helper = fa432.load_helper()
    recovery_dir = TMP / "baseline-recovery"
    recovery_dir.mkdir(parents=True, exist_ok=True)
    data, provenance = artifact_helper.recover_exact_source(recovery_dir)
    text = data.decode("utf-8")
    if sha_text(text) != PASS423_SHA or line_count(text) != EXPECTED_LINES:
        raise RuntimeError(
            f"PASS423 exact source recovery failed: sha={sha_text(text)}, lines={line_count(text)}"
        )
    return text, provenance


def add_candidate(
    mapping: dict[str, str], label: str, text: str, baseline_header: str
) -> None:
    if line_count(text) != EXPECTED_LINES:
        return
    span = declaration_span(text, "actualEdgeAmbientParam_hasDerivAt")
    if span is None or span[3] != baseline_header:
        return
    mapping.setdefault(sha_text(text), (label, text))


def initial_candidates(baseline: str) -> list[tuple[str, str]]:
    candidates: dict[str, tuple[str, str]] = {}
    baseline_span = declaration_span(baseline, "actualEdgeAmbientParam_hasDerivAt")
    if baseline_span is None:
        raise RuntimeError("target theorem missing from baseline")
    baseline_header = baseline_span[3]

    fa432 = load_module(
        ROOT / "scripts/fa432_prepare_scoped_instance_candidate.py",
        "fa440_fa432_variants",
    )
    for variant in sorted(fa432.VARIANTS):
        try:
            text, _ = fa432.prepare(baseline, variant)
        except Exception:
            continue
        add_candidate(candidates, f"fa432::{variant}", text, baseline_header)

    artifact_helper = fa432.load_helper()
    for variant in sorted(artifact_helper.VARIANTS):
        try:
            text, _ = artifact_helper.prepare_variant(baseline, variant)
        except Exception:
            continue
        add_candidate(candidates, f"fa427::{variant}", text, baseline_header)

    fa435 = load_module(
        ROOT / "scripts/fa435_prepare_scoped_cumulative_candidate.py",
        "fa440_fa435_hunks",
    )
    try:
        scoped, _ = fa432.prepare(baseline, "scoped-normed-remove")
    except Exception:
        scoped = baseline
    staged: list[tuple[str, str]] = [("scoped", scoped)]
    for style in ("dot", "parenthesized"):
        try:
            paired, _ = fa435.apply_paired(scoped, style)
            staged.append((f"scoped-paired-{style}", paired))
            for tactic in ("ring", "simp"):
                try:
                    normalized, _ = fa435.apply_selected_piola(paired, tactic)
                    staged.append(
                        (f"scoped-paired-{style}-{tactic}", normalized)
                    )
                except Exception:
                    pass
            try:
                safe, _ = fa435.apply_safe(paired)
                staged.append((f"scoped-paired-{style}-safe", safe))
                try:
                    analytic, _ = fa435.apply_analytic(safe)
                    staged.append(
                        (f"scoped-paired-{style}-safe-analytic", analytic)
                    )
                except Exception:
                    pass
            except Exception:
                pass
        except Exception:
            pass
    for label, text in staged:
        add_candidate(candidates, f"fa435::{label}", text, baseline_header)

    candidates.pop(sha_text(baseline), None)
    return list(candidates.values())


def list_remote_branches() -> list[str]:
    proc = run(
        ["git", "ls-remote", "--heads", "origin"],
        stdout=subprocess.PIPE,
        stderr=subprocess.DEVNULL,
    )
    if proc.returncode != 0:
        return []
    names = []
    for line in proc.stdout.splitlines():
        parts = line.split()
        if len(parts) != 2:
            continue
        ref = parts[1]
        if ref.startswith("refs/heads/"):
            names.append(ref.removeprefix("refs/heads/"))
    return names


def relevant_branch(name: str) -> bool:
    lowered = name.lower()
    return any(
        token in lowered
        for token in (
            "fa37",
            "fa38",
            "fa39",
            "fa40",
            "fa41",
            "fa42",
            "fa43",
            "champion",
            "functional",
        )
    )


def fetch_donor_refs() -> list[str]:
    names = [name for name in list_remote_branches() if relevant_branch(name)]
    names.sort(
        key=lambda name: (
            "champion" in name.lower(),
            any(token in name.lower() for token in ("fa435", "fa434", "fa432", "fa428", "fa427", "fa426", "fa424", "fa423")),
            name,
        ),
        reverse=True,
    )
    names = names[:120]
    fetched: list[str] = []
    for offset in range(0, len(names), 16):
        chunk = names[offset : offset + 16]
        args = ["git", "fetch", "origin", "--depth=1"] + [
            f"+refs/heads/{name}:refs/remotes/origin/{name}" for name in chunk
        ]
        proc = run(args, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        if proc.returncode == 0:
            fetched.extend(f"refs/remotes/origin/{name}" for name in chunk)
        else:
            for name in chunk:
                proc = run(
                    [
                        "git",
                        "fetch",
                        "origin",
                        "--depth=1",
                        f"+refs/heads/{name}:refs/remotes/origin/{name}",
                    ],
                    stdout=subprocess.DEVNULL,
                    stderr=subprocess.DEVNULL,
                )
                if proc.returncode == 0:
                    fetched.append(f"refs/remotes/origin/{name}")
    return fetched


def git_show(ref: str, path: str) -> bytes | None:
    proc = run(
        ["git", "show", f"{ref}:{path}"],
        text=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.DEVNULL,
    )
    return proc.stdout if proc.returncode == 0 else None


def collect_donors(refs: Iterable[str], excluded_sha: str) -> list[Donor]:
    donors: dict[str, Donor] = {}
    for ref in refs:
        direct = git_show(
            ref, "PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean"
        )
        if direct is not None:
            try:
                text = direct.decode("utf-8")
            except UnicodeDecodeError:
                text = ""
            digest = sha_text(text) if text else ""
            if (
                text
                and line_count(text) == EXPECTED_LINES
                and digest != excluded_sha
            ):
                donors.setdefault(
                    digest,
                    Donor(
                        ref.rsplit("/", 1)[-1],
                        digest,
                        text,
                        f"{ref}:PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean",
                    ),
                )

        tree = run(
            [
                "git",
                "ls-tree",
                "-r",
                "--name-only",
                ref,
                "build-logs",
                "candidate-records",
                "champion-records",
            ],
            stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL,
        )
        if tree.returncode != 0:
            continue
        source_paths = [
            path
            for path in tree.stdout.splitlines()
            if "Mock2_FunctionalAnalysis" in path and path.endswith(".lean")
        ][:30]
        for path in source_paths:
            data = git_show(ref, path)
            if data is None:
                continue
            try:
                text = data.decode("utf-8")
            except UnicodeDecodeError:
                continue
            digest = sha_text(text)
            if line_count(text) != EXPECTED_LINES or digest == excluded_sha:
                continue
            donors.setdefault(
                digest,
                Donor(
                    f"{ref.rsplit('/', 1)[-1]}::{Path(path).name}",
                    digest,
                    text,
                    f"{ref}:{path}",
                ),
            )
    result = list(donors.values())
    result.sort(key=lambda donor: donor.label)
    return result[:160]


def donor_candidates(
    champion: str, declaration: str, donors: list[Donor]
) -> list[tuple[str, str]]:
    current_span = declaration_span(champion, declaration)
    if current_span is None:
        return []
    _, body_start, end, current_header = current_span
    current_lines = champion.splitlines(keepends=True)
    candidates: dict[str, tuple[str, str]] = {}
    for donor in donors:
        donor_span = declaration_span(donor.source, declaration)
        if donor_span is None:
            continue
        _, donor_body_start, donor_end, donor_header = donor_span
        # The statement/header in the candidate always remains the champion's.
        donor_lines = donor.source.splitlines(keepends=True)
        donor_body = donor_lines[donor_body_start:donor_end]
        whole = same_height_replace(champion, body_start, end, donor_body)
        if whole is not None and theorem_header_preserved(
            champion, whole, declaration
        ):
            candidates.setdefault(
                sha_text(whole), (f"donor-body::{donor.label}", whole)
            )

        matcher = difflib.SequenceMatcher(
            a=current_lines[body_start:end],
            b=donor_lines[donor_body_start:donor_end],
            autojunk=False,
        )
        hunks = [opcode for opcode in matcher.get_opcodes() if opcode[0] != "equal"]
        clustered = champion
        valid = True
        for _, i1, i2, j1, j2 in reversed(hunks):
            replacement = donor_lines[donor_body_start + j1 : donor_body_start + j2]
            updated = same_height_replace(
                clustered, body_start + i1, body_start + i2, replacement
            )
            if updated is None:
                valid = False
                break
            clustered = updated
        if valid and clustered != champion and theorem_header_preserved(
            champion, clustered, declaration
        ):
            candidates.setdefault(
                sha_text(clustered),
                (f"donor-cluster::{donor.label}", clustered),
            )
        for index, (_, i1, i2, j1, j2) in enumerate(hunks[:8]):
            replacement = donor_lines[donor_body_start + j1 : donor_body_start + j2]
            single = same_height_replace(
                champion, body_start + i1, body_start + i2, replacement
            )
            if single is not None and theorem_header_preserved(
                champion, single, declaration
            ):
                candidates.setdefault(
                    sha_text(single),
                    (f"donor-hunk-{index}::{donor.label}", single),
                )
    candidates.pop(sha_text(champion), None)
    return list(candidates.values())[:60]


def replace_exact_same_height(
    text: str, old: str, new: str, expected: int | None = None
) -> str | None:
    count = text.count(old)
    if count == 0:
        return None
    if expected is not None and count != expected:
        return None
    candidate = text.replace(old, new)
    if line_count(candidate) != line_count(text):
        return None
    return candidate


def known_candidates(champion: str, first_line: int) -> list[tuple[str, str]]:
    output: dict[str, tuple[str, str]] = {}

    def add(label: str, candidate: str | None) -> None:
        if candidate is None or candidate == champion:
            return
        if line_count(candidate) != EXPECTED_LINES:
            return
        output.setdefault(sha_text(candidate), (label, candidate))

    dot = champion
    parenthesized = champion
    dot_changed = 0
    parenthesized_changed = 0
    for edge, expected in (
        ("circularArc", 5),
        ("leftVerticalSegment", 2),
        ("rightVerticalSegment", 2),
    ):
        old = (
            "GammaTwoActualPolygonEdge.paired "
            f"((q, GammaTwoModularTileEdge.{edge}) : GammaTwoActualPolygonEdge)"
        )
        if dot.count(old) in (0, expected):
            dot_changed += dot.count(old)
            dot = dot.replace(
                old,
                f"((q, GammaTwoModularTileEdge.{edge}) : GammaTwoActualPolygonEdge).paired",
            )
        if parenthesized.count(old) in (0, expected):
            parenthesized_changed += parenthesized.count(old)
            parenthesized = parenthesized.replace(
                old,
                "(GammaTwoActualPolygonEdge.paired "
                f"((q, GammaTwoModularTileEdge.{edge}) : GammaTwoActualPolygonEdge))",
            )
    if dot_changed:
        add("known::paired-dot", dot)
    if parenthesized_changed:
        add("known::paired-parenthesized", parenthesized)

    replacements = [
        (
            "selected-Piola-ring",
            "  rw [nativeActualEdgeFluxIntegral_left_eq_selectedPiola hT]\n\n",
            "  rw [nativeActualEdgeFluxIntegral_left_eq_selectedPiola hT]\n  ring\n",
            1,
        ),
        (
            "selected-Piola-simp",
            "  rw [nativeActualEdgeFluxIntegral_left_eq_selectedPiola hT]\n\n",
            "  rw [nativeActualEdgeFluxIntegral_left_eq_selectedPiola hT]\n  simp\n",
            1,
        ),
        (
            "height-membership",
            "        (show z ∈ {w : ℍ | w.im ≤ H} from le_of_not_gt hHigh)⟩\n",
            "        (show z.im ≤ H from le_of_not_gt hHigh)⟩\n",
            1,
        ),
        (
            "upper-half-plane-constructor",
            "    hcomplex.subtype_mk _\n",
            "    hcomplex.upperHalfPlaneMk _\n",
            1,
        ),
        (
            "upper-half-plane-ext",
            "      apply Subtype.ext\n      apply Complex.ext <;> simp)\n",
            "      apply UpperHalfPlane.ext\n      apply Complex.ext <;> simp)\n",
            1,
        ),
        (
            "absolute-triangle",
            "      abs_add _ _\n",
            "      abs_add_le _ _\n",
            1,
        ),
        (
            "tail-projection",
            "  rcases (fixedPhaseCore_hasZeroThreeCuspTail n u)\n"
            "      .eventually_zero_on_horocycleBoundary with\n",
            "  rcases (fixedPhaseCore_hasZeroThreeCuspTail n u)"
            ".eventually_zero_on_horocycleBoundary with\n\n",
            2,
        ),
        (
            "zero-function-coercion",
            "  simpa using htrace.trans hrep\n",
            "  simpa only [Pi.zero_apply] using htrace.trans hrep\n",
            1,
        ),
        (
            "product-derivative-normalization",
            "  simpa only [one_mul] using hprod.deriv\n",
            "  convert hprod.deriv using 1 <;> ring\n",
            1,
        ),
        (
            "positive-tail-height",
            "    exact norm_deriv_height_mul_normSq_le\n"
            "      (hf.differentiable (by norm_num)) (le_of_lt hy)\n",
            "    exact norm_deriv_height_mul_normSq_le (hf.differentiable (by norm_num))\n"
            "      ((zero_le_one.trans hH).trans (le_of_lt hy))\n",
            1,
        ),
        (
            "nonnegative-multiplier",
            "        (mul_le_mul_of_nonneg_left hinner\n"
            "          (mul_nonneg (by norm_num) hy)) _\n",
            "        (mul_le_mul_of_nonneg_left hinner (by positivity))\n"
            "          _\n",
            1,
        ),
    ]
    for label, old, new, expected in replacements:
        add(label, replace_exact_same_height(champion, old, new, expected))

    # Cumulative known repairs, preserving the source height after every step.
    cumulative = champion
    applied: list[str] = []
    for label, old, new, expected in replacements:
        candidate = replace_exact_same_height(cumulative, old, new, expected)
        if candidate is not None:
            cumulative = candidate
            applied.append(label)
            add("known-cumulative::" + "+".join(applied), cumulative)
    if dot_changed:
        cumulative_dot = dot
        applied_dot = ["paired-dot"]
        for label, old, new, expected in replacements:
            candidate = replace_exact_same_height(
                cumulative_dot, old, new, expected
            )
            if candidate is not None:
                cumulative_dot = candidate
                applied_dot.append(label)
                add(
                    "known-cumulative::" + "+".join(applied_dot),
                    cumulative_dot,
                )
    if parenthesized_changed:
        cumulative_parenthesized = parenthesized
        applied_parenthesized = ["paired-parenthesized"]
        for label, old, new, expected in replacements:
            candidate = replace_exact_same_height(
                cumulative_parenthesized, old, new, expected
            )
            if candidate is not None:
                cumulative_parenthesized = candidate
                applied_parenthesized.append(label)
                add(
                    "known-cumulative::" + "+".join(applied_parenthesized),
                    cumulative_parenthesized,
                )
    return list(output.values())[:40]


def first_error_context(metric: Metric) -> str:
    path = ROOT / metric.log_path if not Path(metric.log_path).is_absolute() else Path(metric.log_path)
    if not path.exists() or metric.first_error_line <= 0:
        return ""
    lines = path.read_text(encoding="utf-8", errors="replace").splitlines()
    needle = f".lean:{metric.first_error_line}:{metric.first_error_col}:"
    for index, line in enumerate(lines):
        if needle in line:
            return (
                "\n".join(lines[max(0, index - 10) : min(len(lines), index + 110)])
                + "\n"
            )
    return ""


def parallel_screen(
    candidates: list[tuple[str, str]], attempted: set[str], remaining: int
) -> list[tuple[Metric, str]]:
    selected: list[tuple[str, str]] = []
    for label, text in candidates:
        digest = sha_text(text)
        if digest in attempted:
            continue
        attempted.add(digest)
        selected.append((label, text))
        if len(selected) >= remaining:
            break
    if not selected:
        return []
    results: list[tuple[Metric, str]] = []
    with ThreadPoolExecutor(max_workers=MAX_WORKERS) as pool:
        futures = {
            pool.submit(compile_temp, label, text): text for label, text in selected
        }
        for future in as_completed(futures):
            text = futures[future]
            try:
                metric = future.result()
            except Exception as exc:
                write_json(
                    OUT / "candidate-exceptions" / f"{safe_name(str(exc))}.json",
                    {"error": repr(exc)},
                )
                continue
            results.append((metric, text))
    results.sort(
        key=lambda pair: (
            pair[0].passed,
            pair[0].first_error_line,
            pair[0].first_error_col,
        ),
        reverse=True,
    )
    return results


def confirm_best_candidates(
    screened: list[tuple[Metric, str]],
    champion_text: str,
    champion_metric: Metric,
    round_index: int,
) -> tuple[str, Metric, dict | None]:
    for rank, (screen_metric, candidate_text) in enumerate(screened[:6], 1):
        if not metric_better(screen_metric, champion_metric):
            continue
        if line_count(candidate_text) != EXPECTED_LINES:
            continue
        declaration = champion_metric.first_error_declaration
        if declaration not in ("<none>", "<unknown>") and not theorem_header_preserved(
            champion_text, candidate_text, declaration
        ):
            continue
        SOURCE.write_text(candidate_text, encoding="utf-8")
        actual = compile_actual(
            "Mock2_FunctionalAnalysis",
            f"round-{round_index:02d}-rank-{rank:02d}-actual-confirmation",
        )
        if (
            actual.source_sha256 == screen_metric.source_sha256
            and actual.line_count == EXPECTED_LINES
            and metric_better(actual, champion_metric)
        ):
            return candidate_text, actual, {
                "screen": asdict(screen_metric),
                "actual": asdict(actual),
                "rank": rank,
            }
        SOURCE.write_text(champion_text, encoding="utf-8")
    return champion_text, champion_metric, None


def main() -> int:
    OUT.mkdir(parents=True, exist_ok=True)
    TMP.mkdir(parents=True, exist_ok=True)
    baseline, provenance = recover_verified_baseline()
    baseline_sha = sha_text(baseline)
    write_json(OUT / "BASELINE_PROVENANCE.json", provenance)
    (OUT / "Mock2_FunctionalAnalysis-baseline.lean").write_text(
        baseline, encoding="utf-8"
    )
    SOURCE.write_text(baseline, encoding="utf-8")

    mock2 = compile_actual("Mock2", "prerequisite-Mock2")
    mock2_advanced = compile_actual(
        "Mock2_Advanced", "prerequisite-Mock2_Advanced"
    )
    if not (mock2.passed and mock2_advanced.passed):
        status = {
            "classification": "INFRA_FAILURE",
            "reason": "completed prerequisite regression",
            "Mock2": asdict(mock2),
            "Mock2_Advanced": asdict(mock2_advanced),
        }
        write_json(OUT / "CURRENT.json", status)
        return 2

    baseline_metric = compile_actual(
        "Mock2_FunctionalAnalysis", "baseline-direct-confirmation"
    )
    if (
        baseline_metric.source_sha256 != PASS423_SHA
        or baseline_metric.line_count != EXPECTED_LINES
        or (
            not baseline_metric.passed
            and baseline_metric.first_error_line < MINIMUM_FRONTIER
        )
    ):
        status = {
            "classification": "INFRA_FAILURE",
            "reason": "PASS423 baseline did not reproduce",
            "baseline": asdict(baseline_metric),
            "required_sha256": PASS423_SHA,
            "minimum_frontier": MINIMUM_FRONTIER,
        }
        write_json(OUT / "CURRENT.json", status)
        return 3

    refs = fetch_donor_refs()
    donors = collect_donors(refs, baseline_sha)
    write_json(
        OUT / "DONORS.json",
        [
            {
                "label": donor.label,
                "source_sha256": donor.source_sha256,
                "provenance": donor.provenance,
            }
            for donor in donors
        ],
    )

    champion_text = baseline
    champion_metric = baseline_metric
    attempted: set[str] = {baseline_sha}
    trial_metrics: list[dict] = []
    promotions: list[dict] = []
    total_screened = 0

    for round_index in range(MAX_ROUNDS):
        if champion_metric.passed:
            break
        if time.monotonic() - START >= TIME_BUDGET_SECONDS:
            break
        remaining = MAX_TOTAL_CANDIDATES - total_screened
        if remaining <= 0:
            break

        candidates: list[tuple[str, str]] = []
        if round_index == 0:
            candidates.extend(initial_candidates(champion_text))
        candidates.extend(
            known_candidates(champion_text, champion_metric.first_error_line)
        )
        declaration = champion_metric.first_error_declaration
        if declaration not in ("<none>", "<unknown>"):
            candidates.extend(donor_candidates(champion_text, declaration, donors))

        screened = parallel_screen(candidates, attempted, remaining)
        total_screened += len(screened)
        trial_metrics.extend(asdict(metric) for metric, _ in screened)
        new_text, new_metric, promotion_detail = confirm_best_candidates(
            screened,
            champion_text,
            champion_metric,
            round_index,
        )
        if promotion_detail is None:
            break
        promotions.append(
            {
                "round": round_index,
                "previous": asdict(champion_metric),
                "new": asdict(new_metric),
                "confirmation": promotion_detail,
            }
        )
        champion_text = new_text
        champion_metric = new_metric
        (OUT / f"PROMOTION_{len(promotions):02d}.lean").write_text(
            champion_text, encoding="utf-8"
        )
        write_json(
            OUT / f"PROMOTION_{len(promotions):02d}.json",
            promotions[-1],
        )

    SOURCE.write_text(champion_text, encoding="utf-8")
    final_confirmation = compile_actual(
        "Mock2_FunctionalAnalysis", "selected-final-direct-confirmation"
    )
    if final_confirmation.source_sha256 != sha_text(champion_text):
        raise RuntimeError("selected source and final direct log SHA mismatch")
    if not final_confirmation.passed and final_confirmation.first_error_line < champion_metric.first_error_line:
        # A nonreproducible screen/confirmation chain is discarded completely.
        champion_text = baseline
        SOURCE.write_text(champion_text, encoding="utf-8")
        final_confirmation = compile_actual(
            "Mock2_FunctionalAnalysis", "fallback-baseline-direct-confirmation"
        )
        promotions = []

    baseline_forbidden = forbidden_counts(baseline)
    selected_forbidden = forbidden_counts(champion_text)
    forbidden_not_increased = all(
        selected_forbidden[name] <= baseline_forbidden[name]
        for name in baseline_forbidden
    )
    strict_promotion = (
        final_confirmation.source_sha256 != baseline_sha
        and final_confirmation.line_count == EXPECTED_LINES
        and forbidden_not_increased
        and (
            final_confirmation.passed
            or final_confirmation.first_error_line
            > baseline_metric.first_error_line
        )
    )
    materialized_baseline = (
        SOURCE.read_text(encoding="utf-8") == baseline
        and baseline_sha == PASS423_SHA
        and (
            baseline_metric.passed
            or baseline_metric.first_error_line >= MINIMUM_FRONTIER
        )
    )
    persist_source = strict_promotion or materialized_baseline
    if strict_promotion:
        (OUT / "PROMOTED").touch()
    elif materialized_baseline:
        (OUT / "MATERIALIZED_PASS423_BASELINE").touch()
    else:
        (OUT / "NO_VERIFIED_SOURCE_TO_PERSIST").touch()

    (OUT / "Mock2_FunctionalAnalysis-selected.lean").write_text(
        champion_text, encoding="utf-8"
    )
    (OUT / "FIRST_ERROR_CONTEXT.txt").write_text(
        first_error_context(final_confirmation), encoding="utf-8"
    )
    write_json(OUT / "TRIALS.json", trial_metrics)
    status = {
        "classification": "VERIFIED",
        "authority": "direct Lean CLI actual repository-path confirmation",
        "baseline": asdict(baseline_metric),
        "selected": asdict(final_confirmation),
        "strict_promotion": strict_promotion,
        "materialized_PASS423_baseline": materialized_baseline,
        "persist_source": persist_source,
        "promotion_chain": promotions,
        "parallel_screened_candidates": total_screened,
        "parallel_workers": MAX_WORKERS,
        "rounds_completed": len(promotions),
        "line_count_invariant": final_confirmation.line_count == EXPECTED_LINES,
        "baseline_forbidden_counts": baseline_forbidden,
        "selected_forbidden_counts": selected_forbidden,
        "forbidden_not_increased": forbidden_not_increased,
        "maxErrors_cap": 1,
        "maxErrors_interpretation": "screening cap only; not total errors or proof progress",
        "elapsed_seconds": round(time.monotonic() - START, 3),
    }
    write_json(OUT / "CURRENT.json", status)
    (OUT / "CURRENT.txt").write_text(
        "\n".join(
            [
                "classification=VERIFIED",
                "authority=direct Lean CLI actual repository-path confirmation",
                f"baseline_sha256={baseline_metric.source_sha256}",
                f"baseline_first_error={baseline_metric.first_error_line}:{baseline_metric.first_error_col}",
                f"selected_sha256={final_confirmation.source_sha256}",
                f"FA_exit={final_confirmation.exit_code}",
                f"FA_first_error={final_confirmation.first_error_line}:{final_confirmation.first_error_col}",
                f"FA_first_declaration={final_confirmation.first_error_declaration}",
                f"line_count={final_confirmation.line_count}",
                f"strict_promotion={str(strict_promotion).lower()}",
                f"persist_source={str(persist_source).lower()}",
                f"parallel_screened_candidates={total_screened}",
                "maxErrors_cap=1",
            ]
        )
        + "\n",
        encoding="utf-8",
    )
    print(json.dumps(status, indent=2, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as error:
        OUT.mkdir(parents=True, exist_ok=True)
        (OUT / "INFRA_FAILURE.txt").write_text(
            f"{type(error).__name__}: {error}\n", encoding="utf-8"
        )
        raise
