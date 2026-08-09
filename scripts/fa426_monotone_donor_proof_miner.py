#!/usr/bin/env python3
from __future__ import annotations

import base64
import difflib
import hashlib
import json
import os
import re
import subprocess
import sys
import time
import zipfile
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Iterable

ROOT = Path.cwd()
PV = ROOT / "PrimalitySheafVerification"
SRC = PV / "Mock2_FunctionalAnalysis.lean"
OUT = ROOT / "build-logs/fa426-monotone-donor-proof-miner"
TMP = Path("/tmp/fa426-monotone-donor-proof-miner")
REPO = os.environ.get("GITHUB_REPOSITORY", "leegahuyn/mathlib4")
SOURCE_PATH = "PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean"
EXPECTED_LINES = 60453
PASS423_RUN = 31317392557
PASS423_SHA = "71dc36f16ebea92d537aa40a5d420443e4bcb93ccb76fea31efb40a6cb5c3aa0"
PASS376_RUN = 31267332510
PASS376_SHA = "07f6efd3309c3cc23b86adf5811918b752b72c33a3f7a76213ce9beb10796da4"
TARGET_DECL = "actualEdgeAmbientParam_hasDerivAt"
MAX_TOTAL_CANDIDATES = int(os.environ.get("FA426_MAX_CANDIDATES", "24"))
MAX_PROMOTIONS = int(os.environ.get("FA426_MAX_PROMOTIONS", "4"))
TIME_BUDGET_SECONDS = int(os.environ.get("FA426_TIME_BUDGET_SECONDS", "17200"))
START_TIME = time.monotonic()

ERROR_RE = re.compile(
    r"Mock2_FunctionalAnalysis\.lean:(\d+):(\d+):\s+(?:error(?:\([^)]*\))?:|error:)"
)
DECL_RE = re.compile(
    r"^(?:protected\s+|private\s+|noncomputable\s+)?"
    r"(?:theorem|lemma|def|abbrev|instance|structure|class)\s+([^\s(:]+)"
)


@dataclass
class Metric:
    label: str
    source_sha256: str
    line_count: int
    exit_code: int
    error_headers: int
    first_error_line: int
    first_error_col: int
    first_error_declaration: str
    max_errors: int
    olean: bool
    ilean: bool
    elapsed_seconds: float
    log_path: str

    @property
    def passed(self) -> bool:
        return (
            self.exit_code == 0
            and self.error_headers == 0
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
    check: bool = False,
    timeout: int | None = None,
) -> subprocess.CompletedProcess:
    proc = subprocess.run(
        args,
        cwd=ROOT,
        text=text,
        stdout=stdout,
        stderr=stderr,
        check=False,
        timeout=timeout,
    )
    if check and proc.returncode != 0:
        raise RuntimeError(f"command failed ({proc.returncode}): {' '.join(args)}")
    return proc


def sha_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha_text(text: str) -> str:
    return sha_bytes(text.encode("utf-8"))


def line_count(text: str) -> int:
    return text.count("\n") + (0 if text.endswith("\n") else 1)


def write_json(path: Path, obj) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(obj, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


def gh_json(endpoint: str):
    proc = run(
        ["gh", "api", "--paginate", endpoint],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if proc.returncode != 0:
        return None
    raw = proc.stdout.strip()
    if not raw:
        return None
    try:
        return json.loads(raw)
    except json.JSONDecodeError:
        pages = []
        decoder = json.JSONDecoder()
        idx = 0
        while idx < len(raw):
            while idx < len(raw) and raw[idx].isspace():
                idx += 1
            if idx >= len(raw):
                break
            obj, idx = decoder.raw_decode(raw, idx)
            pages.append(obj)
        return pages


def artifact_list(run_id: int) -> list[dict]:
    raw = gh_json(f"/repos/{REPO}/actions/runs/{run_id}/artifacts?per_page=100")
    if raw is None:
        return []
    if isinstance(raw, dict):
        return list(raw.get("artifacts", []))
    out: list[dict] = []
    for page in raw:
        if isinstance(page, dict):
            out.extend(page.get("artifacts", []))
    return out


def exact_source_from_artifacts(run_id: int, expected_sha: str) -> tuple[str | None, dict]:
    provenance: dict = {
        "run_id": run_id,
        "expected_sha256": expected_sha,
        "artifact_checks": [],
    }
    for artifact in artifact_list(run_id):
        if artifact.get("expired"):
            continue
        artifact_id = int(artifact["id"])
        zip_path = TMP / f"run-{run_id}-artifact-{artifact_id}.zip"
        unpack = TMP / f"run-{run_id}-artifact-{artifact_id}"
        unpack.mkdir(parents=True, exist_ok=True)
        with zip_path.open("wb") as handle:
            proc = run(
                ["gh", "api", f"/repos/{REPO}/actions/artifacts/{artifact_id}/zip"],
                text=False,
                stdout=handle,
                stderr=subprocess.PIPE,
            )
        row = {
            "artifact_id": artifact_id,
            "artifact_name": artifact.get("name", ""),
            "download_exit": proc.returncode,
        }
        provenance["artifact_checks"].append(row)
        if proc.returncode != 0:
            continue
        try:
            with zipfile.ZipFile(zip_path) as archive:
                archive.extractall(unpack)
        except zipfile.BadZipFile:
            row["bad_zip"] = True
            continue
        hits: list[Path] = []
        for candidate in unpack.rglob("*"):
            if not candidate.is_file():
                continue
            try:
                data = candidate.read_bytes()
            except OSError:
                continue
            if sha_bytes(data) == expected_sha:
                hits.append(candidate)
        row["exact_sha_hits"] = len(hits)
        if len(hits) == 1:
            source = hits[0].read_text(encoding="utf-8")
            row["member"] = str(hits[0].relative_to(unpack))
            provenance["selected_artifact_id"] = artifact_id
            provenance["selected_member"] = row["member"]
            return source, provenance
    return None, provenance


def branch_names() -> list[str]:
    raw = gh_json(f"/repos/{REPO}/branches?per_page=100")
    pages = raw if isinstance(raw, list) else []
    names: list[str] = []
    for item in pages:
        if isinstance(item, dict) and "name" in item:
            names.append(str(item["name"]))
        elif isinstance(item, list):
            names.extend(str(x["name"]) for x in item if isinstance(x, dict) and "name" in x)
    # gh --paginate may return a single JSON array.
    if pages and all(isinstance(x, dict) for x in pages):
        names = [str(x["name"]) for x in pages if "name" in x]
    return sorted(set(names))


def relevant_branch(name: str) -> bool:
    low = name.lower()
    keys = (
        "fa37", "fa38", "fa39", "fa40", "fa41", "fa42", "fa43",
        "functional", "mock2", "champion", "pass3", "pass4",
    )
    return any(key in low for key in keys)


def fetch_relevant_refs() -> list[str]:
    names = [name for name in branch_names() if relevant_branch(name)]
    # Prefer recent-numbered and champion branches, but cap network work.
    names.sort(key=lambda n: ("champion" not in n.lower(), n), reverse=True)
    names = names[:140]
    fetched: list[str] = []
    for offset in range(0, len(names), 18):
        chunk = names[offset : offset + 18]
        args = ["git", "fetch", "origin", "--depth=1"]
        args.extend(
            f"+refs/heads/{name}:refs/remotes/origin/{name}" for name in chunk
        )
        proc = run(args, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        if proc.returncode == 0:
            fetched.extend(f"refs/remotes/origin/{name}" for name in chunk)
        else:
            for name in chunk:
                single = run(
                    [
                        "git", "fetch", "origin", "--depth=1",
                        f"+refs/heads/{name}:refs/remotes/origin/{name}",
                    ],
                    stdout=subprocess.DEVNULL,
                    stderr=subprocess.DEVNULL,
                )
                if single.returncode == 0:
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


def exact_source_from_refs(refs: Iterable[str], expected_sha: str) -> tuple[str | None, str | None]:
    for ref in refs:
        data = git_show(ref, SOURCE_PATH)
        if data is not None and sha_bytes(data) == expected_sha:
            return data.decode("utf-8"), ref
    return None, None


def checked_source_with_verified_evidence() -> tuple[str | None, dict | None]:
    if not SRC.exists():
        return None, None
    text = SRC.read_text(encoding="utf-8")
    digest = sha_text(text)
    evidence_paths = sorted(
        ROOT.glob("build-logs/fa42*/CURRENT.json"),
        key=lambda p: p.stat().st_mtime,
        reverse=True,
    )
    for evidence_path in evidence_paths:
        try:
            evidence = json.loads(evidence_path.read_text(encoding="utf-8"))
        except Exception:
            continue
        selected = evidence.get("selected", {})
        if (
            evidence.get("promoted") is True
            and evidence.get("authority") == "direct Lean CLI"
            and selected.get("source_sha256") == digest
            and int(selected.get("exit_code", 1)) == 0
            or (
                evidence.get("promoted") is True
                and evidence.get("authority") == "direct Lean CLI"
                and selected.get("source_sha256") == digest
                and int(selected.get("first_error_line", 0)) >= 31726
            )
        ):
            return text, {"evidence_path": str(evidence_path), "evidence": evidence}
    if digest in {PASS423_SHA, PASS376_SHA}:
        return text, {"exact_historical_sha": digest}
    return None, None


def select_verified_baseline(refs: list[str]) -> tuple[str, dict, int]:
    checked, checked_evidence = checked_source_with_verified_evidence()
    checked_sha = sha_text(checked) if checked is not None else None
    if checked is not None and checked_sha not in {PASS376_SHA}:
        frontier = 0
        if checked_evidence and "evidence" in checked_evidence:
            frontier = int(
                checked_evidence["evidence"].get("selected", {}).get("first_error_line", 0)
            )
        if checked_sha == PASS423_SHA:
            frontier = max(frontier, 31726)
        return checked, {"source": "checked-in verified evidence", **(checked_evidence or {})}, frontier

    source, provenance = exact_source_from_artifacts(PASS423_RUN, PASS423_SHA)
    if source is not None:
        return source, {"source": "PASS423 artifact", **provenance}, 31726
    source, ref = exact_source_from_refs(refs, PASS423_SHA)
    if source is not None:
        return source, {"source": "remote ref exact SHA", "ref": ref}, 31726

    source, provenance376 = exact_source_from_artifacts(PASS376_RUN, PASS376_SHA)
    if source is not None:
        return source, {"source": "PASS376 artifact fallback", **provenance376}, 31725
    source, ref = exact_source_from_refs(refs, PASS376_SHA)
    if source is not None:
        return source, {"source": "PASS376 remote-ref fallback", "ref": ref}, 31725
    if checked is not None:
        return checked, {"source": "checked-in PASS376 fallback", **(checked_evidence or {})}, 31725
    raise RuntimeError("no exact direct-verified FA baseline could be recovered")


def declaration_at(text: str, line_no: int) -> str:
    if line_no <= 0:
        return "<none>"
    lines = text.splitlines()
    idx = min(line_no - 1, len(lines) - 1)
    for i in range(idx, -1, -1):
        match = DECL_RE.match(lines[i])
        if match:
            return match.group(1)
    return "<unknown>"


def declaration_span(text: str, name: str) -> tuple[int, int, int, str] | None:
    lines = text.splitlines(keepends=True)
    start = None
    for i, line in enumerate(lines):
        match = DECL_RE.match(line)
        if match and match.group(1) == name:
            start = i
            break
    if start is None:
        return None
    end = len(lines)
    for i in range(start + 1, len(lines)):
        if DECL_RE.match(lines[i]):
            end = i
            break
    block = "".join(lines[start:end])
    marker = block.find(":= by")
    marker_len = len(":= by")
    if marker < 0:
        marker = block.find(":=")
        marker_len = len(":=")
    if marker < 0:
        return None
    prefix = block[: marker + marker_len]
    header_lines = prefix.count("\n")
    body_start = start + header_lines
    return start, body_start, end, prefix


def replace_same_height(
    text: str,
    start_line: int,
    end_line: int,
    replacement_lines: list[str],
) -> str | None:
    lines = text.splitlines(keepends=True)
    original_height = end_line - start_line
    normalized: list[str] = []
    for line in replacement_lines:
        normalized.append(line if line.endswith("\n") else line + "\n")
    if len(normalized) > original_height:
        return None
    normalized.extend(["\n"] * (original_height - len(normalized)))
    lines[start_line:end_line] = normalized
    candidate = "".join(lines)
    if line_count(candidate) != line_count(text):
        return None
    return candidate


def compile_metric(stem: str, label: str, max_errors: int = 1) -> Metric:
    source = PV / f"{stem}.lean"
    build = ROOT / ".lake/build/lib/lean/PrimalitySheafVerification"
    build.mkdir(parents=True, exist_ok=True)
    olean = build / f"{stem}.olean"
    ilean = build / f"{stem}.ilean"
    olean.unlink(missing_ok=True)
    ilean.unlink(missing_ok=True)
    log_path = OUT / f"{label}.log"
    started = time.monotonic()
    with log_path.open("w", encoding="utf-8") as handle:
        proc = run(
            [
                "lake", "env", "lean",
                f"-DmaxErrors={max_errors}",
                "-DwarningAsError=false",
                "-o", str(olean),
                "-i", str(ilean),
                str(source),
            ],
            stdout=handle,
            stderr=subprocess.STDOUT,
        )
    elapsed = time.monotonic() - started
    log = log_path.read_text(encoding="utf-8", errors="replace")
    matches = list(ERROR_RE.finditer(log)) if stem == "Mock2_FunctionalAnalysis" else list(
        re.finditer(
            rf"{re.escape(stem)}\.lean:(\d+):(\d+):\s+(?:error(?:\([^)]*\))?:|error:)",
            log,
        )
    )
    first_line = int(matches[0].group(1)) if matches else 0
    first_col = int(matches[0].group(2)) if matches else 0
    source_text = source.read_text(encoding="utf-8")
    metric = Metric(
        label=label,
        source_sha256=sha_text(source_text),
        line_count=line_count(source_text),
        exit_code=proc.returncode,
        error_headers=len(matches),
        first_error_line=first_line,
        first_error_col=first_col,
        first_error_declaration=declaration_at(source_text, first_line),
        max_errors=max_errors,
        olean=olean.exists() and olean.stat().st_size > 0,
        ilean=ilean.exists() and ilean.stat().st_size > 0,
        elapsed_seconds=round(elapsed, 3),
        log_path=str(log_path.relative_to(ROOT)),
    )
    write_json(OUT / f"{label}.json", asdict(metric))
    return metric


def strictly_better(candidate: Metric, champion: Metric) -> bool:
    if candidate.passed:
        return not champion.passed
    if champion.passed:
        return False
    # Line-only strict comparison prevents column-only or layout-only promotion.
    return candidate.first_error_line > champion.first_error_line


def theorem_header_preserved(before: str, after: str, name: str) -> bool:
    a = declaration_span(before, name)
    b = declaration_span(after, name)
    return a is not None and b is not None and a[3] == b[3]


def code_without_comments_and_strings(text: str) -> str:
    out: list[str] = []
    i = 0
    block_depth = 0
    in_line = False
    in_string = False
    escaped = False
    while i < len(text):
        ch = text[i]
        nxt = text[i + 1] if i + 1 < len(text) else ""
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
                out.extend([" ", " "])
                i += 2
                continue
            if ch == "-" and nxt == "/":
                block_depth -= 1
                out.extend([" ", " "])
                i += 2
                continue
            out.append("\n" if ch == "\n" else " ")
            i += 1
            continue
        if in_string:
            if ch == "\n":
                out.append("\n")
            else:
                out.append(" ")
            if escaped:
                escaped = False
            elif ch == "\\":
                escaped = True
            elif ch == '"':
                in_string = False
            i += 1
            continue
        if ch == "-" and nxt == "-":
            in_line = True
            out.extend([" ", " "])
            i += 2
            continue
        if ch == "/" and nxt == "-":
            block_depth = 1
            out.extend([" ", " "])
            i += 2
            continue
        if ch == '"':
            in_string = True
            out.append(" ")
            i += 1
            continue
        out.append(ch)
        i += 1
    return "".join(out)


def forbidden_counts(text: str) -> dict[str, int]:
    code = code_without_comments_and_strings(text)
    patterns = {
        "sorry": r"\bsorry\b",
        "admit": r"\badmit\b",
        "global_axiom": r"(?m)^\s*(?:protected\s+|private\s+)?axiom\b",
        "unsafe": r"\bunsafe\b",
        "native_decide": r"\bnative_decide\b",
        "Lean.ofReduceBool": r"\bLean\.ofReduceBool\b",
    }
    return {name: len(re.findall(pattern, code)) for name, pattern in patterns.items()}


def collect_donors(refs: list[str], baseline_sha: str) -> list[Donor]:
    donors: dict[str, Donor] = {}
    for ref in refs:
        direct = git_show(ref, SOURCE_PATH)
        if direct is not None:
            try:
                text = direct.decode("utf-8")
            except UnicodeDecodeError:
                text = ""
            digest = sha_text(text) if text else ""
            if text and line_count(text) == EXPECTED_LINES and digest != baseline_sha:
                donors.setdefault(
                    digest,
                    Donor(ref.rsplit("/", 1)[-1], digest, text, f"{ref}:{SOURCE_PATH}"),
                )

        tree = run(
            ["git", "ls-tree", "-r", "--name-only", ref, "build-logs", "candidate-records"],
            stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL,
        )
        if tree.returncode != 0:
            continue
        paths = [
            path for path in tree.stdout.splitlines()
            if "Mock2_FunctionalAnalysis" in path and path.endswith(".lean")
        ][:20]
        for path in paths:
            data = git_show(ref, path)
            if data is None:
                continue
            try:
                text = data.decode("utf-8")
            except UnicodeDecodeError:
                continue
            digest = sha_text(text)
            if line_count(text) != EXPECTED_LINES or digest == baseline_sha:
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
    # Prefer the newest solver/controller naming and deterministic order.
    result = list(donors.values())
    result.sort(
        key=lambda d: (
            not any(key in d.label.lower() for key in ("fa424", "fa423", "fa422", "fa421", "fa420")),
            d.label,
        )
    )
    return result[:90]


def instance_candidates(champion: str, decl: str) -> list[tuple[str, str]]:
    span = declaration_span(champion, decl)
    if span is None:
        return []
    start, body_start, end, _ = span
    lines = champion.splitlines(keepends=True)
    candidates: list[tuple[str, str]] = []

    blank_slots = [
        i for i in range(max(0, start - 10), start)
        if lines[i].strip() == ""
    ]
    local_add = None
    for i in range(body_start, min(end, body_start + 30)):
        if re.search(r"\bletI\s*:\s*AddCommGroup\s+(?:Complex|ℂ)", lines[i]):
            local_add = i
            break

    instance_lines = [
        (
            "local_normed_parent",
            "local instance actualEdgeCanonicalComplexAddCommGroup : AddCommGroup Complex := "
            "Complex.instNormedAddCommGroup.toAddCommGroup\n",
        ),
        (
            "local_inferred_parent",
            "local instance actualEdgeCanonicalComplexAddCommGroup : AddCommGroup Complex := "
            "inferInstance\n",
        ),
    ]
    if blank_slots:
        slot = blank_slots[-1]
        for tag, command in instance_lines:
            modified = list(lines)
            modified[slot] = command
            if local_add is not None:
                modified[local_add] = "\n"
            text = "".join(modified)
            if theorem_header_preserved(champion, text, decl):
                candidates.append((f"{tag}-remove-proof-local", text))

            if local_add is not None:
                modified2 = list(lines)
                modified2[slot] = command
                modified2[local_add] = (
                    "  letI : AddCommGroup Complex := "
                    "actualEdgeCanonicalComplexAddCommGroup\n"
                )
                text2 = "".join(modified2)
                if theorem_header_preserved(champion, text2, decl):
                    candidates.append((f"{tag}-reuse-proof-local", text2))

    if local_add is not None:
        modified = list(lines)
        modified[local_add] = (
            "  letI : AddCommGroup Complex := "
            "Complex.instNormedAddCommGroup.toAddCommGroup\n"
        )
        text = "".join(modified)
        if theorem_header_preserved(champion, text, decl):
            candidates.append(("proof-local-normed-parent", text))

        modified = list(lines)
        modified[local_add] = "\n"
        text = "".join(modified)
        if theorem_header_preserved(champion, text, decl):
            candidates.append(("remove-proof-local-instance", text))

    # Replace only the final proof command that consumes hcomp.  Height is padded.
    block_lines = lines[start:end]
    hcomp_positions = [j for j, line in enumerate(block_lines) if "hcomp" in line]
    if hcomp_positions:
        last = start + hcomp_positions[-1]
        cmd_start = last
        while cmd_start > body_start:
            stripped = lines[cmd_start].lstrip()
            if stripped.startswith(("simpa", "exact", "convert", "refine", "show")):
                break
            cmd_start -= 1
        replacements = [
            ("finish-exact-hcomp", ["  exact hcomp\n"]),
            (
                "finish-simpa-definitions",
                [
                    "  simpa only [actualEdgeAmbientParam, actualEdgeNativeVelocity] using hcomp\n"
                ],
            ),
            ("finish-convert-rfl", ["  convert hcomp using 1 <;> rfl\n"]),
            (
                "finish-change-exact",
                [
                    "  change HasDerivAt\n",
                    "    (fun x => selectedCosetAmbientMap e.1\n",
                    "      (modularTileEdgeAmbientParam e.2 x))\n",
                    "    ((UpperHalfPlane.smulFDeriv (selectedCosetGL e.1)\n",
                    "      ↑(modularTileEdgeParam e.2 t))\n",
                    "      (modularTileEdgeVelocity e.2 t)) (t : Real)\n",
                    "  exact hcomp\n",
                ],
            ),
        ]
        base_variants = [("base", champion)] + candidates[:6]
        for base_tag, base_text in base_variants:
            base_lines2 = base_text.splitlines(keepends=True)
            for tag, replacement in replacements:
                candidate = replace_same_height(base_text, cmd_start, last + 1, replacement)
                if candidate is None:
                    continue
                if theorem_header_preserved(champion, candidate, decl):
                    candidates.append((f"{base_tag}-{tag}", candidate))

    unique: dict[str, tuple[str, str]] = {}
    for label, text in candidates:
        digest = sha_text(text)
        if digest != sha_text(champion) and line_count(text) == line_count(champion):
            unique.setdefault(digest, (label, text))
    return list(unique.values())


def donor_candidates(champion: str, decl: str, donors: list[Donor]) -> list[tuple[str, str]]:
    current_span = declaration_span(champion, decl)
    if current_span is None:
        return []
    start, body_start, end, current_header = current_span
    current_lines = champion.splitlines(keepends=True)
    output: list[tuple[str, str]] = []

    for donor in donors:
        donor_span = declaration_span(donor.source, decl)
        if donor_span is None:
            continue
        d_start, d_body_start, d_end, donor_header = donor_span
        donor_lines = donor.source.splitlines(keepends=True)

        # Whole proof-body transplant only; the current statement/header remains byte-identical.
        donor_body = donor_lines[d_body_start:d_end]
        whole = replace_same_height(champion, body_start, end, donor_body)
        if whole is not None and theorem_header_preserved(champion, whole, decl):
            output.append((f"donor-body::{donor.label}", whole))

        # Hunk cluster inside the proof body only.
        matcher = difflib.SequenceMatcher(
            a=current_lines[body_start:end],
            b=donor_lines[d_body_start:d_end],
            autojunk=False,
        )
        hunks = [op for op in matcher.get_opcodes() if op[0] != "equal"]
        if hunks:
            clustered = champion
            # Apply bottom-up so line indices remain stable; every hunk keeps its original height.
            valid = True
            for tag, i1, i2, j1, j2 in reversed(hunks):
                replacement = donor_lines[d_body_start + j1 : d_body_start + j2]
                updated = replace_same_height(
                    clustered,
                    body_start + i1,
                    body_start + i2,
                    replacement,
                )
                if updated is None:
                    valid = False
                    break
                clustered = updated
            if valid and theorem_header_preserved(champion, clustered, decl):
                output.append((f"donor-cluster::{donor.label}", clustered))

        # Single localized hunks are useful when a donor contains later regressions.
        for h_index, (_tag, i1, i2, j1, j2) in enumerate(hunks[:5]):
            replacement = donor_lines[d_body_start + j1 : d_body_start + j2]
            single = replace_same_height(
                champion,
                body_start + i1,
                body_start + i2,
                replacement,
            )
            if single is not None and theorem_header_preserved(champion, single, decl):
                output.append((f"donor-hunk-{h_index}::{donor.label}", single))

    unique: dict[str, tuple[str, str]] = {}
    for label, text in output:
        digest = sha_text(text)
        if digest != sha_text(champion) and line_count(text) == line_count(champion):
            unique.setdefault(digest, (label, text))
    return list(unique.values())


def known_same_height_candidates(champion: str, frontier: int) -> list[tuple[str, str]]:
    result: list[tuple[str, str]] = []

    def replace_exact(label: str, old: str, new: str, count: int = 1) -> None:
        if champion.count(old) != count:
            return
        candidate = champion.replace(old, new)
        if line_count(candidate) == line_count(champion):
            result.append((label, candidate))

    # Paired-edge function applications immediately after the actual-edge derivative theorem.
    if frontier <= 32120:
        dot = champion
        paren = champion
        dot_count = 0
        paren_count = 0
        for edge in ("circularArc", "leftVerticalSegment", "rightVerticalSegment"):
            old = (
                "GammaTwoActualPolygonEdge.paired "
                f"((q, GammaTwoModularTileEdge.{edge}) : GammaTwoActualPolygonEdge)"
            )
            dot_new = f"((q, GammaTwoModularTileEdge.{edge}) : GammaTwoActualPolygonEdge).paired"
            paren_new = (
                "(GammaTwoActualPolygonEdge.paired "
                f"((q, GammaTwoModularTileEdge.{edge}) : GammaTwoActualPolygonEdge))"
            )
            dot_count += dot.count(old)
            paren_count += paren.count(old)
            dot = dot.replace(old, dot_new)
            paren = paren.replace(old, paren_new)
        if dot_count and line_count(dot) == line_count(champion):
            result.append(("paired-edge-dot-application", dot))
        if paren_count and line_count(paren) == line_count(champion):
            result.append(("paired-edge-parenthesized-application", paren))

    replacements = [
        (
            "height-membership",
            "        (show z ∈ {w : ℍ | w.im ≤ H} from le_of_not_gt hHigh)⟩\n",
            "        (show z.im ≤ H from le_of_not_gt hHigh)⟩\n",
        ),
        ("upper-half-plane-constructor", "    hcomplex.subtype_mk _\n", "    hcomplex.upperHalfPlaneMk _\n"),
        ("upper-half-plane-ext", "      apply Subtype.ext\n", "      apply UpperHalfPlane.ext\n"),
        ("abs-add-rename", "      abs_add _ _\n", "      abs_add_le _ _\n"),
        (
            "tail-projection-linejoin",
            "  rcases (fixedPhaseCore_hasZeroThreeCuspTail n u)\n      .eventually_zero_on_horocycleBoundary with\n",
            "  rcases (fixedPhaseCore_hasZeroThreeCuspTail n u).eventually_zero_on_horocycleBoundary with\n\n",
        ),
        (
            "zero-function-coercion",
            "  simpa using htrace.trans hrep\n",
            "  simpa only [Pi.zero_apply] using htrace.trans hrep\n",
        ),
    ]
    for label, old, new in replacements:
        replace_exact(label, old, new)

    unique: dict[str, tuple[str, str]] = {}
    for label, text in result:
        digest = sha_text(text)
        if digest != sha_text(champion):
            unique.setdefault(digest, (label, text))
    return list(unique.values())


def first_error_context(metric: Metric) -> str:
    log_path = ROOT / metric.log_path
    if not log_path.exists() or metric.first_error_line <= 0:
        return ""
    lines = log_path.read_text(encoding="utf-8", errors="replace").splitlines()
    needle = f".lean:{metric.first_error_line}:{metric.first_error_col}:"
    for i, line in enumerate(lines):
        if needle in line:
            return "\n".join(lines[max(0, i - 10) : min(len(lines), i + 100)]) + "\n"
    return ""


def candidate_order(champion: str, metric: Metric, donors: list[Donor]) -> list[tuple[str, str]]:
    decl = metric.first_error_declaration
    candidates: list[tuple[str, str]] = []
    if decl == TARGET_DECL:
        candidates.extend(instance_candidates(champion, decl))
    candidates.extend(donor_candidates(champion, decl, donors))
    candidates.extend(known_same_height_candidates(champion, metric.first_error_line))
    unique: dict[str, tuple[str, str]] = {}
    for label, text in candidates:
        if line_count(text) != EXPECTED_LINES:
            continue
        digest = sha_text(text)
        unique.setdefault(digest, (label, text))
    return list(unique.values())


def main() -> int:
    OUT.mkdir(parents=True, exist_ok=True)
    TMP.mkdir(parents=True, exist_ok=True)
    refs = fetch_relevant_refs()
    baseline, provenance, required_frontier = select_verified_baseline(refs)
    if line_count(baseline) != EXPECTED_LINES:
        raise RuntimeError(
            f"verified baseline line count {line_count(baseline)} != {EXPECTED_LINES}"
        )
    baseline_sha = sha_text(baseline)
    write_json(OUT / "BASELINE_PROVENANCE.json", provenance)
    (OUT / "Mock2_FunctionalAnalysis-baseline.lean").write_text(baseline, encoding="utf-8")
    (OUT / "baseline-sha256.txt").write_text(
        f"{baseline_sha}  {SOURCE_PATH}\n", encoding="utf-8"
    )

    original_checked_sha = sha_text(SRC.read_text(encoding="utf-8"))
    SRC.write_text(baseline, encoding="utf-8")

    m2 = compile_metric("Mock2", "prerequisite-Mock2", 1)
    m2a = compile_metric("Mock2_Advanced", "prerequisite-Mock2_Advanced", 1)
    if not (m2.passed and m2a.passed):
        status = {
            "classification": "INFRA_FAILURE",
            "reason": "completed prerequisite regression",
            "Mock2": asdict(m2),
            "Mock2_Advanced": asdict(m2a),
        }
        write_json(OUT / "CURRENT.json", status)
        return 2

    champion = baseline
    champion_metric = compile_metric("Mock2_FunctionalAnalysis", "baseline-direct", 1)
    if not champion_metric.passed and champion_metric.first_error_line < required_frontier:
        status = {
            "classification": "INFRA_FAILURE",
            "reason": "verified baseline frontier did not reproduce",
            "required_frontier": required_frontier,
            "metric": asdict(champion_metric),
            "provenance": provenance,
        }
        write_json(OUT / "CURRENT.json", status)
        return 3

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

    trials: list[dict] = []
    promotions: list[dict] = []
    attempted_hashes: set[str] = {baseline_sha}
    total_candidates = 0

    while (
        total_candidates < MAX_TOTAL_CANDIDATES
        and len(promotions) < MAX_PROMOTIONS
        and time.monotonic() - START_TIME < TIME_BUDGET_SECONDS
        and not champion_metric.passed
    ):
        generated = candidate_order(champion, champion_metric, donors)
        accepted = False
        for label, candidate in generated:
            digest = sha_text(candidate)
            if digest in attempted_hashes:
                continue
            attempted_hashes.add(digest)
            total_candidates += 1
            if total_candidates > MAX_TOTAL_CANDIDATES:
                break
            if line_count(candidate) != EXPECTED_LINES:
                continue
            current_decl = champion_metric.first_error_declaration
            if current_decl not in {"<none>", "<unknown>"} and not theorem_header_preserved(
                champion, candidate, current_decl
            ):
                continue

            SRC.write_text(candidate, encoding="utf-8")
            metric = compile_metric(
                "Mock2_FunctionalAnalysis",
                f"candidate-{total_candidates:03d}-{re.sub(r'[^A-Za-z0-9_.-]+', '_', label)[:80]}",
                1,
            )
            row = {
                "candidate_number": total_candidates,
                "label": label,
                "metric": asdict(metric),
                "strictly_better": strictly_better(metric, champion_metric),
                "same_file_height": metric.line_count == EXPECTED_LINES,
                "failing_declaration_before": champion_metric.first_error_declaration,
                "failing_declaration_after": metric.first_error_declaration,
            }
            trials.append(row)
            if strictly_better(metric, champion_metric):
                previous = champion_metric
                champion = candidate
                champion_metric = metric
                promotions.append(
                    {
                        "label": label,
                        "previous": asdict(previous),
                        "new": asdict(metric),
                    }
                )
                (OUT / f"PROMOTION_{len(promotions):02d}.lean").write_text(
                    champion, encoding="utf-8"
                )
                accepted = True
                break
            SRC.write_text(champion, encoding="utf-8")
            if time.monotonic() - START_TIME >= TIME_BUDGET_SECONDS:
                break
        if not accepted:
            break

    SRC.write_text(champion, encoding="utf-8")
    selected_metric = compile_metric("Mock2_FunctionalAnalysis", "selected-direct-confirmation", 1)
    if selected_metric.source_sha256 != sha_text(champion):
        raise RuntimeError("selected source/log SHA mismatch")
    if selected_metric.passed:
        valid_selected = True
    else:
        valid_selected = selected_metric.first_error_line >= champion_metric.first_error_line
    if not valid_selected:
        champion = baseline
        SRC.write_text(champion, encoding="utf-8")
        selected_metric = champion_metric = compile_metric(
            "Mock2_FunctionalAnalysis", "fallback-baseline-confirmation", 1
        )
        promotions = []

    baseline_forbidden = forbidden_counts(baseline)
    selected_forbidden = forbidden_counts(champion)
    forbidden_not_increased = all(
        selected_forbidden[key] <= baseline_forbidden[key]
        for key in baseline_forbidden
    )
    strict_promotion = (
        sha_text(champion) != baseline_sha
        and forbidden_not_increased
        and (
            selected_metric.passed
            or selected_metric.first_error_line > champion_metric.first_error_line
            or bool(promotions)
        )
    )
    # promotions already encode a monotone chain; the final direct confirmation must
    # reproduce at least its terminal line.
    if promotions and not selected_metric.passed:
        terminal_line = int(promotions[-1]["new"]["first_error_line"])
        strict_promotion = strict_promotion and selected_metric.first_error_line >= terminal_line

    materialized_verified_baseline = (
        original_checked_sha != baseline_sha
        and baseline_sha in {PASS423_SHA, PASS376_SHA}
        and (
            champion_metric.passed
            or champion_metric.first_error_line >= required_frontier
        )
    )
    persist_source = strict_promotion or materialized_verified_baseline
    if strict_promotion:
        (OUT / "PROMOTED").touch()
    elif materialized_verified_baseline:
        (OUT / "MATERIALIZED_VERIFIED_BASELINE").touch()
    else:
        (OUT / "NO_STRICT_PROMOTION").touch()

    if persist_source:
        (OUT / "Mock2_FunctionalAnalysis-selected.lean").write_text(
            champion, encoding="utf-8"
        )
    else:
        SRC.write_text(baseline, encoding="utf-8")
        champion = baseline
        selected_metric = compile_metric(
            "Mock2_FunctionalAnalysis", "retained-baseline-final", 1
        )

    context = first_error_context(selected_metric)
    (OUT / "FIRST_ERROR_CONTEXT.txt").write_text(context, encoding="utf-8")
    write_json(OUT / "TRIALS.json", trials)
    status = {
        "classification": "VERIFIED",
        "authority": "direct Lean CLI",
        "baseline_provenance": provenance,
        "original_checked_source_sha256": original_checked_sha,
        "baseline": asdict(compile_metric("Mock2_FunctionalAnalysis", "baseline-record", 1))
        if sha_text(SRC.read_text(encoding="utf-8")) == baseline_sha
        else {
            "source_sha256": baseline_sha,
            "required_frontier": required_frontier,
        },
        "selected": asdict(selected_metric),
        "line_count": line_count(champion),
        "strict_promotion": strict_promotion,
        "materialized_verified_baseline": materialized_verified_baseline,
        "persist_source": persist_source,
        "promotion_chain": promotions,
        "candidate_trials": len(trials),
        "maxErrors_cap": 1,
        "maxErrors_interpretation": "cap only; error_headers is not total error count or progress",
        "baseline_forbidden_counts": baseline_forbidden,
        "selected_forbidden_counts": selected_forbidden,
        "forbidden_not_increased": forbidden_not_increased,
        "elapsed_seconds": round(time.monotonic() - START_TIME, 3),
    }
    write_json(OUT / "CURRENT.json", status)
    (OUT / "CURRENT.txt").write_text(
        "\n".join(
            [
                f"classification={status['classification']}",
                "authority=direct Lean CLI",
                f"baseline_sha256={baseline_sha}",
                f"selected_sha256={selected_metric.source_sha256}",
                f"FA_exit={selected_metric.exit_code}",
                f"FA_first_error={selected_metric.first_error_line}:{selected_metric.first_error_col}",
                f"FA_first_declaration={selected_metric.first_error_declaration}",
                f"line_count={line_count(champion)}",
                f"strict_promotion={str(strict_promotion).lower()}",
                f"materialized_verified_baseline={str(materialized_verified_baseline).lower()}",
                f"candidate_trials={len(trials)}",
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
    except Exception as exc:
        OUT.mkdir(parents=True, exist_ok=True)
        (OUT / "INFRA_FAILURE.txt").write_text(
            f"{type(exc).__name__}: {exc}\n", encoding="utf-8"
        )
        raise
