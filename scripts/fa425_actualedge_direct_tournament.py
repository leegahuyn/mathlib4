#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import zipfile
from dataclasses import dataclass, asdict
from pathlib import Path
from typing import Callable

REPO = Path.cwd()
SRC = REPO / "PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean"
M2 = REPO / "PrimalitySheafVerification/Mock2.lean"
M2A = REPO / "PrimalitySheafVerification/Mock2_Advanced.lean"
OUT = REPO / "build-logs/fa425-actualedge-direct-tournament"
TMP = Path("/tmp/fa425-actualedge")
EXPECTED_423_SHA = "71dc36f16ebea92d537aa40a5d420443e4bcb93ccb76fea31efb40a6cb5c3aa0"
PASS376_SHA = "07f6efd3309c3cc23b86adf5811918b752b72c33a3f7a76213ce9beb10796da4"
EXPECTED_LINES = 60453
PASS423_RUN = 31317392557
SOURCE_REL = "PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean"
DECL = "actualEdgeAmbientParam_hasDerivAt"
ERROR_RE = re.compile(r"Mock2_FunctionalAnalysis\.lean:(\d+):(\d+):\s+(?:error(?:\([^)]*\))?:|error:)")
ANY_ERROR_RE = re.compile(r"\.lean:(\d+):(\d+):\s+(?:error(?:\([^)]*\))?:|error:)")
FORBIDDEN = {
    "sorry": re.compile(r"\bsorry\b"),
    "admit": re.compile(r"\badmit\b"),
    "axiom": re.compile(r"(?m)^\s*(?:protected\s+|private\s+)?axiom\b"),
    "unsafe": re.compile(r"\bunsafe\b"),
    "native_decide": re.compile(r"\bnative_decide\b"),
    "Lean.ofReduceBool": re.compile(r"\bLean\.ofReduceBool\b"),
}


def run(cmd: list[str], *, cwd: Path = REPO, check: bool = False, text: bool = True,
        stdout=None, stderr=None, env=None) -> subprocess.CompletedProcess:
    p = subprocess.run(cmd, cwd=cwd, check=False, text=text, stdout=stdout,
                       stderr=stderr, env=env)
    if check and p.returncode != 0:
        raise RuntimeError(f"command failed ({p.returncode}): {' '.join(cmd)}")
    return p


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def line_count_bytes(data: bytes) -> int:
    return data.count(b"\n") + (0 if data.endswith(b"\n") else 1)


def line_count_text(text: str) -> int:
    return text.count("\n") + (0 if text.endswith("\n") else 1)


def artifact_candidates(run_id: int) -> list[tuple[int, str]]:
    repo = os.environ.get("GITHUB_REPOSITORY", "leegahuyn/mathlib4")
    p = run(["gh", "api", f"/repos/{repo}/actions/runs/{run_id}/artifacts", "--paginate"],
            stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    if p.returncode != 0:
        return []
    raw = json.loads(p.stdout)
    if isinstance(raw, dict):
        artifacts = raw.get("artifacts", [])
    else:
        artifacts = []
        for page in raw:
            artifacts.extend(page.get("artifacts", []))
    return [(int(a["id"]), str(a.get("name", ""))) for a in artifacts if not a.get("expired")]


def download_exact_artifact_source(run_id: int, expected_sha: str) -> tuple[bytes | None, dict]:
    repo = os.environ.get("GITHUB_REPOSITORY", "leegahuyn/mathlib4")
    provenance: dict = {"run_id": run_id, "expected_sha256": expected_sha, "artifacts": []}
    for artifact_id, name in artifact_candidates(run_id):
        zip_path = TMP / f"artifact-{artifact_id}.zip"
        unpack = TMP / f"artifact-{artifact_id}"
        unpack.mkdir(parents=True, exist_ok=True)
        with zip_path.open("wb") as fh:
            p = run(["gh", "api", f"/repos/{repo}/actions/artifacts/{artifact_id}/zip"],
                    text=False, stdout=fh, stderr=subprocess.PIPE)
        if p.returncode != 0:
            provenance["artifacts"].append({"id": artifact_id, "name": name, "download": "failed"})
            continue
        try:
            with zipfile.ZipFile(zip_path) as zf:
                zf.extractall(unpack)
        except zipfile.BadZipFile:
            provenance["artifacts"].append({"id": artifact_id, "name": name, "zip": "invalid"})
            continue
        hits = []
        for path in unpack.rglob("*"):
            if not path.is_file():
                continue
            try:
                data = path.read_bytes()
            except OSError:
                continue
            if sha256_bytes(data) == expected_sha:
                hits.append((path, data))
        provenance["artifacts"].append({"id": artifact_id, "name": name, "sha_hits": len(hits)})
        if len(hits) == 1:
            path, data = hits[0]
            provenance.update({"artifact_id": artifact_id, "artifact_name": name,
                               "artifact_member": str(path.relative_to(unpack))})
            return data, provenance
    return None, provenance


def source_from_remote_refs(expected_sha: str) -> tuple[bytes | None, dict]:
    provenance: dict = {"expected_sha256": expected_sha, "searched_refs": []}
    patterns = ["*fa423*", "*fa424*", "*fa425*", "*champion*31726*", "*71dc36*"]
    run(["git", "fetch", "origin", "+refs/heads/*:refs/remotes/origin/*", "--depth=1"],
        stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    p = run(["git", "for-each-ref", "--format=%(refname)", "refs/remotes/origin"],
            stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    refs = p.stdout.splitlines() if p.returncode == 0 else []
    selected = []
    for ref in refs:
        low = ref.lower()
        if any(re.fullmatch(pat.replace("*", ".*"), low) for pat in patterns):
            selected.append(ref)
    for ref in selected:
        provenance["searched_refs"].append(ref)
        p = run(["git", "show", f"{ref}:{SOURCE_REL}"], text=False,
                stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
        if p.returncode == 0 and sha256_bytes(p.stdout) == expected_sha:
            provenance["ref"] = ref
            return p.stdout, provenance
    return None, provenance


def choose_baseline() -> tuple[bytes, dict, int]:
    data, provenance = download_exact_artifact_source(PASS423_RUN, EXPECTED_423_SHA)
    if data is None:
        data, ref_prov = source_from_remote_refs(EXPECTED_423_SHA)
        provenance["remote_ref_search"] = ref_prov
    if data is not None:
        return data, provenance, 31726

    data, p376 = download_exact_artifact_source(31267332510, PASS376_SHA)
    provenance["pass376_fallback"] = p376
    if data is None:
        current = SRC.read_bytes()
        digest = sha256_bytes(current)
        if digest not in {EXPECTED_423_SHA, PASS376_SHA}:
            raise RuntimeError(f"neither verified artifact source was recoverable; checked-in sha={digest}")
        return current, {"checked_in_fallback_sha256": digest}, 31726 if digest == EXPECTED_423_SHA else 31725
    return data, provenance, 31725


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
    log: str

    @property
    def passes(self) -> bool:
        return self.exit_code == 0 and self.error_headers == 0 and self.olean and self.ilean


def declaration_at(text: str, line_no: int) -> str:
    if line_no <= 0:
        return "<none>"
    lines = text.splitlines()
    idx = min(line_no - 1, len(lines) - 1)
    pat = re.compile(r"^(?:protected\s+|private\s+|noncomputable\s+)?(?:theorem|lemma|def|abbrev|instance|structure|class)\s+([^\s(:]+)")
    for i in range(idx, -1, -1):
        m = pat.match(lines[i])
        if m:
            return m.group(1)
    return "<unknown>"


def compile_source(stem: str, label: str, max_errors: int, error_re: re.Pattern[str]) -> Metric:
    src = REPO / f"PrimalitySheafVerification/{stem}.lean"
    lib = REPO / ".lake/build/lib/lean/PrimalitySheafVerification"
    lib.mkdir(parents=True, exist_ok=True)
    olean = lib / f"{stem}.olean"
    ilean = lib / f"{stem}.ilean"
    olean.unlink(missing_ok=True)
    ilean.unlink(missing_ok=True)
    log_path = OUT / f"{label}.log"
    with log_path.open("w", encoding="utf-8") as fh:
        p = run(["lake", "env", "lean", f"-DmaxErrors={max_errors}",
                 "-DwarningAsError=false", "-o", str(olean), "-i", str(ilean), str(src)],
                stdout=fh, stderr=subprocess.STDOUT)
    log = log_path.read_text(encoding="utf-8", errors="replace")
    matches = list(error_re.finditer(log))
    first_line = int(matches[0].group(1)) if matches else 0
    first_col = int(matches[0].group(2)) if matches else 0
    text = src.read_text(encoding="utf-8")
    metric = Metric(
        label=label,
        source_sha256=sha256_file(src),
        line_count=line_count_text(text),
        exit_code=p.returncode,
        error_headers=len(matches),
        first_error_line=first_line,
        first_error_col=first_col,
        first_error_declaration=declaration_at(text, first_line),
        max_errors=max_errors,
        olean=olean.exists() and olean.stat().st_size > 0,
        ilean=ilean.exists() and ilean.stat().st_size > 0,
        log=str(log_path.relative_to(REPO)),
    )
    (OUT / f"{label}.json").write_text(json.dumps(asdict(metric), indent=2) + "\n", encoding="utf-8")
    return metric


def metric_better(a: Metric, b: Metric) -> bool:
    if a.passes != b.passes:
        return a.passes
    if a.passes:
        return False
    return (a.first_error_line, a.first_error_col) > (b.first_error_line, b.first_error_col)


def forbidden_counts(text: str) -> dict[str, int]:
    # Conservative source audit.  The final gate also records matching lines.
    return {name: len(list(pat.finditer(text))) for name, pat in FORBIDDEN.items()}


def theorem_bounds(lines: list[str]) -> tuple[int, int, str]:
    start = next(i for i, line in enumerate(lines) if line.startswith(f"theorem {DECL}"))
    decl_pat = re.compile(r"^(?:protected\s+|private\s+|noncomputable\s+)?(?:theorem|lemma|def|abbrev|instance|structure|class)\b")
    end = len(lines)
    for i in range(start + 1, len(lines)):
        if decl_pat.match(lines[i]) and not lines[i].startswith("  "):
            end = i
            break
    block = "".join(lines[start:end])
    marker = block.find(":= by")
    if marker < 0:
        raise RuntimeError("target theorem does not contain ':= by'")
    header = block[:marker + len(":= by")]
    return start, end, header


def replace_span_same_height(lines: list[str], start: int, end: int, replacement: str) -> list[str]:
    out = list(lines)
    old_count = end - start
    repl = replacement.splitlines(keepends=True)
    if replacement and not replacement.endswith("\n"):
        repl[-1] += "\n"
    if len(repl) > old_count:
        raise ValueError("replacement is taller than original span")
    repl.extend(["\n"] * (old_count - len(repl)))
    out[start:end] = repl
    return out


def generate_theorem_candidates(baseline: str) -> dict[str, str]:
    lines = baseline.splitlines(keepends=True)
    start, end, header = theorem_bounds(lines)
    local_idx = None
    for i in range(start, end):
        if re.search(r"\bletI\s*:\s*AddCommGroup\s+(?:Complex|ℂ)", lines[i]):
            local_idx = i
            break
    blank_before = None
    for i in range(start - 1, max(-1, start - 12), -1):
        if lines[i].strip() == "":
            blank_before = i
            break

    def with_local_instance(kind: str, proof_instance: str | None, final_kind: str | None) -> str | None:
        out = list(lines)
        if kind == "top":
            if blank_before is None:
                return None
            out[blank_before] = (
                "local instance actualEdgeAmbientParamCanonicalComplexAddCommGroup : "
                "AddCommGroup Complex := Complex.instNormedAddCommGroup.toAddCommGroup\n"
            )
        if local_idx is not None:
            if proof_instance == "normed":
                out[local_idx] = (
                    "  letI : AddCommGroup Complex := "
                    "Complex.instNormedAddCommGroup.toAddCommGroup\n"
                )
            elif proof_instance == "ambient":
                out[local_idx] = "  -- use the ambient canonical Complex additive structure\n"
            elif proof_instance == "same_top":
                out[local_idx] = (
                    "  letI : AddCommGroup Complex := "
                    "actualEdgeAmbientParamCanonicalComplexAddCommGroup\n"
                )
        block = "".join(out[start:end])
        if final_kind is not None and "hcomp" in block:
            b_lines = out[start:end]
            h_indices = [j for j, line in enumerate(b_lines) if "hcomp" in line]
            if h_indices:
                last = h_indices[-1] + start
                simpa_start = last
                while simpa_start > start and "simpa" not in out[simpa_start] and "exact" not in out[simpa_start] and "convert" not in out[simpa_start]:
                    simpa_start -= 1
                if "simpa" in out[simpa_start] or "exact" in out[simpa_start] or "convert" in out[simpa_start]:
                    if final_kind == "exact":
                        out = replace_span_same_height(out, simpa_start, last + 1, "  exact hcomp\n")
                    elif final_kind == "simpa_defs":
                        out = replace_span_same_height(
                            out, simpa_start, last + 1,
                            "  simpa only [actualEdgeAmbientParam, actualEdgeNativeVelocity] using hcomp\n")
                    elif final_kind == "convert_rfl":
                        out = replace_span_same_height(out, simpa_start, last + 1,
                                                       "  convert hcomp using 1 <;> rfl\n")
        text = "".join(out)
        c_lines = text.splitlines(keepends=True)
        c_start, c_end, c_header = theorem_bounds(c_lines)
        if c_header != header or c_start != start or line_count_text(text) != line_count_text(baseline):
            return None
        return text

    candidates: dict[str, str] = {}
    specs = [
        ("proof_normed", "none", "normed", None),
        ("ambient_only", "none", "ambient", None),
        ("top_normed_ambient_body", "top", "ambient", None),
        ("top_normed_same_body", "top", "same_top", None),
        ("top_normed_proof_normed", "top", "normed", None),
        ("top_normed_exact", "top", "ambient", "exact"),
        ("top_normed_simpa_defs", "top", "ambient", "simpa_defs"),
        ("top_normed_convert_rfl", "top", "ambient", "convert_rfl"),
    ]
    for name, kind, proof_inst, final_kind in specs:
        text = with_local_instance(kind, proof_inst, final_kind)
        if text is not None and text != baseline:
            candidates[name] = text
    return candidates


def paired_variants(text: str) -> dict[str, str]:
    dot = text
    paren = text
    changed_dot = 0
    changed_paren = 0
    for edge in ["circularArc", "leftVerticalSegment", "rightVerticalSegment"]:
        old = (
            "GammaTwoActualPolygonEdge.paired "
            f"((q, GammaTwoModularTileEdge.{edge}) : GammaTwoActualPolygonEdge)"
        )
        new_dot = f"((q, GammaTwoModularTileEdge.{edge}) : GammaTwoActualPolygonEdge).paired"
        new_paren = (
            "(GammaTwoActualPolygonEdge.paired "
            f"((q, GammaTwoModularTileEdge.{edge}) : GammaTwoActualPolygonEdge))"
        )
        changed_dot += dot.count(old)
        changed_paren += paren.count(old)
        dot = dot.replace(old, new_dot)
        paren = paren.replace(old, new_paren)
    result = {}
    if changed_dot:
        result["paired_dot"] = dot
    if changed_paren:
        result["paired_parenthesized"] = paren
    return result


def normalization_variants(text: str) -> dict[str, str]:
    anchor = "  rw [nativeActualEdgeFluxIntegral_left_eq_selectedPiola hT]\n\n"
    result = {}
    if text.count(anchor) == 1:
        result["selected_piola_ring"] = text.replace(
            anchor, "  rw [nativeActualEdgeFluxIntegral_left_eq_selectedPiola hT]\n  ring\n")
        result["selected_piola_simp"] = text.replace(
            anchor, "  rw [nativeActualEdgeFluxIntegral_left_eq_selectedPiola hT]\n  simp\n")
    return result


def screen_candidate(label: str, text: str, baseline_header: str) -> Metric | None:
    if line_count_text(text) != EXPECTED_LINES:
        return None
    lines = text.splitlines(keepends=True)
    _, _, header = theorem_bounds(lines)
    if header != baseline_header:
        return None
    path = TMP / "candidates" / f"{label}.lean"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")
    SRC.write_text(text, encoding="utf-8")
    return compile_source("Mock2_FunctionalAnalysis", f"screen-{label}", 1, ERROR_RE)


def copy_context(metric: Metric) -> None:
    log_path = REPO / metric.log
    lines = log_path.read_text(encoding="utf-8", errors="replace").splitlines()
    context = []
    needle = f".lean:{metric.first_error_line}:{metric.first_error_col}:"
    for i, line in enumerate(lines):
        if needle in line:
            context = lines[max(0, i - 8): min(len(lines), i + 80)]
            break
    (OUT / "FIRST_ERROR_CONTEXT.txt").write_text("\n".join(context) + ("\n" if context else ""), encoding="utf-8")


def final_gates(best_text: str, promoted_metric: Metric) -> dict:
    result: dict = {"fa_true_pass": False, "downstream": {}}
    if not promoted_metric.passes:
        return result
    SRC.write_text(best_text, encoding="utf-8")
    fa2 = compile_source("Mock2_FunctionalAnalysis", "FA-gate-2", 1, ERROR_RE)
    result["FA_gate_1"] = asdict(promoted_metric)
    result["FA_gate_2"] = asdict(fa2)
    counts = forbidden_counts(best_text)
    result["forbidden_audit"] = counts
    audit_clean = all(v == 0 for v in counts.values())
    result["fa_true_pass"] = promoted_metric.passes and fa2.passes and audit_clean
    if not result["fa_true_pass"]:
        return result

    targets: list[str] = []
    integrated = REPO / "PrimalitySheafVerification/Mock2_FunctionalAnalysis_Integrated.lean"
    if integrated.exists():
        targets.append("Mock2_FunctionalAnalysis_Integrated")
    targets.extend(sorted(p.stem for p in (REPO / "PrimalitySheafVerification").glob("Mock3*.lean")))
    if (REPO / "PrimalitySheafVerification/QYM.lean").exists():
        targets.append("QYM")
    for stem in targets:
        runs = []
        for idx in (1, 2):
            metric = compile_source(stem, f"{stem}-gate-{idx}", 1,
                                    re.compile(rf"{re.escape(stem)}\.lean:(\d+):(\d+):\s+(?:error(?:\([^)]*\))?:|error:)"))
            runs.append(asdict(metric))
            if not metric.passes:
                break
        result["downstream"][stem] = runs
    result["all_downstream_2x"] = bool(targets) and all(
        len(runs) == 2 and all(r["exit_code"] == 0 and r["error_headers"] == 0 and r["olean"] and r["ilean"] for r in runs)
        for runs in result["downstream"].values()
    )
    return result


def main() -> int:
    OUT.mkdir(parents=True, exist_ok=True)
    TMP.mkdir(parents=True, exist_ok=True)
    baseline_data, provenance, required_frontier = choose_baseline()
    if line_count_bytes(baseline_data) != EXPECTED_LINES:
        raise RuntimeError(f"verified source line count mismatch: {line_count_bytes(baseline_data)}")
    baseline_sha = sha256_bytes(baseline_data)
    baseline_text = baseline_data.decode("utf-8")
    (OUT / "BASELINE_PROVENANCE.json").write_text(json.dumps(provenance, indent=2) + "\n", encoding="utf-8")
    (OUT / "baseline-source-sha256.txt").write_text(f"{baseline_sha}  {SOURCE_REL}\n", encoding="utf-8")
    (OUT / "Mock2_FunctionalAnalysis-baseline.lean").write_bytes(baseline_data)
    SRC.write_bytes(baseline_data)

    # Regressions in the two completed prerequisites block every FA promotion.
    m2 = compile_source("Mock2", "Mock2-prerequisite", 50,
                        re.compile(r"Mock2\.lean:(\d+):(\d+):\s+(?:error(?:\([^)]*\))?:|error:)"))
    m2a = compile_source("Mock2_Advanced", "Mock2_Advanced-prerequisite", 50,
                         re.compile(r"Mock2_Advanced\.lean:(\d+):(\d+):\s+(?:error(?:\([^)]*\))?:|error:)"))
    if not (m2.passes and m2a.passes):
        status = {"classification": "INFRA_OR_PREREQUISITE_FAILURE", "Mock2": asdict(m2),
                  "Mock2_Advanced": asdict(m2a), "baseline_sha256": baseline_sha}
        (OUT / "CURRENT.json").write_text(json.dumps(status, indent=2) + "\n", encoding="utf-8")
        return 2

    baseline_metric = compile_source("Mock2_FunctionalAnalysis", "baseline-authoritative", 1800, ERROR_RE)
    if baseline_metric.exit_code != 0 and baseline_metric.first_error_line < required_frontier:
        status = {"classification": "BASELINE_REPRODUCTION_FAILURE", "baseline": asdict(baseline_metric),
                  "required_frontier": required_frontier, "provenance": provenance}
        (OUT / "CURRENT.json").write_text(json.dumps(status, indent=2) + "\n", encoding="utf-8")
        return 3

    base_lines = baseline_text.splitlines(keepends=True)
    _, _, baseline_header = theorem_bounds(base_lines)
    best_text = baseline_text
    best_metric = baseline_metric
    trials: list[dict] = []

    for label, text in generate_theorem_candidates(baseline_text).items():
        metric = screen_candidate(label, text, baseline_header)
        if metric is None:
            continue
        trials.append(asdict(metric))
        if metric_better(metric, best_metric):
            best_text, best_metric = text, metric
        if metric.passes:
            break

    # Only after the target declaration is crossed do we touch the immediately
    # following paired-edge call sites.  Every variant preserves file height.
    target_lines = [i + 1 for i, line in enumerate(best_text.splitlines()) if line.startswith(f"theorem {DECL}")]
    target_line = target_lines[0] if target_lines else 0
    if best_metric.passes or best_metric.first_error_declaration != DECL or best_metric.first_error_line > target_line + 20:
        stage_base = best_text
        for label, text in paired_variants(stage_base).items():
            metric = screen_candidate(label, text, baseline_header)
            if metric is None:
                continue
            trials.append(asdict(metric))
            if metric_better(metric, best_metric):
                best_text, best_metric = text, metric
        stage_base = best_text
        for label, text in normalization_variants(stage_base).items():
            metric = screen_candidate(label, text, baseline_header)
            if metric is None:
                continue
            trials.append(asdict(metric))
            if metric_better(metric, best_metric):
                best_text, best_metric = text, metric

    # Re-run the selected candidate with a high diagnostic cap.  Promotion is
    # based on this direct Lean CLI result, never on the screening cap.
    SRC.write_text(best_text, encoding="utf-8")
    authoritative = compile_source("Mock2_FunctionalAnalysis", "selected-authoritative", 1800, ERROR_RE)
    if metric_better(authoritative, best_metric) or authoritative.passes:
        best_metric = authoritative
    else:
        # The first diagnostic must agree; otherwise reject the screening result.
        if (authoritative.first_error_line, authoritative.first_error_col) != (
            best_metric.first_error_line, best_metric.first_error_col
        ):
            best_text = baseline_text
            SRC.write_text(best_text, encoding="utf-8")
            best_metric = baseline_metric

    baseline_forbidden = forbidden_counts(baseline_text)
    best_forbidden = forbidden_counts(best_text)
    forbidden_not_increased = all(best_forbidden[k] <= baseline_forbidden[k] for k in FORBIDDEN)
    promoted = (
        sha256_bytes(best_text.encode()) != baseline_sha
        and line_count_text(best_text) == EXPECTED_LINES
        and forbidden_not_increased
        and (best_metric.passes or (best_metric.first_error_line, best_metric.first_error_col) >
             (baseline_metric.first_error_line, baseline_metric.first_error_col))
    )

    if promoted:
        SRC.write_text(best_text, encoding="utf-8")
        (OUT / "Mock2_FunctionalAnalysis-promoted.lean").write_text(best_text, encoding="utf-8")
        (OUT / "PROMOTED").touch()
    else:
        SRC.write_text(baseline_text, encoding="utf-8")
        (OUT / "RETAINED_BASELINE").touch()
        best_text = baseline_text
        best_metric = baseline_metric

    copy_context(best_metric)
    gates = final_gates(best_text, best_metric) if promoted else {"fa_true_pass": False}
    status = {
        "classification": "VERIFIED" if promoted else "VERIFIED_NO_STRICT_PROMOTION",
        "authority": "direct Lean CLI",
        "PASS423_run": PASS423_RUN,
        "baseline": asdict(baseline_metric),
        "selected": asdict(best_metric),
        "previous_frontier": [baseline_metric.first_error_line, baseline_metric.first_error_col],
        "new_frontier": [best_metric.first_error_line, best_metric.first_error_col],
        "same_file_height": line_count_text(best_text) == EXPECTED_LINES,
        "target_declaration_header_preserved": theorem_bounds(best_text.splitlines(keepends=True))[2] == baseline_header,
        "promoted": promoted,
        "baseline_forbidden_counts": baseline_forbidden,
        "selected_forbidden_counts": best_forbidden,
        "forbidden_not_increased": forbidden_not_increased,
        "screening_maxErrors": 1,
        "authoritative_maxErrors": 1800,
        "trials": trials,
        "gates": gates,
    }
    (OUT / "CURRENT.json").write_text(json.dumps(status, indent=2) + "\n", encoding="utf-8")
    (OUT / "CURRENT.txt").write_text(
        f"classification={status['classification']}\n"
        f"baseline_sha256={baseline_metric.source_sha256}\n"
        f"baseline_first={baseline_metric.first_error_line}:{baseline_metric.first_error_col}\n"
        f"selected_sha256={best_metric.source_sha256}\n"
        f"selected_exit={best_metric.exit_code}\n"
        f"selected_first={best_metric.first_error_line}:{best_metric.first_error_col}\n"
        f"selected_declaration={best_metric.first_error_declaration}\n"
        f"promoted={str(promoted).lower()}\n"
        f"FA_TRUE_PASS={str(gates.get('fa_true_pass', False)).lower()}\n",
        encoding="utf-8",
    )
    print(json.dumps(status, indent=2))
    return 0 if promoted or gates.get("fa_true_pass") else 1


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as exc:
        OUT.mkdir(parents=True, exist_ok=True)
        (OUT / "INFRA_FAILURE.txt").write_text(f"{type(exc).__name__}: {exc}\n", encoding="utf-8")
        raise
