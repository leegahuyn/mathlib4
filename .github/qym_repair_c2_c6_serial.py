#!/usr/bin/env python3
from __future__ import annotations

from dataclasses import dataclass
from difflib import SequenceMatcher
from pathlib import Path
import collections
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import zipfile

REPO = os.environ.get("GITHUB_REPOSITORY", "leegahuyn/mathlib4")
ROOT = Path(os.environ.get("GITHUB_WORKSPACE", Path.cwd())).resolve()
OUT = Path(os.environ.get("OUT", "/tmp/qym-c2-c6-serial")).resolve()
QYM = ROOT / "PrimalitySheafVerification/QYM.lean"
BASE = ROOT / ".github/qym-frontier/QYM_C1_BEST.lean"
FRONTIER = ROOT / ".github/qym-frontier"
BASE_SHA256 = "830563b33d873354809594d9e9dce962c1253052f8e70bd4d1513226f7598217"

ARTIFACTS = {
    "C02_intrinsic_mobius": 9354070486,
    "C03_using_bang_explicit_constants": 9353982088,
    "C04_mul_inv_using_bang": 9354072137,
    "C05_derive_and_normsq": 9353934515,
    "C05_derive_and_star": 9354094831,
    "C05_coordinate_star": 9354228988,
    "C06_helper_letI": 9354078873,
    "C06_inline_letI": 9354124499,
}

ERROR_RE = re.compile(
    r"^(?P<file>.*?\.lean):(?P<line>\d+):(?P<column>\d+): "
    r"(?P<severity>error|warning)(?:\((?P<code>[^)]*)\))?:\s*(?P<message>.*)$",
    re.M,
)
PANIC_RE = re.compile(
    r"(?im)^.*(?:internal error|uncaught exception|panic(?:!|:|\s)).*$"
)
C2_RE = re.compile(
    r"(?ms)^theorem actualFixedPhaseCuspHorocyclePoint_coe_contDiff\b.*?"
    r"(?=^/-- Restriction of every actual real-smooth automorphic core section)"
)
C2_GATE_MARKER = "/-- Restriction of every actual real-smooth automorphic core section"


@dataclass(frozen=True)
class Diagnostic:
    file: str
    line: int
    column: int
    severity: str
    code: str | None
    message: str


@dataclass
class Artifact:
    label: str
    artifact_id: int
    root: Path
    source: str
    result: dict
    diagnostics: list[Diagnostic]


@dataclass(frozen=True)
class Hunk:
    i1: int
    i2: int
    j1: int
    j2: int
    old: str
    new: str


def sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def git_blob(text: str) -> str:
    data = text.encode("utf-8")
    return hashlib.sha1(
        b"blob " + str(len(data)).encode("ascii") + b"\0" + data
    ).hexdigest()


def download_artifact(label: str, artifact_id: int) -> Path:
    target = OUT / "artifacts" / label
    archive = OUT / "downloads" / f"{label}.zip"
    target.mkdir(parents=True, exist_ok=True)
    archive.parent.mkdir(parents=True, exist_ok=True)
    env = os.environ.copy()
    token = env.get("GH_TOKEN") or env.get("GITHUB_TOKEN")
    if not token:
        raise RuntimeError("GH_TOKEN/GITHUB_TOKEN is required")
    env["GH_TOKEN"] = token
    with archive.open("wb") as handle:
        subprocess.run(
            [
                "gh",
                "api",
                f"/repos/{REPO}/actions/artifacts/{artifact_id}/zip",
            ],
            cwd=ROOT,
            env=env,
            stdout=handle,
            check=True,
        )
    with zipfile.ZipFile(archive) as zf:
        zf.extractall(target)
    return target


def parse_log(text: str) -> list[Diagnostic]:
    rows: list[Diagnostic] = []
    for match in ERROR_RE.finditer(text):
        row = match.groupdict()
        rows.append(
            Diagnostic(
                file=row["file"],
                line=int(row["line"]),
                column=int(row["column"]),
                severity=row["severity"],
                code=row["code"],
                message=row["message"],
            )
        )
    return rows


def load_artifact(label: str, artifact_id: int) -> Artifact:
    root = download_artifact(label, artifact_id)
    json_objects: list[tuple[Path, dict]] = []
    for path in root.rglob("*.json"):
        try:
            value = json.loads(path.read_text(errors="replace"))
        except Exception:
            continue
        if isinstance(value, dict):
            json_objects.append((path, value))

    sources = sorted(
        (path for path in root.rglob("*.lean") if path.stat().st_size > 2_000_000),
        key=lambda path: path.stat().st_size,
        reverse=True,
    )
    if not sources:
        raise RuntimeError(f"{label}: no full QYM candidate source found")

    selected_source: Path | None = None
    selected_result: dict | None = None
    for source_path in sources:
        digest = hashlib.sha256(source_path.read_bytes()).hexdigest()
        for _, obj in json_objects:
            if obj.get("candidate_qym_sha256") == digest and "error_headers" in obj:
                selected_source = source_path
                selected_result = obj
                break
        if selected_source is not None:
            break
    if selected_source is None:
        selected_source = sources[0]
        matching = [obj for _, obj in json_objects if "error_headers" in obj]
        if not matching:
            raise RuntimeError(f"{label}: no result JSON found")
        selected_result = min(matching, key=lambda obj: int(obj["error_headers"]))

    diagnostics: list[Diagnostic] = []
    diagnostic_files = list(root.rglob("diagnostics.jsonl"))
    if diagnostic_files:
        for line in diagnostic_files[0].read_text(errors="replace").splitlines():
            try:
                row = json.loads(line)
            except Exception:
                continue
            if row.get("severity") not in {"error", "warning"}:
                continue
            diagnostics.append(
                Diagnostic(
                    file=str(row.get("file", "")),
                    line=int(row.get("line", 0)),
                    column=int(row.get("column", 0)),
                    severity=str(row.get("severity")),
                    code=row.get("code"),
                    message=str(row.get("message", "")),
                )
            )
    else:
        logs = sorted(root.rglob("full.log"), key=lambda path: path.stat().st_size, reverse=True)
        if not logs:
            logs = sorted(root.rglob("*.log"), key=lambda path: path.stat().st_size, reverse=True)
        if logs:
            diagnostics = parse_log(logs[0].read_text(errors="replace"))

    assert selected_result is not None
    return Artifact(
        label=label,
        artifact_id=artifact_id,
        root=root,
        source=selected_source.read_text(encoding="utf-8"),
        result=selected_result,
        diagnostics=diagnostics,
    )


def diff_hunks(base: str, candidate: str) -> list[Hunk]:
    base_lines = base.splitlines(keepends=True)
    candidate_lines = candidate.splitlines(keepends=True)
    matcher = SequenceMatcher(None, base_lines, candidate_lines, autojunk=False)
    hunks: list[Hunk] = []
    for tag, i1, i2, j1, j2 in matcher.get_opcodes():
        if tag == "equal":
            continue
        hunks.append(
            Hunk(
                i1=i1,
                i2=i2,
                j1=j1,
                j2=j2,
                old="".join(base_lines[i1:i2]),
                new="".join(candidate_lines[j1:j2]),
            )
        )
    changed = sum(max(h.i2 - h.i1, h.j2 - h.j1) for h in hunks)
    if not hunks or changed > 1200:
        raise RuntimeError(f"unexpected candidate diff size: hunks={len(hunks)} changed={changed}")
    return hunks


def errors_inside_candidate_hunks(artifact: Artifact, hunks: list[Hunk]) -> int:
    ranges = [(h.j1 + 1, max(h.j1 + 1, h.j2 + 1)) for h in hunks]
    return sum(
        1
        for row in artifact.diagnostics
        if row.severity == "error" and any(lo <= row.line <= hi for lo, hi in ranges)
    )


def apply_hunks(current: str, hunks: list[Hunk]) -> tuple[str, int]:
    text = current
    gate = 0
    for hunk in hunks:
        if hunk.old:
            occurrences = text.count(hunk.old)
            if occurrences != 1:
                raise RuntimeError(
                    f"candidate hunk old block occurrence count is {occurrences}, expected 1"
                )
            index = text.index(hunk.old)
            text = text[:index] + hunk.new + text[index + len(hunk.old):]
            gate = max(gate, text.count("\n", 0, index + len(hunk.new)) + 1)
        else:
            raise RuntimeError("pure insertion hunk is not accepted for theorem repair")
    return text, gate


def c2_theorem(hx_proof: str) -> str:
    return f'''theorem actualFixedPhaseCuspHorocyclePoint_coe_contDiff
    (kappa : GammaTwoCusp) (Y : ℝ) :
    ContDiff ℝ ∞
      (fun x : ℝ =>
        ((actualFixedPhaseCuspHorocyclePoint kappa Y x : ℍ) : ℂ)) := by
  let g : GL (Fin 2) ℝ :=
    (gammaTwoCuspScaling kappa : GL (Fin 2) ℝ)
  have hg : 0 < g.det.val := by
    simp [g]
  have hx : ContDiff ℝ ∞ (fun x : ℝ => (x : ℂ)) := by
{hx_proof}
  have hz : ContDiff ℝ ∞
      (fun x : ℝ =>
        (x : ℂ) + (actualFixedPhaseCuspHeight Y : ℂ) * Complex.I) := by
    exact hx.add
      (contDiff_const : ContDiff ℝ ∞
        (fun _ : ℝ => (actualFixedPhaseCuspHeight Y : ℂ) * Complex.I))
  have hnum : ContDiff ℝ ∞
      (fun x : ℝ =>
        UpperHalfPlane.num g
          (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ)) := by
    simp only [UpperHalfPlane.num,
      actualFixedPhaseHorizontalHorocyclePoint,
      UpperHalfPlane.coe_mk]
    exact
      (((contDiff_const : ContDiff ℝ ∞
          (fun _ : ℝ => ((g 0 0 : ℝ) : ℂ))).mul hz).add
        (contDiff_const : ContDiff ℝ ∞
          (fun _ : ℝ => ((g 0 1 : ℝ) : ℂ))))
  have hdenDiff : ContDiff ℝ ∞
      (fun x : ℝ =>
        UpperHalfPlane.denom g
          (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ)) := by
    simp only [UpperHalfPlane.denom,
      actualFixedPhaseHorizontalHorocyclePoint,
      UpperHalfPlane.coe_mk]
    exact
      (((contDiff_const : ContDiff ℝ ∞
          (fun _ : ℝ => ((g 1 0 : ℝ) : ℂ))).mul hz).add
        (contDiff_const : ContDiff ℝ ∞
          (fun _ : ℝ => ((g 1 1 : ℝ) : ℂ))))
  have hden : ∀ x : ℝ,
      UpperHalfPlane.denom g
        (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ) ≠ 0 := by
    intro x
    exact UpperHalfPlane.denom_ne_zero g
      (actualFixedPhaseHorizontalHorocyclePoint Y x)
  have hfrac : ContDiff ℝ ∞
      (fun x : ℝ =>
        UpperHalfPlane.num g
            (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ) /
          UpperHalfPlane.denom g
            (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ)) := by
    simpa only [div_eq_mul_inv] using
      hnum.mul (hdenDiff.inv hden)
  change ContDiff ℝ ∞
    (fun x : ℝ =>
      (↑(g • actualFixedPhaseHorizontalHorocyclePoint Y x) : ℂ))
  simpa only [UpperHalfPlane.coe_smul_of_det_pos hg] using hfrac
'''


C2_VARIANTS = {
    "ofRealCLM_typed_apply": c2_theorem(
        "    simpa only [Complex.ofRealCLM_apply] using\n"
        "      (Complex.ofRealCLM.contDiff :\n"
        "        ContDiff ℝ ∞ (fun x : ℝ => Complex.ofRealCLM x))"
    ),
    "ofRealCLM_coe_function": c2_theorem(
        "    simpa using\n"
        "      ((Complex.ofRealCLM : ℝ →L[ℝ] ℂ).contDiff :\n"
        "        ContDiff ℝ ∞ (Complex.ofRealCLM : ℝ → ℂ))"
    ),
    "ofRealCLM_defeq": c2_theorem(
        "    exact\n"
        "      ((Complex.ofRealCLM : ℝ →L[ℝ] ℂ).contDiff :\n"
        "        ContDiff ℝ ∞ (fun x : ℝ => (x : ℂ)))"
    ),
    "ofRealCLM_simpa": c2_theorem(
        "    simpa using ((Complex.ofRealCLM : ℝ →L[ℝ] ℂ).contDiff)"
    ),
    "split_fun_prop": c2_theorem("    fun_prop"),
}


def replace_c2(text: str, theorem: str) -> tuple[str, int]:
    matches = list(C2_RE.finditer(text))
    if len(matches) != 1:
        raise RuntimeError(f"expected one C2 theorem, found {len(matches)}")
    match = matches[0]
    updated = text[:match.start()] + theorem.rstrip() + "\n\n" + text[match.end():]
    marker = updated.find(C2_GATE_MARKER)
    if marker < 0:
        raise RuntimeError("C2 gate marker is missing")
    return updated, updated.count("\n", 0, marker) + 1


def audit_forbidden(text: str) -> dict[str, int]:
    return {
        "sorry": len(re.findall(r"\bsorry\b", text)),
        "admit": len(re.findall(r"\badmit\b", text)),
        "native_decide": len(re.findall(r"\bnative_decide\b", text)),
        "Lean.ofReduceBool": text.count("Lean.ofReduceBool"),
        "global_axiom": len(re.findall(r"(?m)^\s*axiom\s+", text)),
        "unsafe": len(re.findall(r"(?m)^\s*unsafe\s+", text)),
        "maxHeartbeats_zero": len(
            re.findall(r"set_option\s+maxHeartbeats\s+0\b", text)
        ),
    }


def run_lean(text: str, label: str, max_errors: int) -> dict:
    QYM.write_text(text, encoding="utf-8")
    log = OUT / f"{label}.log"
    time_file = OUT / f"{label}.time"
    olean = OUT / f"{label}.olean"
    ilean = OUT / f"{label}.ilean"
    for path in (olean, ilean):
        path.unlink(missing_ok=True)
    command = [
        "/usr/bin/time",
        "-v",
        "-o",
        str(time_file),
        "lake",
        "env",
        "lean",
        f"-DmaxErrors={max_errors}",
        "-DwarningAsError=false",
        "-o",
        str(olean),
        "-i",
        str(ilean),
        str(QYM.relative_to(ROOT)),
    ]
    with log.open("w", encoding="utf-8", errors="replace") as handle:
        proc = subprocess.run(command, cwd=ROOT, stdout=handle, stderr=subprocess.STDOUT)
    raw = log.read_bytes()
    decoded = raw.decode(errors="replace")
    diagnostics = parse_log(decoded)
    errors = [row for row in diagnostics if row.severity == "error"]
    warnings = [row for row in diagnostics if row.severity == "warning"]
    panics = PANIC_RE.findall(decoded)
    result = {
        "label": label,
        "exit": proc.returncode,
        "error_headers": len(errors),
        "warning_headers": len(warnings),
        "panic_lines": len(panics),
        "first_error": None
        if not errors
        else {
            "file": errors[0].file,
            "line": errors[0].line,
            "column": errors[0].column,
            "code": errors[0].code,
            "message": errors[0].message,
        },
        "last_error": None
        if not errors
        else {
            "file": errors[-1].file,
            "line": errors[-1].line,
            "column": errors[-1].column,
            "code": errors[-1].code,
            "message": errors[-1].message,
        },
        "error_codes": dict(
            sorted(collections.Counter(row.code or "uncoded" for row in errors).items())
        ),
        "log_sha256": hashlib.sha256(raw).hexdigest(),
        "qym_sha256": sha256_text(text),
    }
    (OUT / f"{label}.json").write_text(
        json.dumps(result, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return result


def gate_passed(result: dict, gate: int) -> bool:
    if int(result["panic_lines"]) != 0:
        return False
    first = result["first_error"]
    return first is None or int(first["line"]) >= gate


def choose_artifact_variant(
    stage: str,
    base_text: str,
    current: str,
    artifacts: list[Artifact],
) -> tuple[str, str, int, dict]:
    ranked: list[tuple[int, int, str, Artifact, list[Hunk]]] = []
    for artifact in artifacts:
        hunks = diff_hunks(base_text, artifact.source)
        inside = errors_inside_candidate_hunks(artifact, hunks)
        ranked.append(
            (
                inside,
                int(artifact.result.get("error_headers", 10**9)),
                artifact.label,
                artifact,
                hunks,
            )
        )
    ranked.sort(key=lambda row: (row[0], row[1], row[2]))
    attempts: list[dict] = []
    for inside, total_errors, _, artifact, hunks in ranked:
        try:
            trial, gate = apply_hunks(current, hunks)
        except Exception as exc:
            attempts.append(
                {
                    "artifact": artifact.label,
                    "artifact_id": artifact.artifact_id,
                    "inside_errors": inside,
                    "artifact_error_headers": total_errors,
                    "apply_error": str(exc),
                }
            )
            continue
        result = run_lean(trial, f"{stage}-{artifact.label}", 1)
        attempt = {
            "artifact": artifact.label,
            "artifact_id": artifact.artifact_id,
            "inside_errors": inside,
            "artifact_error_headers": total_errors,
            "gate_line": gate,
            "direct_lean": result,
        }
        attempts.append(attempt)
        if gate_passed(result, gate):
            (OUT / f"{stage}-attempts.json").write_text(
                json.dumps(attempts, indent=2, sort_keys=True) + "\n",
                encoding="utf-8",
            )
            return trial, artifact.label, gate, result
    (OUT / f"{stage}-attempts.json").write_text(
        json.dumps(attempts, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    raise RuntimeError(f"{stage}: no artifact variant advanced the first-error frontier")


def main() -> None:
    OUT.mkdir(parents=True, exist_ok=True)
    FRONTIER.mkdir(parents=True, exist_ok=True)
    if not BASE.is_file():
        raise RuntimeError(f"missing baseline source: {BASE}")
    base_text = BASE.read_text(encoding="utf-8")
    if sha256_text(base_text) != BASE_SHA256:
        raise RuntimeError("immutable C1 baseline SHA256 mismatch")

    artifacts = {
        label: load_artifact(label, artifact_id)
        for label, artifact_id in ARTIFACTS.items()
    }
    c04 = artifacts["C04_mul_inv_using_bang"]
    c04_errors = int(c04.result.get("error_headers", -1))
    if c04_errors != 85:
        raise RuntimeError(f"C04 authority expected 85 errors, got {c04_errors}")
    if sha256_text(c04.source) != c04.result.get("candidate_qym_sha256"):
        raise RuntimeError("C04 authority source/result SHA256 mismatch")
    current = c04.source

    selected: dict[str, object] = {
        "baseline": {
            "label": "C04_mul_inv_using_bang",
            "artifact_id": c04.artifact_id,
            "error_headers": c04_errors,
            "qym_sha256": sha256_text(current),
            "qym_blob": git_blob(current),
        }
    }

    c2_attempts: list[dict] = []
    c2_selected: tuple[str, str, int, dict] | None = None
    for variant, theorem in C2_VARIANTS.items():
        trial, gate = replace_c2(current, theorem)
        result = run_lean(trial, f"C2-{variant}", 1)
        c2_attempts.append(
            {"variant": variant, "gate_line": gate, "direct_lean": result}
        )
        if gate_passed(result, gate):
            c2_selected = (trial, variant, gate, result)
            break
    if c2_selected is None:
        intrinsic = artifacts["C02_intrinsic_mobius"]
        hunks = diff_hunks(base_text, intrinsic.source)
        trial, gate = apply_hunks(current, hunks)
        result = run_lean(trial, "C2-artifact-intrinsic_mobius", 1)
        c2_attempts.append(
            {
                "variant": "artifact_intrinsic_mobius",
                "artifact_id": intrinsic.artifact_id,
                "gate_line": gate,
                "direct_lean": result,
            }
        )
        if gate_passed(result, gate):
            c2_selected = (trial, "artifact_intrinsic_mobius", gate, result)
    (OUT / "C2-attempts.json").write_text(
        json.dumps(c2_attempts, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    if c2_selected is None:
        raise RuntimeError("C2: no candidate advanced the first-error frontier")
    current, variant, gate, result = c2_selected
    selected["C2"] = {
        "variant": variant,
        "gate_line": gate,
        "direct_lean": result,
    }

    current, label, gate, result = choose_artifact_variant(
        "C3",
        base_text,
        current,
        [artifacts["C03_using_bang_explicit_constants"]],
    )
    selected["C3"] = {
        "variant": label,
        "gate_line": gate,
        "direct_lean": result,
    }

    selected["C4"] = {
        "variant": "C04_mul_inv_using_bang",
        "artifact_id": c04.artifact_id,
        "verified_predecessor_error_headers": c04_errors,
    }

    current, label, gate, result = choose_artifact_variant(
        "C5",
        base_text,
        current,
        [
            artifacts["C05_derive_and_normsq"],
            artifacts["C05_derive_and_star"],
            artifacts["C05_coordinate_star"],
        ],
    )
    selected["C5"] = {
        "variant": label,
        "gate_line": gate,
        "direct_lean": result,
    }

    current, label, c6_gate, result = choose_artifact_variant(
        "C6",
        base_text,
        current,
        [
            artifacts["C06_helper_letI"],
            artifacts["C06_inline_letI"],
        ],
    )
    selected["C6"] = {
        "variant": label,
        "gate_line": c6_gate,
        "direct_lean": result,
    }

    forbidden = audit_forbidden(current)
    if any(forbidden.values()):
        raise RuntimeError(f"forbidden token audit failed: {forbidden}")

    full = run_lean(current, "C2-C6-final-full", 10000)
    if int(full["panic_lines"]) != 0:
        raise RuntimeError("final direct Lean emitted panic/internal-error lines")
    first = full["first_error"]
    if first is not None and int(first["line"]) < c6_gate:
        raise RuntimeError(
            f"final first error {first['line']} is still before C6 gate {c6_gate}"
        )
    if int(full["error_headers"]) >= c04_errors:
        raise RuntimeError(
            f"final candidate did not improve 85-error authority: {full['error_headers']}"
        )

    QYM.write_text(current, encoding="utf-8")
    repaired = FRONTIER / "QYM_C2_C6_REPAIRED.lean"
    repaired.write_text(current, encoding="utf-8")
    result_payload = {
        "schema": "qym-c2-c6-serial-repair-v1",
        "run_id": int(os.environ.get("GITHUB_RUN_ID", "0")),
        "trigger_sha": os.environ.get("GITHUB_SHA"),
        "baseline_error_headers": c04_errors,
        "baseline_qym_sha256": c04.result.get("candidate_qym_sha256"),
        "candidate_qym_sha256": sha256_text(current),
        "candidate_qym_blob": git_blob(current),
        "bytes": len(current.encode("utf-8")),
        "lf": current.count("\n"),
        "forbidden": forbidden,
        "c2_c6_gate_line": c6_gate,
        "selected": selected,
        "exit": full["exit"],
        "error_headers": full["error_headers"],
        "warning_headers": full["warning_headers"],
        "panic_lines": full["panic_lines"],
        "first_error": full["first_error"],
        "last_error": full["last_error"],
        "error_codes": full["error_codes"],
        "log_sha256": full["log_sha256"],
        "semantic_pass": full["exit"] == 0 and full["error_headers"] == 0,
        "c2_c6_clean": first is None or int(first["line"]) >= c6_gate,
        "strict_improvement": int(full["error_headers"]) < c04_errors,
    }
    (FRONTIER / "C2_C6_RESULT.json").write_text(
        json.dumps(result_payload, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    shutil.copy2(OUT / "C2-C6-final-full.log", FRONTIER / "C2_C6_FULL.log")
    print(json.dumps(result_payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    try:
        main()
    except Exception as exc:
        OUT.mkdir(parents=True, exist_ok=True)
        (OUT / "FATAL.txt").write_text(f"{type(exc).__name__}: {exc}\n", encoding="utf-8")
        raise
