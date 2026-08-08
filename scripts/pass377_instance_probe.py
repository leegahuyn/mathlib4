from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
from typing import Callable

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
OUT = Path("/tmp/pass377")
OUT.mkdir(parents=True, exist_ok=True)
BASELINE_SHA256 = "07f6efd3309c3cc23b86adf5811918b752b72c33a3f7a76213ce9beb10796da4"


def sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def proof_headers(text: str) -> list[str]:
    lines = text.splitlines()
    headers: list[str] = []
    decl = re.compile(r"^\s*(?:(?:noncomputable|private|protected)\s+)*(?:theorem|lemma|corollary)\s+")
    i = 0
    while i < len(lines):
        if not decl.match(lines[i]):
            i += 1
            continue
        block = [lines[i]]
        i += 1
        while i < len(lines):
            line = lines[i]
            block.append(line)
            if ":=" in line or re.search(r"\bwhere\s*$", line):
                break
            # A declaration may put a bare `by` on the next line.
            if re.match(r"^\s*by\s*$", line):
                break
            i += 1
        header = "\n".join(block)
        if ":=" in header:
            header = header.split(":=", 1)[0]
        elif re.search(r"\n\s*by\s*$", header):
            header = re.sub(r"\n\s*by\s*$", "", header)
        headers.append(re.sub(r"\s+", " ", header).strip())
        i += 1
    return headers


def compile_source(label: str, source: str) -> dict[str, object]:
    TARGET.write_text(source, encoding="utf-8")
    for suffix in ("olean", "ilean"):
        p = ROOT / ".lake" / "build" / "lib" / "lean" / "PrimalitySheafVerification" / f"Mock2_FunctionalAnalysis.{suffix}"
        p.unlink(missing_ok=True)
    log = OUT / f"{label}.log"
    env = os.environ.copy()
    env["PATH"] = f"{Path.home() / '.elan' / 'bin'}:{env.get('PATH', '')}"
    proc = subprocess.run(
        ["lake", "env", "lean", "-DmaxErrors=25", str(TARGET.relative_to(ROOT))],
        cwd=ROOT,
        env=env,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=900,
        check=False,
    )
    log.write_text(proc.stdout, encoding="utf-8")
    errors = re.findall(r"^.*?\.lean:(\d+):(\d+): error:", proc.stdout, flags=re.M)
    first_line = int(errors[0][0]) if errors else None
    first_col = int(errors[0][1]) if errors else None
    first_message = ""
    if errors:
        m = re.search(r"^.*?\.lean:\d+:\d+: error:\s*(.*)$", proc.stdout, flags=re.M)
        first_message = m.group(1).strip() if m else ""
    return {
        "label": label,
        "returncode": proc.returncode,
        "error_headers": len(errors),
        "first_error_line": first_line,
        "first_error_col": first_col,
        "first_error_message": first_message,
        "source_sha256": sha256_text(source),
        "log": str(log),
    }


def insert_after_proof_start(text: str, error_line: int, additions: list[str]) -> str:
    lines = text.splitlines()
    idx = max(0, min(len(lines) - 1, error_line - 1))
    start = None
    for j in range(idx, max(-1, idx - 260), -1):
        if ":= by" in lines[j] or re.match(r"^\s*by\s*$", lines[j]):
            start = j
            break
    if start is None:
        return text
    indent = "  "
    for j in range(start + 1, min(len(lines), start + 20)):
        if lines[j].strip():
            indent = re.match(r"^\s*", lines[j]).group(0)
            break
    payload = [indent + a for a in additions]
    return "\n".join(lines[: start + 1] + payload + lines[start + 1 :]) + ("\n" if text.endswith("\n") else "")


def remove_local_complex_add(text: str, error_line: int) -> str:
    lines = text.splitlines()
    lo = max(0, error_line - 260)
    hi = min(len(lines), error_line + 40)
    pat = re.compile(r"^\s*letI\s*:\s*AddCommGroup\s+ℂ\s*:=\s*Complex\..*$")
    out: list[str] = []
    for i, line in enumerate(lines):
        if lo <= i < hi and pat.match(line):
            continue
        out.append(line)
    return "\n".join(out) + ("\n" if text.endswith("\n") else "")


def better(candidate: dict[str, object], baseline: dict[str, object]) -> bool:
    if candidate["returncode"] == 0:
        return True
    bline = baseline["first_error_line"]
    cline = candidate["first_error_line"]
    if isinstance(bline, int) and isinstance(cline, int) and cline > bline:
        return True
    if cline == bline and int(candidate["error_headers"]) < int(baseline["error_headers"]):
        return True
    return False


def score(result: dict[str, object]) -> tuple[int, int, int]:
    if result["returncode"] == 0:
        return (2, 10**9, 10**9)
    line = result["first_error_line"] if isinstance(result["first_error_line"], int) else -1
    return (1, line, -int(result["error_headers"]))


def main() -> int:
    original = TARGET.read_text(encoding="utf-8")
    digest = sha256_text(original)
    if digest != BASELINE_SHA256:
        raise SystemExit(f"unexpected PASS 376 source SHA-256: {digest}")
    headers = proof_headers(original)
    baseline = compile_source("baseline", original)
    error_line = baseline["first_error_line"]
    if baseline["returncode"] == 0:
        (OUT / "PASS_ALREADY.txt").write_text(json.dumps(baseline, indent=2), encoding="utf-8")
        TARGET.write_text(original, encoding="utf-8")
        return 0
    if not isinstance(error_line, int):
        raise SystemExit("PASS 376 failed without a parseable Lean error line")

    candidates: dict[str, str] = {}
    candidates["global_canonical_add"] = original.replace(
        "Complex.addCommGroup", "Complex.instNormedAddCommGroup.toAddCommGroup"
    )
    candidates["global_legacy_add"] = original.replace(
        "Complex.instNormedAddCommGroup.toAddCommGroup", "Complex.addCommGroup"
    )
    candidates["local_canonical_add"] = insert_after_proof_start(
        original,
        error_line,
        ["letI : AddCommGroup ℂ := Complex.instNormedAddCommGroup.toAddCommGroup"],
    )
    candidates["local_legacy_add"] = insert_after_proof_start(
        original,
        error_line,
        ["letI : AddCommGroup ℂ := Complex.addCommGroup"],
    )
    candidates["local_canonical_add_module"] = insert_after_proof_start(
        original,
        error_line,
        [
            "letI : AddCommGroup ℂ := Complex.instNormedAddCommGroup.toAddCommGroup",
            "letI : Module ℝ ℂ := Complex.instNormedSpaceReal.toModule",
        ],
    )
    candidates["remove_local_complex_add"] = remove_local_complex_add(original, error_line)

    results: list[dict[str, object]] = [baseline]
    accepted_sources: dict[str, str] = {}
    for label, source in candidates.items():
        if source == original:
            continue
        if proof_headers(source) != headers:
            (OUT / f"{label}.rejected.txt").write_text(
                "public theorem/lemma/corollary header fingerprint changed\n", encoding="utf-8"
            )
            continue
        result = compile_source(label, source)
        results.append(result)
        if better(result, baseline):
            accepted_sources[label] = source
            (OUT / f"{label}.lean").write_text(source, encoding="utf-8")

    best_result = max(results, key=score)
    summary = {
        "baseline_sha256": BASELINE_SHA256,
        "baseline": baseline,
        "results": results,
        "best": best_result,
        "accepted": sorted(accepted_sources),
    }
    (OUT / "summary.json").write_text(json.dumps(summary, indent=2), encoding="utf-8")
    (OUT / "first-error-source-context.txt").write_text(
        "\n".join(
            f"{i + 1}: {line}"
            for i, line in enumerate(original.splitlines())
            if max(1, error_line - 100) <= i + 1 <= error_line + 100
        ),
        encoding="utf-8",
    )

    best_label = str(best_result["label"])
    if best_label in accepted_sources:
        TARGET.write_text(accepted_sources[best_label], encoding="utf-8")
        (OUT / "IMPROVED.txt").write_text(
            f"best={best_label}\nsource_sha256={best_result['source_sha256']}\n",
            encoding="utf-8",
        )
    else:
        TARGET.write_text(original, encoding="utf-8")
        (OUT / "NO_IMPROVEMENT.txt").write_text(
            "No tested instance-normalization candidate advanced the first Lean error.\n",
            encoding="utf-8",
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
