from __future__ import annotations

import hashlib
import json
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PSV = ROOT / "PrimalitySheafVerification"
EVIDENCE = ROOT / "build-logs" / "fa391-final-gate"
FORBIDDEN = {
    "sorry": re.compile(r"\bsorry\b"),
    "admit": re.compile(r"\badmit\b"),
    "global_axiom": re.compile(r"(?m)^\s*(?:public\s+)?axiom\b"),
    "unsafe": re.compile(r"(?m)^\s*unsafe\b"),
    "native_decide": re.compile(r"\bnative_decide\b"),
    "Lean.ofReduceBool": re.compile(r"\bLean\.ofReduceBool\b"),
}


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


def artifacts(path: Path) -> list[Path]:
    stem = path.stem
    return [
        path.with_suffix(".olean"),
        path.with_suffix(".ilean"),
        ROOT
        / ".lake"
        / "build"
        / "lib"
        / "lean"
        / "PrimalitySheafVerification"
        / f"{stem}.olean",
        ROOT
        / ".lake"
        / "build"
        / "lib"
        / "lean"
        / "PrimalitySheafVerification"
        / f"{stem}.ilean",
    ]


def clean_artifacts(path: Path) -> None:
    for candidate in artifacts(path):
        candidate.unlink(missing_ok=True)


def generated(path: Path, extension: str) -> bool:
    return any(candidate.exists() for candidate in artifacts(path) if candidate.suffix == extension)


def compile_one(path: Path, label: str) -> dict[str, object]:
    clean_artifacts(path)
    proc = subprocess.run(
        [
            "lake",
            "env",
            "lean",
            "-DmaxErrors=300",
            str(path.relative_to(ROOT)),
        ],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=3600,
        check=False,
    )
    EVIDENCE.mkdir(parents=True, exist_ok=True)
    log_path = EVIDENCE / f"{label}.log"
    log_path.write_text(proc.stdout, encoding="utf-8")
    error_headers = len(re.findall(r"\.lean:\d+:\d+:\s*error:", proc.stdout))
    result = {
        "module": path.name,
        "label": label,
        "exit_code": proc.returncode,
        "error_headers": error_headers,
        "olean": generated(path, ".olean"),
        "ilean": generated(path, ".ilean"),
        "source_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
        "log": str(log_path.relative_to(ROOT)),
    }
    (EVIDENCE / f"{label}.json").write_text(
        json.dumps(result, indent=2), encoding="utf-8"
    )
    return result


def audit(path: Path) -> dict[str, object]:
    code = strip_comments_and_strings(path.read_text(encoding="utf-8"))
    counts = {name: len(pattern.findall(code)) for name, pattern in FORBIDDEN.items()}
    return {
        "module": path.name,
        "source_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
        "counts": counts,
        "pass": not any(counts.values()),
    }


def passed(result: dict[str, object]) -> bool:
    return (
        result["exit_code"] == 0
        and result["error_headers"] == 0
        and result["olean"]
        and result["ilean"]
    )


def main() -> int:
    EVIDENCE.mkdir(parents=True, exist_ok=True)
    prereqs = [PSV / "Mock2.lean", PSV / "Mock2_Advanced.lean"]
    targets = [
        PSV / "Mock2_FunctionalAnalysis.lean",
        PSV / "Mock2_FunctionalAnalysis_Integrated.lean",
        *sorted(PSV.glob("Mock3*.lean")),
        PSV / "QYM.lean",
    ]
    for path in prereqs + targets:
        if not path.exists():
            raise RuntimeError(f"required source is missing: {path}")

    audit_report = [audit(path) for path in targets]
    (EVIDENCE / "forbidden-token-audit.json").write_text(
        json.dumps(audit_report, indent=2), encoding="utf-8"
    )
    if not all(item["pass"] for item in audit_report):
        (EVIDENCE / "FINAL_STATUS.json").write_text(
            json.dumps(
                {
                    "complete": False,
                    "stage": "forbidden-token-audit",
                    "audit": audit_report,
                },
                indent=2,
            ),
            encoding="utf-8",
        )
        return 3

    results: list[dict[str, object]] = []
    for path in prereqs:
        result = compile_one(path, f"prereq-{path.stem}")
        results.append(result)
        if not passed(result):
            (EVIDENCE / "FINAL_STATUS.json").write_text(
                json.dumps(
                    {
                        "complete": False,
                        "stage": path.name,
                        "kind": "prerequisite",
                        "result": result,
                        "results": results,
                    },
                    indent=2,
                ),
                encoding="utf-8",
            )
            return 4

    for path in targets:
        for run_number in (1, 2):
            result = compile_one(path, f"{path.stem}-run{run_number}")
            results.append(result)
            if not passed(result):
                (EVIDENCE / "FINAL_STATUS.json").write_text(
                    json.dumps(
                        {
                            "complete": False,
                            "stage": path.name,
                            "run": run_number,
                            "result": result,
                            "results": results,
                        },
                        indent=2,
                    ),
                    encoding="utf-8",
                )
                return 2

    marker_lines = [
        "Mock2_FunctionalAnalysis=PASSx2",
        "Mock2_FunctionalAnalysis_Integrated=PASSx2",
        *[f"{path.stem}=PASSx2" for path in sorted(PSV.glob("Mock3*.lean"))],
        "QYM=PASSx2",
    ]
    (EVIDENCE / "ALL_REQUIRED_TARGETS_2X_PASS").write_text(
        "\n".join(marker_lines) + "\n", encoding="utf-8"
    )
    final = {
        "complete": True,
        "stage": "ALL_REQUIRED_TARGETS_2X_PASS",
        "targets": marker_lines,
        "results": results,
        "audit": audit_report,
    }
    (EVIDENCE / "FINAL_STATUS.json").write_text(
        json.dumps(final, indent=2), encoding="utf-8"
    )
    (EVIDENCE / "FINAL_STATUS.txt").write_text(
        "complete=true\nstage=ALL_REQUIRED_TARGETS_2X_PASS\n"
        + "\n".join(marker_lines)
        + "\n",
        encoding="utf-8",
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
