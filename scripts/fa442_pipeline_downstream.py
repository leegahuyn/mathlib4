from __future__ import annotations

import json
import subprocess
from pathlib import Path
from typing import Any

from fa442_pipeline_common import REPO, exact_command, write_json

PSV = REPO / "PrimalitySheafVerification"
OUT = REPO / "build-logs/fa442-pipeline-repair/downstream"


def compile_one(source: Path, label: str) -> dict[str, Any]:
    stem = source.stem
    output_dir = REPO / ".lake/build/lib/lean/PrimalitySheafVerification"
    output_dir.mkdir(parents=True, exist_ok=True)
    olean = output_dir / f"{stem}.olean"
    ilean = output_dir / f"{stem}.ilean"
    olean.unlink(missing_ok=True)
    ilean.unlink(missing_ok=True)
    command = [
        "lake", "env", "lean", "-DwarningAsError=false",
        "-o", str(olean), "-i", str(ilean), str(source.relative_to(REPO)),
    ]
    log_path = OUT / f"{stem}-{label}.log"
    with log_path.open("wb") as log:
        cp = subprocess.run(
            command, cwd=REPO, stdout=log, stderr=subprocess.STDOUT, check=False
        )
    text = log_path.read_text(encoding="utf-8", errors="replace")
    return {
        "source": str(source.relative_to(REPO)),
        "label": label,
        "command": exact_command(command),
        "exit_code": cp.returncode,
        "error_header_count": len([
            line for line in text.splitlines()
            if ".lean:" in line and ": error" in line
        ]),
        "olean_exists": olean.exists() and olean.stat().st_size > 0,
        "ilean_exists": ilean.exists() and ilean.stat().st_size > 0,
        "log": str(log_path.relative_to(OUT)),
    }


def passed(row: dict[str, Any]) -> bool:
    return bool(
        row["exit_code"] == 0 and row["error_header_count"] == 0 and
        row["olean_exists"] and row["ilean_exists"]
    )


def twice(source: Path) -> dict[str, Any]:
    run1 = compile_one(source, "run1")
    run2 = compile_one(source, "run2")
    return {"run1": run1, "run2": run2, "pass_2x": passed(run1) and passed(run2)}


def main() -> None:
    OUT.mkdir(parents=True, exist_ok=True)

    bootstrap_sources = [
        PSV / "Mock2.lean",
        PSV / "Mock2_Advanced.lean",
        PSV / "Mock2_FunctionalAnalysis.lean",
    ]
    bootstrap = [compile_one(source, "dependency-bootstrap") for source in bootstrap_sources]
    if not all(passed(row) for row in bootstrap):
        report = {
            "classification": "INFRA_FAILURE",
            "error": "checked-in completed prerequisites/FA failed dependency bootstrap in downstream job",
            "bootstrap": bootstrap,
            "Integrated": "NOT_RUN_BOOTSTRAP_FAILURE",
            "Mock3_bridges": "NOT_RUN_BOOTSTRAP_FAILURE",
            "QYM": "NOT_RUN_BOOTSTRAP_FAILURE",
        }
        write_json(OUT / "downstream.json", report)
        raise RuntimeError(report["error"])

    integrated_source = PSV / "Mock2_FunctionalAnalysis_Integrated.lean"
    if not integrated_source.exists():
        report = {
            "classification": "INFRA_FAILURE",
            "error": "required Mock2_FunctionalAnalysis_Integrated.lean is missing",
            "bootstrap": bootstrap,
            "Integrated": "MISSING",
            "Mock3_bridges": "NOT_RUN",
            "QYM": "NOT_RUN",
        }
        write_json(OUT / "downstream.json", report)
        raise RuntimeError(report["error"])
    integrated = twice(integrated_source)
    if not integrated["pass_2x"]:
        report = {
            "classification": "LEAN_FAILURE",
            "bootstrap": bootstrap,
            "Integrated": integrated,
            "Mock3_bridges": "NOT_RUN_INTEGRATED_FAILURE",
            "QYM": "NOT_RUN_INTEGRATED_FAILURE",
        }
        write_json(OUT / "downstream.json", report)
        raise RuntimeError("Integrated direct compile did not pass twice")

    bridge_sources = sorted(PSV.glob("Mock3*.lean"))
    bridges = {source.name: twice(source) for source in bridge_sources}
    bridge_ok = all(row["pass_2x"] for row in bridges.values())
    if not bridge_ok:
        report = {
            "classification": "LEAN_FAILURE",
            "bootstrap": bootstrap,
            "Integrated": integrated,
            "Mock3_bridges": bridges,
            "QYM": "NOT_RUN_MOCK3_BRIDGE_FAILURE",
        }
        write_json(OUT / "downstream.json", report)
        raise RuntimeError("one or more Mock3 bridges did not pass twice")

    qym_source = PSV / "QYM.lean"
    if not qym_source.exists():
        report = {
            "classification": "INFRA_FAILURE",
            "bootstrap": bootstrap,
            "Integrated": integrated,
            "Mock3_bridges": bridges if bridges else "NO_BRIDGES_PRESENT",
            "QYM": "MISSING",
        }
        write_json(OUT / "downstream.json", report)
        raise RuntimeError("required QYM.lean is missing")
    qym = twice(qym_source)
    final_ok = qym["pass_2x"]
    report = {
        "classification": "TRUE_PASS" if final_ok else "LEAN_FAILURE",
        "bootstrap": bootstrap,
        "Integrated": integrated,
        "Mock3_bridges": bridges if bridges else "NO_BRIDGES_PRESENT",
        "QYM": qym,
        "all_downstream_2x_pass": final_ok,
    }
    write_json(OUT / "downstream.json", report)
    if final_ok:
        (OUT / "ALL_DOWNSTREAM_2X_PASS").touch()
    else:
        raise RuntimeError("QYM direct compile did not pass twice")
    print(json.dumps(report, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
