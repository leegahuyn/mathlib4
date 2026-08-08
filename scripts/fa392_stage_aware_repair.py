from __future__ import annotations

import importlib.util
import json
import os
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PSV = ROOT / "PrimalitySheafVerification"
EVIDENCE = ROOT / "build-logs" / "fa392-stage-aware"
PREVIOUS_STATUS = ROOT / "build-logs" / "fa391-final-gate" / "FINAL_STATUS.json"


def import_script(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot import {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


VERIFY = import_script(
    "fa383_stage_verify", ROOT / "scripts" / "fa383_select_and_verify.py"
)
GATE = import_script("fa391_stage_gate", ROOT / "scripts" / "fa391_final_gate.py")


def run(args: list[str], *, timeout: int | None = None):
    return subprocess.run(
        args,
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=timeout,
        check=False,
    )


def previous_status() -> dict:
    if not PREVIOUS_STATUS.exists():
        return {"complete": False, "stage": "Mock2_FunctionalAnalysis.lean"}
    try:
        return json.loads(PREVIOUS_STATUS.read_text(encoding="utf-8"))
    except Exception as exc:
        return {
            "complete": False,
            "stage": "Mock2_FunctionalAnalysis.lean",
            "status_parse_exception": repr(exc),
        }


def prepare_dependencies() -> tuple[bool, str | None]:
    paths = [
        PSV / "Mock2.lean",
        PSV / "Mock2_Advanced.lean",
        PSV / "Mock2_FunctionalAnalysis.lean",
    ]
    EVIDENCE.mkdir(parents=True, exist_ok=True)
    for path in paths:
        metric, log = VERIFY.compile_module(
            path,
            EVIDENCE / "dependency-preparation",
            f"prepare-{path.stem}",
            max_errors=250,
            clean_target=True,
        )
        if metric.exit_code != 0 or metric.errors != 0:
            return False, path.name
    return True, None


def repair_fa() -> dict:
    output = EVIDENCE / "fa-beam"
    output.mkdir(parents=True, exist_ok=True)
    env = os.environ.copy()
    command = [
        sys.executable,
        "scripts/fa389_declaration_beam_solver.py",
        "--output-dir",
        str(output),
        "--max-frontiers",
        os.environ.get("FA392_FA_FRONTIERS", "12"),
        "--beam-size",
        os.environ.get("FA392_FA_BEAM_SIZE", "16"),
        "--query-workers",
        os.environ.get("FA392_FA_QUERY_WORKERS", "8"),
        "--compile-workers",
        os.environ.get("FA392_FA_COMPILE_WORKERS", "2"),
    ]
    proc = subprocess.run(
        command,
        cwd=ROOT,
        env=env,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=20000,
        check=False,
    )
    (output / "driver-console.log").write_text(proc.stdout, encoding="utf-8")
    return {
        "kind": "fa-beam",
        "exit_code": proc.returncode,
        "output": str(output.relative_to(ROOT)),
    }


def stage_to_path(stage: str) -> Path | None:
    if not stage:
        return None
    name = Path(stage).name
    if not name.endswith(".lean"):
        return None
    candidate = PSV / name
    return candidate if candidate.exists() else None


def repair_downstream(path: Path) -> dict:
    ready, failed_dependency = prepare_dependencies()
    if not ready:
        return {
            "kind": "dependency-preparation-failed",
            "failed_dependency": failed_dependency,
        }
    configured = int(os.environ.get("FA392_DOWNSTREAM_FRONTIERS", "32"))
    metric = VERIFY.repair_module(
        path,
        EVIDENCE / path.stem,
        max_frontiers=configured,
    )
    return {
        "kind": "downstream-repair",
        "module": path.name,
        "metric": metric.__dict__,
    }


def run_final_gate() -> tuple[int, dict]:
    GATE.EVIDENCE = EVIDENCE / "final-gate"
    code = GATE.main()
    status_path = GATE.EVIDENCE / "FINAL_STATUS.json"
    status = (
        json.loads(status_path.read_text(encoding="utf-8"))
        if status_path.exists()
        else {"complete": False, "stage": "missing-final-gate-status"}
    )
    return code, status


def main() -> int:
    EVIDENCE.mkdir(parents=True, exist_ok=True)
    before = previous_status()
    stage = str(before.get("stage") or "Mock2_FunctionalAnalysis.lean")
    repair_result: dict

    if bool(before.get("complete")):
        repair_result = {"kind": "previous-gate-complete-no-repair"}
    else:
        path = stage_to_path(stage)
        if path is None or path.name in {
            "Mock2.lean",
            "Mock2_Advanced.lean",
            "Mock2_FunctionalAnalysis.lean",
        }:
            repair_result = repair_fa()
        elif path.name == "Mock2_FunctionalAnalysis_Integrated.lean" or path.name.startswith(
            "Mock3"
        ) or path.name == "QYM.lean":
            repair_result = repair_downstream(path)
        else:
            repair_result = repair_fa()

    gate_code, after = run_final_gate()
    complete = bool(gate_code == 0 and after.get("complete"))
    if complete:
        marker = GATE.EVIDENCE / "ALL_REQUIRED_TARGETS_2X_PASS"
        shutil.copy2(marker, EVIDENCE / "ALL_REQUIRED_TARGETS_2X_PASS")

    status = {
        "previous_status": before,
        "selected_stage": stage,
        "repair_result": repair_result,
        "gate_exit_code": gate_code,
        "final_status": after,
        "complete": complete,
    }
    (EVIDENCE / "AUTHORITATIVE_STATUS.json").write_text(
        json.dumps(status, indent=2), encoding="utf-8"
    )
    lines = [
        f"complete={str(complete).lower()}",
        f"selected_stage={stage}",
        f"repair_kind={repair_result.get('kind')}",
        f"gate_exit_code={gate_code}",
        f"final_stage={after.get('stage')}",
    ]
    if after.get("result"):
        result = after["result"]
        lines.extend(
            [
                f"failing_module={result.get('module')}",
                f"failing_exit_code={result.get('exit_code')}",
                f"failing_error_headers={result.get('error_headers')}",
            ]
        )
    (EVIDENCE / "AUTHORITATIVE_STATUS.txt").write_text(
        "\n".join(lines) + "\n", encoding="utf-8"
    )
    return 0 if complete else 2


if __name__ == "__main__":
    raise SystemExit(main())
