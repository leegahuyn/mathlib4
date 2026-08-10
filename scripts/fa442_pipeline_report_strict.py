from pathlib import Path
import json
import os

from fa442_pipeline_common import REPO

root = Path(os.environ.get(
    "REPORT_INPUT_ROOT",
    REPO / "build-logs/fa442-pipeline-repair/final-download",
))
out = REPO / "build-logs/fa442-pipeline-repair/final-report"
report_path = out / "FA_MATRIX_PIPELINE_REPAIR_REPORT.json"
markdown_path = out / "FA_MATRIX_PIPELINE_REPAIR_REPORT.md"
report = json.loads(report_path.read_text(encoding="utf-8"))
selection_paths = list(root.rglob("selection.json"))
verification_paths = list(root.rglob("verification.json"))
selection = json.loads(selection_paths[0].read_text(encoding="utf-8")) if selection_paths else {}
verification = json.loads(verification_paths[0].read_text(encoding="utf-8")) if verification_paths else {}
current_infra = int(selection.get("infra_failure_count", 0))
selector_infra = selection.get("classification") == "INFRA_FAILURE"
verify_infra = verification.get("classification") == "INFRA_FAILURE"
if current_infra or selector_infra or verify_infra:
    previous = report.get("final_classification", "")
    report["pre_strict_final_classification"] = previous
    report["final_classification"] = "INFRA FAILURE"
    report["current_run_infra_failure_count"] = current_infra
    report_path.write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    text = markdown_path.read_text(encoding="utf-8")
    marker = "## Final classification\n\n"
    start = text.find(marker)
    if start >= 0:
        value_start = start + len(marker)
        next_section = text.find("\n\n## ", value_start)
        replacement = "**INFRA FAILURE**"
        if next_section >= 0:
            text = text[:value_start] + replacement + text[next_section:]
        else:
            text = text[:value_start] + replacement + "\n"
        markdown_path.write_text(text, encoding="utf-8")
