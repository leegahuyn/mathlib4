#!/usr/bin/env python3
from __future__ import annotations

import os
from pathlib import Path

import qym_gb10_r2_driver as core

core.BASE = Path(os.environ.get("BASE", "PrimalitySheafVerification/QYM.lean"))
core.PATCH = Path(os.environ.get("PATCH", ".github/qym_patch_gb5_true_pass_round1.py"))
core.QYM = Path(os.environ.get("QYM", "PrimalitySheafVerification/QYM.lean"))
core.OUT = Path(os.environ.get("OUT", "/tmp/qym-gb5-true-pass-r1"))
core.BASE_SHA256 = "231efe9a0b8f9d05aae5e65ff3904b3636182ef6f1c93c11eac0c05313730998"
core.CANDIDATE_SHA256 = "9825139b42b65a3a64ab54f42d125998c08200d33622f9351a5fc6e0418ab7c3"

_original_parse_result = core.parse_result


def parse_result(candidate, log, exit_code, elapsed, audit):
    result = _original_parse_result(candidate, log, exit_code, elapsed, audit)
    result["schema"] = "qym-gb5-true-pass-round1-v1"
    result["base_error_headers"] = 5
    clean = result["panic_lines"] == 0 and result["forbidden_zero"]
    result["semantic_improvement"] = result["error_headers"] < 5 and clean
    result["numeric_global_improvement"] = result["error_headers"] < 5 and clean
    return result


core.parse_result = parse_result


if __name__ == "__main__":
    core.main()
