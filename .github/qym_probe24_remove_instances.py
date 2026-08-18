#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import hashlib
import json
import re
import sys

INPUT_SHA256 = "94fceba9313ded915c6e50a17e156699eb48170595b062b1138d04b6abe31534"
EXPECTED = {
    "remove-inner": {
        "sha256": "b8b1aa7fada440df9a94300fb7e5b93fed529cd05ce6538928b2389f52ecc355",
        "blob": "53e529d77bc2feb61dad0e9961f19828b024288c",
    },
    "remove-both": {
        "sha256": "08d91a28ee65ecfb744110a34a43fef655edbf9deed8ac702a8a38a677438380",
        "blob": "b9a4c36a59e4d6553c6103be36a9f90822bad388",
    },
}

COMPLETE = """noncomputable local instance actualFixedPhaseCanonicalCompletion_complete_inst
    (n : ℤ) (Y : ℝ) :
    CompleteSpace (ActualFixedPhaseCuspTraceCompletion n Y) :=
  actualFixedPhaseCuspTraceCompletionCompleteSpace n Y

"""

INNER = """noncomputable local instance actualFixedPhaseCanonicalCompletion_inner_inst
    (n : ℤ) (Y : ℝ) :
    InnerProductSpace ℂ (ActualFixedPhaseCuspTraceCompletion n Y) :=
  actualFixedPhaseCuspTraceCompletionInnerProductSpace n Y

"""


def git_blob(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def main() -> None:
    if len(sys.argv) != 3:
        raise SystemExit("usage: qym_probe24_remove_instances.py VARIANT QYM.lean")
    variant, file_name = sys.argv[1], sys.argv[2]
    if variant not in EXPECTED:
        raise SystemExit(f"unknown variant: {variant}")

    path = Path(file_name)
    raw = path.read_bytes()
    assert hashlib.sha256(raw).hexdigest() == INPUT_SHA256
    text = raw.decode("utf-8")

    assert text.count(INNER) == 1
    text = text.replace(INNER, "", 1)
    if variant == "remove-both":
        assert text.count(COMPLETE) == 1
        text = text.replace(COMPLETE, "", 1)

    path.write_text(text, encoding="utf-8")
    result = path.read_bytes()
    sha256 = hashlib.sha256(result).hexdigest()
    blob = git_blob(result)
    assert sha256 == EXPECTED[variant]["sha256"], (sha256, EXPECTED[variant]["sha256"])
    assert blob == EXPECTED[variant]["blob"], (blob, EXPECTED[variant]["blob"])

    decoded = result.decode("utf-8")
    forbidden = {
        "sorry": len(re.findall(r"\bsorry\b", decoded)),
        "admit": len(re.findall(r"\badmit\b", decoded)),
        "native_decide": len(re.findall(r"\bnative_decide\b", decoded)),
        "Lean.ofReduceBool": decoded.count("Lean.ofReduceBool"),
        "global_axiom": len(re.findall(r"(?m)^\s*axiom\s+", decoded)),
        "unsafe": len(re.findall(r"(?m)^\s*unsafe\s+", decoded)),
        "maxHeartbeats_zero": len(re.findall(r"set_option\s+maxHeartbeats\s+0\b", decoded)),
    }
    assert not any(forbidden.values()), forbidden

    print(json.dumps({
        "schema": "qym-probe24-remove-redundant-instances-v1",
        "variant": variant,
        "input_sha256": INPUT_SHA256,
        "candidate_sha256": sha256,
        "candidate_blob": blob,
        "bytes": len(result),
        "lf": result.count(b"\n"),
        "forbidden": forbidden,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
