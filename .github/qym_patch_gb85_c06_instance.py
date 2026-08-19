#!/usr/bin/env python3
from pathlib import Path
import hashlib
import json
import re
import sys

BASE_SHA256 = "f4c9b27a297be772cde7183526378ad42ae826053f69cf3ce521670da4f06210"
BASE_BLOB = "bd28d0436230a8f0bcb01806dac01787542256b8"
OLD = "variable (hSmooth : SmoothTransitionResidual)"
NEW = "variable [hSmooth : SmoothTransitionResidual]"


def git_blob(data: bytes) -> str:
    return hashlib.sha1(
        b"blob " + str(len(data)).encode() + b"\0" + data
    ).hexdigest()


def audit(text: str) -> dict[str, int]:
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


def main() -> None:
    if len(sys.argv) != 2:
        raise SystemExit("usage: qym_patch_gb85_c06_instance.py QYM.lean")
    path = Path(sys.argv[1])
    before = path.read_bytes()
    if hashlib.sha256(before).hexdigest() != BASE_SHA256:
        raise SystemExit("GB85 SHA256 mismatch")
    if git_blob(before) != BASE_BLOB:
        raise SystemExit("GB85 Git blob mismatch")
    text = before.decode("utf-8")
    before_audit = audit(text)
    if text.count(OLD) != 1:
        raise SystemExit(f"expected one C06 binder, found {text.count(OLD)}")
    text = text.replace(OLD, NEW, 1)
    after_audit = audit(text)
    if after_audit != before_audit:
        raise SystemExit(f"forbidden-token delta: {before_audit} -> {after_audit}")
    path.write_text(text, encoding="utf-8")
    after = path.read_bytes()
    print(json.dumps({
        "schema": "qym-gb85-c06-instance-v1",
        "input_sha256": BASE_SHA256,
        "input_blob": BASE_BLOB,
        "candidate_sha256": hashlib.sha256(after).hexdigest(),
        "candidate_blob": git_blob(after),
        "bytes": len(after),
        "lf": after.count(b"\n"),
        "forbidden": after_audit,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
