from __future__ import annotations

import base64
import gzip
import hashlib
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
PARTS = ROOT / "scripts" / "pass375c"
EXPECTED_INPUT_SHA256 = "8fd20f88c43060d392bab969c91a84b7c0bb08657af7728752a77c5f3c57c6c6"
EXPECTED_OUTPUT_SHA256 = "d2e1b383b9e60fd18607094ce104679cd604e8c90ffc0261d8a877e700b99b8e"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> int:
    before = sha256(TARGET)
    print(f"input_sha256={before}")
    if before == EXPECTED_OUTPUT_SHA256:
        print("[pass375c] already applied")
        return 0
    if before != EXPECTED_INPUT_SHA256:
        raise RuntimeError(
            f"unexpected input sha256: {before}; expected {EXPECTED_INPUT_SHA256}"
        )
    encoded = "".join(
        path.read_text(encoding="utf-8").strip()
        for path in sorted(PARTS.glob("patch.part*"))
    )
    if not encoded:
        raise RuntimeError("PASS 375 patch chunks are missing")
    patch_bytes = gzip.decompress(base64.b64decode(encoded))
    proc = subprocess.run(
        ["patch", "--batch", "--forward", "-p1"],
        cwd=ROOT,
        input=patch_bytes,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    print(proc.stdout.decode("utf-8", errors="replace"))
    if proc.returncode != 0:
        raise RuntimeError(f"patch failed with exit code {proc.returncode}")
    after = sha256(TARGET)
    print(f"output_sha256={after}")
    if after != EXPECTED_OUTPUT_SHA256:
        raise RuntimeError(
            f"unexpected output sha256: {after}; expected {EXPECTED_OUTPUT_SHA256}"
        )
    print("[pass375c] cumulative PASS358-to-PASS375 candidate applied")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
