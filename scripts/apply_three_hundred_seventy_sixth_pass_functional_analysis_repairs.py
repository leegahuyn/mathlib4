from __future__ import annotations

import base64
from hashlib import sha256
from pathlib import Path
import subprocess
import zlib

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
EXPECTED_INPUT_SHA256 = "d2e1b383b9e60fd18607094ce104679cd604e8c90ffc0261d8a877e700b99b8e"
EXPECTED_OUTPUT_SHA256 = "07f6efd3309c3cc23b86adf5811918b752b72c33a3f7a76213ce9beb10796da4"
PATCH_ZLIB_BASE64 = (
    "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"
)


def file_sha256(path: Path) -> str:
    return sha256(path.read_bytes()).hexdigest()


def main() -> int:
    before = file_sha256(TARGET)
    print(f"input_sha256={before}")
    if before == EXPECTED_OUTPUT_SHA256:
        print("[pass376] already applied")
        return 0
    if before != EXPECTED_INPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass376 input sha256: {before}; expected {EXPECTED_INPUT_SHA256}"
        )
    patch = zlib.decompress(base64.b64decode(PATCH_ZLIB_BASE64))
    subprocess.run(
        ["git", "apply", "--whitespace=nowarn", "-"],
        cwd=ROOT,
        input=patch,
        check=True,
    )
    after = file_sha256(TARGET)
    print(f"output_sha256={after}")
    if after != EXPECTED_OUTPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass376 output sha256: {after}; expected {EXPECTED_OUTPUT_SHA256}"
        )
    print("[pass376] FunctionalAnalysis derivative, paired-edge, orientation, and cusp-trace roots repaired")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
