from __future__ import annotations

import base64
from hashlib import sha256
from pathlib import Path
import subprocess
import zlib

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
EXPECTED_INPUT_SHA256 = "f694e78260b73e1e6d22ebfd36208d7507791b930b6d69098eeab0f62e206e13"
EXPECTED_OUTPUT_SHA256 = "6a122109186467fe7dc90a595fad3e840b6ea147f2e3e30c15398ba170d5bb2a"
PATCH_ZLIB_BASE64 = (
    "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"
)


def file_sha256(path: Path) -> str:
    return sha256(path.read_bytes()).hexdigest()


def main() -> int:
    before = file_sha256(TARGET)
    print(f"input_sha256={before}")
    if before == EXPECTED_OUTPUT_SHA256:
        print("[pass361] already applied")
        return 0
    if before != EXPECTED_INPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass361 input sha256: {before}; expected {EXPECTED_INPUT_SHA256}"
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
            f"unexpected pass361 output sha256: {after}; expected {EXPECTED_OUTPUT_SHA256}"
        )
    print("[pass361] FunctionalAnalysis dependent transport and first analytic frontier repaired")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
