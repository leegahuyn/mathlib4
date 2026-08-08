from __future__ import annotations

import base64
from hashlib import sha256
from pathlib import Path
import subprocess
import zlib

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
EXPECTED_INPUT_SHA256 = "31f3ecaf1d42e21e630de3f693f35f459500eec4c320771b919414b3de7154b7"
EXPECTED_OUTPUT_SHA256 = "f694e78260b73e1e6d22ebfd36208d7507791b930b6d69098eeab0f62e206e13"
PATCH_ZLIB_BASE64 = (
    "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"
)


def file_sha256(path: Path) -> str:
    return sha256(path.read_bytes()).hexdigest()


def main() -> int:
    before = file_sha256(TARGET)
    print(f"input_sha256={before}")
    if before == EXPECTED_OUTPUT_SHA256:
        print("[pass360] already applied")
        return 0
    if before != EXPECTED_INPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass360 input sha256: {before}; expected {EXPECTED_INPUT_SHA256}"
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
            f"unexpected pass360 output sha256: {after}; expected {EXPECTED_OUTPUT_SHA256}"
        )
    print("[pass360] FunctionalAnalysis covariance, dependent transport, Green, tile, density, and curvilinear roots repaired")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
