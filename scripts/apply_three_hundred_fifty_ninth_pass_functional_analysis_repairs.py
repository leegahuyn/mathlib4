from __future__ import annotations

import base64
from hashlib import sha256
from pathlib import Path
import subprocess
import zlib

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
EXPECTED_INPUT_SHA256 = "8fd20f88c43060d392bab969c91a84b7c0bb08657af7728752a77c5f3c57c6c6"
EXPECTED_OUTPUT_SHA256 = "31f3ecaf1d42e21e630de3f693f35f459500eec4c320771b919414b3de7154b7"
PATCH_ZLIB_BASE64 = "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"


def file_sha256(path: Path) -> str:
    return sha256(path.read_bytes()).hexdigest()


def main() -> int:
    before = file_sha256(TARGET)
    print(f"input_sha256={before}")
    if before == EXPECTED_OUTPUT_SHA256:
        print("[pass359] already applied")
        return 0
    if before != EXPECTED_INPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass359 input sha256: {before}; expected {EXPECTED_INPUT_SHA256}"
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
            f"unexpected pass359 output sha256: {after}; expected {EXPECTED_OUTPUT_SHA256}"
        )
    print("[pass359] FunctionalAnalysis covariance, transport, Green, tile, and density roots repaired")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
