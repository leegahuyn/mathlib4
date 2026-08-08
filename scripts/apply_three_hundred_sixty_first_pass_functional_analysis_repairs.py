from __future__ import annotations

import base64
from hashlib import sha256
from pathlib import Path
import subprocess
import zlib

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
EXPECTED_INPUT_SHA256 = "f694e78260b73e1e6d22ebfd36208d7507791b930b6d69098eeab0f62e206e13"
EXPECTED_OUTPUT_SHA256 = "530704ce43d7fb68a1267f8c8ba37f08aa657b2113491ea908104c62f5f21a1b"
PATCH_ZLIB_BASE64 = (
        "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"
        "b1nQvePiP2FcV7Q="
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
    print("[pass361] FunctionalAnalysis dependent transports and first curved-tile roots repaired")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
