from __future__ import annotations

import base64
import bz2
import hashlib
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
PAYLOAD_DIR = ROOT / "scripts" / "fa316_payload"

EXPECTED_INPUT_SHA256 = "36258b062cf8caef1f07cb28111cf0d6293897515b0cc49565f177eb2195de69"
EXPECTED_PATCH_SHA256 = "b767bd8959b9eaabf4a2fa7f85486875964b31f88cd492296dcbf3edbd7a0b72"
EXPECTED_OUTPUT_SHA256 = "ac23d9918a1daf9b534345ec4ef7eb382d081514c52bfb0dceda92d6e3633ade"


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def main() -> int:
    before = TARGET.read_bytes()
    before_sha = sha256_bytes(before)
    if before_sha == EXPECTED_OUTPUT_SHA256:
        print("[fa316] already applied")
        return 0
    if before_sha != EXPECTED_INPUT_SHA256:
        raise RuntimeError(
            f"unexpected FunctionalAnalysis input SHA-256: {before_sha}"
        )

    parts = sorted(PAYLOAD_DIR.glob("part*.b85"))
    if [p.name for p in parts] != [f"part{i:02d}.b85" for i in range(9)]:
        raise RuntimeError(f"unexpected payload part set: {[p.name for p in parts]}")
    encoded = "".join(p.read_text(encoding="ascii").strip() for p in parts)
    patch = bz2.decompress(base64.b85decode(encoded.encode("ascii")))
    patch_sha = sha256_bytes(patch)
    if patch_sha != EXPECTED_PATCH_SHA256:
        raise RuntimeError(f"unexpected FA316 patch SHA-256: {patch_sha}")

    with tempfile.NamedTemporaryFile(prefix="fa316-", suffix=".patch", delete=False) as tmp:
        tmp.write(patch)
        patch_path = Path(tmp.name)
    try:
        subprocess.run(
            ["patch", "--quiet", str(TARGET)],
            stdin=patch_path.open("rb"),
            cwd=ROOT,
            check=True,
        )
    finally:
        patch_path.unlink(missing_ok=True)

    after_sha = sha256_bytes(TARGET.read_bytes())
    if after_sha != EXPECTED_OUTPUT_SHA256:
        raise RuntimeError(f"unexpected FunctionalAnalysis output SHA-256: {after_sha}")
    print(f"[fa316] applied: {before_sha} -> {after_sha}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
