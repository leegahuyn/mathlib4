from __future__ import annotations

from hashlib import sha256
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
EXPECTED_INPUT_SHA256 = "ec0ed028d3d6d45e90e034be9d4686e39a9eb595e57beafd2c6a54fe4c61bcda"
EXPECTED_OUTPUT_SHA256 = "75815d2006a9ef958f6833ac47eec907760b0b16ad6f15e03c21fa6b63285904"
OLD = "open scoped BigOperators Pointwise\n"
NEW = "open scoped BigOperators Pointwise ContDiff ENNReal\n"


def digest(text: str) -> str:
    return sha256(text.encode("utf-8")).hexdigest()


def main() -> int:
    source = TARGET.read_text(encoding="utf-8")
    before = digest(source)
    print(f"input_sha256={before}")
    if before == EXPECTED_OUTPUT_SHA256:
        print("[pass393] already applied")
        return 0
    if before != EXPECTED_INPUT_SHA256:
        raise RuntimeError(f"unexpected PASS393 input: {before}")
    count = source.count(OLD)
    print(f"global_scope_occurrences={count}")
    if count != 1:
        raise RuntimeError(f"expected one global scope line, found {count}")
    candidate = source.replace(OLD, NEW, 1)
    after = digest(candidate)
    print(f"output_sha256={after}")
    if after != EXPECTED_OUTPUT_SHA256:
        raise RuntimeError(f"unexpected PASS393 output: {after}")
    TARGET.write_text(candidate, encoding="utf-8")
    print("[pass393] restored global ContDiff and ENNReal scopes")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
