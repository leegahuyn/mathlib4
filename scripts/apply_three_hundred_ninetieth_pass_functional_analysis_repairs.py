from __future__ import annotations

from hashlib import sha256
import os
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
EXPECTED_INPUT_SHA256 = "5f2d7615aaad7bb3a232d19829f0f801278e7ab2fa2f66ccb68408b87647e620"
EXPECTED_DONOR_SHA256 = "07f6efd3309c3cc23b86adf5811918b752b72c33a3f7a76213ce9beb10796da4"
EXPECTED_OUTPUT_SHA256 = "10c95422f6e57fb0ec21f8307f5ca97636997bb111e9347beb7ac5fb58b2d196"

OLD_START = "/-- The Definition 1 Sobolev space: completion of the genuine energy graph. -/"
DONOR_START = "/-- The graph-range subtype inherits the uniform additive group structure"
END_MARKER = "/-- All three completion coordinates jointly remain injective. -/"
OLD_CLOSED_BASE = "abbrev ClosedBaseDomain :=\n  LinearMap.range Q.baseExtension.toLinearMap"
NEW_CLOSED_BASE = "noncomputable def ClosedBaseDomain :=\n  LinearMap.range Q.baseExtension.toLinearMap"


def digest(text: str) -> str:
    return sha256(text.encode("utf-8")).hexdigest()


def main() -> int:
    donor_path = Path(os.environ["PASS376_DONOR"])
    source = TARGET.read_text(encoding="utf-8")
    donor = donor_path.read_text(encoding="utf-8")

    before = digest(source)
    donor_hash = digest(donor)
    print(f"input_sha256={before}")
    print(f"donor_sha256={donor_hash}")

    if before == EXPECTED_OUTPUT_SHA256:
        print("[pass390] already applied")
        return 0
    if before != EXPECTED_INPUT_SHA256:
        raise RuntimeError(f"unexpected PASS390 input: {before}")
    if donor_hash != EXPECTED_DONOR_SHA256:
        raise RuntimeError(f"unexpected PASS376 donor: {donor_hash}")

    source_start = source.index(OLD_START)
    source_end = source.index(END_MARKER, source_start)
    donor_start = donor.index(DONOR_START)
    donor_end = donor.index(END_MARKER, donor_start)

    candidate = source[:source_start] + donor[donor_start:donor_end] + source[source_end:]
    if candidate.count(OLD_CLOSED_BASE) != 1:
        raise RuntimeError("expected exactly one ClosedBaseDomain abbreviation")
    candidate = candidate.replace(OLD_CLOSED_BASE, NEW_CLOSED_BASE, 1)

    after = digest(candidate)
    print(f"output_sha256={after}")
    if after != EXPECTED_OUTPUT_SHA256:
        raise RuntimeError(f"unexpected PASS390 output: {after}")

    TARGET.write_text(candidate, encoding="utf-8")
    print("[pass390] restored PASS376 completion instances, graph extension, and energy proofs")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
