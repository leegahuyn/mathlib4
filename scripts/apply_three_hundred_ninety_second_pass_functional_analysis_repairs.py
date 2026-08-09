from __future__ import annotations

from hashlib import sha256
import os
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
DONOR = Path(os.environ["PASS376_DONOR"])
EXPECTED_INPUT_SHA256 = "58e503b0d8bc304fda07fc9b4fe3056bf43cd6df089bc8a27ab34712696e64e0"
EXPECTED_DONOR_SHA256 = "07f6efd3309c3cc23b86adf5811918b752b72c33a3f7a76213ce9beb10796da4"
EXPECTED_OUTPUT_SHA256 = "ec0ed028d3d6d45e90e034be9d4686e39a9eb595e57beafd2c6a54fe4c61bcda"
START = "theorem jointExtensions_injective"
END = "/-- The Mobius-composed actual edge has the declared native tangent. -/"


def digest(text: str) -> str:
    return sha256(text.encode("utf-8")).hexdigest()


def main() -> int:
    source = TARGET.read_text(encoding="utf-8")
    donor = DONOR.read_text(encoding="utf-8")
    before = digest(source)
    donor_hash = digest(donor)
    print(f"input_sha256={before}")
    print(f"donor_sha256={donor_hash}")
    if before == EXPECTED_OUTPUT_SHA256:
        print("[pass392] already applied")
        return 0
    if before != EXPECTED_INPUT_SHA256:
        raise RuntimeError(f"unexpected PASS392 input: {before}")
    if donor_hash != EXPECTED_DONOR_SHA256:
        raise RuntimeError(f"unexpected PASS376 donor: {donor_hash}")

    source_start = source.index(START)
    source_end = source.index(END, source_start)
    donor_start = donor.index(START)
    donor_end = donor.index(END, donor_start)
    candidate = source[:source_start] + donor[donor_start:donor_end] + source[source_end:]
    after = digest(candidate)
    print(f"output_sha256={after}")
    if after != EXPECTED_OUTPUT_SHA256:
        raise RuntimeError(f"unexpected PASS392 output: {after}")

    required_names = (
        "jointExtensions_injective",
        "completionEquiv_apply",
        "potentialPreInnerProductCore",
        "graphSobolevCompletionNormedAddCommGroup",
        "hyperbolicDensity_coe",
        "transportSuccessorCoordinates",
        "transportGraphLowerExtension",
        "actualEdgeAmbientParam_hasDerivAt",
    )
    for name in required_names:
        count = candidate.count(name)
        print(f"required_name {name}: {count}")
        if count < 1:
            raise RuntimeError(f"missing required declaration name: {name}")
    if candidate.count("def potentialPreInnerProductCore") != 1:
        raise RuntimeError("PASS392 must contain exactly one potentialPreInnerProductCore")

    TARGET.write_text(candidate, encoding="utf-8")
    print("[pass392] explicit PASS376-compatible completion-to-edge region restored")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
