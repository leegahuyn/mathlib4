#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import sys
from pathlib import Path

BASE_SHA256 = "c604b258541c4ec8477f0e4aa93b7fb9658d5a9f74546e85faa4b2c6add7ace4"
EXPECTED_SHA256 = "8abc23b49c1cabed88fac0a67c3958d4dec7411d9c078ff555e137a1c19560d7"


def replace_once(text: str, old: str, new: str, label: str) -> str:
    count = text.count(old)
    if count != 1:
        raise SystemExit(f"{label}: expected exactly one match, found {count}")
    return text.replace(old, new, 1)


def main() -> None:
    if len(sys.argv) != 3:
        raise SystemExit("usage: qym_patch_gb8_parser_unblock.py INPUT OUTPUT")
    source = Path(sys.argv[1])
    output = Path(sys.argv[2])
    raw = source.read_bytes()
    actual = hashlib.sha256(raw).hexdigest()
    if actual != BASE_SHA256:
        raise SystemExit(f"wrong GB8 bytes: {actual}")
    text = raw.decode()

    duplicates = [
        "/-- The already constructed projection of the quotient total space. -/\n",
        "/-- Every actual quotient fibre is canonically equivalent to `C`. -/\n",
        "/-- Each actual quotient fibre is homeomorphic to the standard complex line,\n",
        "/-- Complex homogeneity of the indicator projection. -/\n",
        "/-! ## 4. The bounded global projection operator -/\n",
    ]
    for marker in duplicates:
        text = replace_once(text, marker + marker, marker, f"deduplicate {marker.strip()}")

    text = replace_once(
        text,
        "/-- The global dominating density has finite nonnegative integral\n"
        "/-- The global dominating density has finite nonnegative integral, exactly\n",
        "/-- The global dominating density has finite nonnegative integral, exactly\n",
        "repair nested global density doc comment",
    )

    text = replace_once(
        text,
        "  have hTotal := totalOfBaseScalar_continuous.comp\n"
        "    (continuous_const.prodMk continuous_id)\n"
        "  change Continuous (fun c : ℂ => totalOfBaseScalar x c) at hTotal\n",
        "  have hTotal : Continuous (fun c : ℂ => totalOfBaseScalar x c) := by\n"
        "    simpa only [Function.comp_apply] using\n"
        "      totalOfBaseScalar_continuous.comp\n"
        "        (continuous_const.prodMk continuous_id)\n",
        "make fixed-fibre reconstruction continuity type explicit",
    )

    output.write_text(text)
    result = hashlib.sha256(output.read_bytes()).hexdigest()
    if result != EXPECTED_SHA256:
        raise SystemExit(f"unexpected candidate bytes: {result}")
    print(f"candidate_sha256={result}")


if __name__ == "__main__":
    main()
