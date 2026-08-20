#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import sys
from pathlib import Path

BASE_SHA256 = "8abc23b49c1cabed88fac0a67c3958d4dec7411d9c078ff555e137a1c19560d7"
EXPECTED_SHA256 = "ad5907140b638416a282bb89b7c61e67dccc9c76dcba1665a89bef8aa27554f4"

OLD = """  have hTotal : Continuous (fun c : ℂ => totalOfBaseScalar x c) := by
    simpa only [Function.comp_apply] using
      totalOfBaseScalar_continuous.comp
        (continuous_const.prodMk continuous_id)
"""

NEW = """  have hTotal : Continuous (fun c : ℂ => totalOfBaseScalar x c) := by
    change Continuous
      ((fun p : InverseEtaBase × ℂ => totalOfBaseScalar p.1 p.2) ∘
        (fun c : ℂ => (x, c)))
    exact totalOfBaseScalar_continuous.comp
      (continuous_const.prodMk continuous_id)
"""


def main() -> None:
    if len(sys.argv) != 3:
        raise SystemExit("usage: qym_patch_gb_parserfixed_hTotal.py INPUT OUTPUT")

    source = Path(sys.argv[1])
    output = Path(sys.argv[2])
    raw = source.read_bytes()
    actual = hashlib.sha256(raw).hexdigest()
    if actual != BASE_SHA256:
        raise SystemExit(f"wrong parser-fixed source bytes: {actual}")

    text = raw.decode()
    count = text.count(OLD)
    if count != 1:
        raise SystemExit(f"hTotal block: expected exactly one match, found {count}")

    output.write_text(text.replace(OLD, NEW, 1))
    result = hashlib.sha256(output.read_bytes()).hexdigest()
    if result != EXPECTED_SHA256:
        raise SystemExit(f"unexpected candidate bytes: {result}")
    print(f"candidate_sha256={result}")


if __name__ == "__main__":
    main()
