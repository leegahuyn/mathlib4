#!/usr/bin/env python3
"""Apply the first v66 direct fix to the exact v65 all_field_w_primary source.

This pass changes theorem-local elaboration budgets only. It does not alter
imports, declarations, statements, axioms, or executable trust features.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path

SOURCE = Path("PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean")
EXPECTED_INPUT_SHA256 = "71d8eeca6cce4e520754a3e45b43bf3d61a94f4f1bac6f452d0c8ae2c1ee853b"
HEARTBEATS = "5_000_000"
TARGETS = (
    "theorem discriminantHardStageOperator_eq_weightedHard\n",
    "theorem weightedFull_sub_weightedHard_eq_weightedTail\n",
    "theorem norm_discriminantHardStageOperator_sub_graphPotential_le\n",
    "theorem graphPotentialOperator_isCompact_unconditional (n : ℤ) :\n",
)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def main() -> None:
    before = SOURCE.read_bytes()
    before_sha = sha256(before)
    if before_sha != EXPECTED_INPUT_SHA256:
        raise SystemExit(
            f"refusing non-authoritative input: got {before_sha}, "
            f"expected {EXPECTED_INPUT_SHA256}"
        )

    text = before.decode("utf-8")
    operations: list[dict[str, object]] = []
    for target in TARGETS:
        needle = "\n" + target
        replacement = f"\nset_option maxHeartbeats {HEARTBEATS} in\n" + target
        count = text.count(needle)
        if count != 1:
            raise SystemExit(f"expected exactly one target {target.strip()!r}, found {count}")
        text = text.replace(needle, replacement, 1)
        operations.append(
            {
                "target": target.strip(),
                "local_maxHeartbeats": HEARTBEATS,
                "replacement_count": 1,
            }
        )

    after = text.encode("utf-8")
    SOURCE.write_bytes(after)
    evidence = {
        "schema": "fa-v66-local-heartbeat-fix-v1",
        "status": "MATERIALIZED_UNVERIFIED",
        "source": str(SOURCE),
        "input_sha256": before_sha,
        "output_sha256": sha256(after),
        "input_bytes": len(before),
        "output_bytes": len(after),
        "input_lines": len(before.decode("utf-8").splitlines()),
        "output_lines": len(text.splitlines()),
        "operations": operations,
        "trust_tokens_added": {
            "sorry": 0,
            "admit": 0,
            "axiom": 0,
            "unsafe": 0,
            "native_decide": 0,
            "Lean.ofReduceBool": 0,
        },
    }
    out = Path("build-logs/fa-v66-decl4017")
    out.mkdir(parents=True, exist_ok=True)
    (out / "MATERIALIZATION.json").write_text(
        json.dumps(evidence, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    print(json.dumps(evidence, sort_keys=True))


if __name__ == "__main__":
    main()
