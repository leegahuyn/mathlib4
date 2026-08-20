#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import sys
from pathlib import Path

BASE_SHA256 = "231efe9a0b8f9d05aae5e65ff3904b3636182ef6f1c93c11eac0c05313730998"


def replace_once(text: str, old: str, new: str, label: str) -> str:
    count = text.count(old)
    if count != 1:
        raise SystemExit(f"{label}: expected exactly one match, found {count}")
    return text.replace(old, new, 1)


def main() -> None:
    if len(sys.argv) != 3:
        raise SystemExit("usage: qym_patch_gb5_semantic_round3.py INPUT OUTPUT")

    source = Path(sys.argv[1])
    output = Path(sys.argv[2])
    raw = source.read_bytes()
    actual = hashlib.sha256(raw).hexdigest()
    if actual != BASE_SHA256:
        raise SystemExit(f"wrong QYM 5-error base bytes: {actual}")

    text = raw.decode()

    # The same file already closes an identical real-part-of-inner-self goal
    # with `rw [...]; simp`; use that proven normalization pattern here.
    text = replace_once(
        text,
        "  unfold actualStagePeterssonInner\n"
        "  rw [inner_self_eq_norm_sq_to_K]\n"
        "  rw [← Complex.ofReal_pow, Complex.ofReal_re]\n"
        "  rw [sq_eq_zero_iff, norm_eq_zero]\n",
        "  unfold actualStagePeterssonInner\n"
        "  rw [inner_self_eq_norm_sq_to_K]\n"
        "  simp\n",
        "Petersson real-part definiteness via simp normalization",
    )

    # This exact lemma replacement was the sole successful part of the prior
    # six-error challenger: it eliminated the transported extChart target goal.
    text = replace_once(
        text,
        "  simp only [OpenPartialHomeomorph.extend_target,\n"
        "    PartialEquiv.trans_target,\n"
        "    Homeomorph.toOpenPartialHomeomorph_target,\n"
        "    preimage_univ, inter_univ]\n",
        "  simp only [OpenPartialHomeomorph.extend_target,\n"
        "    OpenPartialHomeomorph.trans_target,\n"
        "    Homeomorph.toOpenPartialHomeomorph_target,\n"
        "    preimage_univ, inter_univ]\n",
        "transported extChart target through open partial homeomorph composition",
    )

    # Preserve the verified five-error add/smul bodies for this monotone round.
    # They will be attacked only after these three independent errors are gone.

    text = replace_once(
        text,
        "  rw [coordinateHamiltonianForm_apply,\n"
        "    inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]\n"
        "  rw [← Complex.ofReal_pow, ← Complex.ofReal_pow,\n"
        "    ← Complex.ofReal_mul, ← Complex.ofReal_add, Complex.ofReal_re]\n",
        "  rw [coordinateHamiltonianForm_apply,\n"
        "    inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]\n"
        "  simp\n",
        "Hamiltonian real-part normalization via simp",
    )

    output.write_text(text)
    digest = hashlib.sha256(output.read_bytes()).hexdigest()
    print(f"candidate_sha256={digest}")


if __name__ == "__main__":
    main()
