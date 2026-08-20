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
        raise SystemExit("usage: qym_patch_gb5_true_pass_round1.py INPUT OUTPUT")
    source = Path(sys.argv[1])
    output = Path(sys.argv[2])
    raw = source.read_bytes()
    actual = hashlib.sha256(raw).hexdigest()
    if actual != BASE_SHA256:
        raise SystemExit(f"wrong QYM GB5 bytes: {actual}")
    text = raw.decode()

    text = replace_once(
        text,
        "  unfold actualStagePeterssonInner\n"
        "  rw [inner_self_eq_norm_sq_to_K]\n"
        "  rw [← Complex.ofReal_pow, Complex.ofReal_re]\n"
        "  rw [sq_eq_zero_iff, norm_eq_zero]\n",
        "  unfold actualStagePeterssonInner\n"
        "  rw [inner_self_eq_norm_sq_to_K]\n"
        "  simp [pow_two, Complex.mul_re]\n",
        "Petersson self real-part definiteness",
    )

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
        "transported extended-chart target through OPH composition",
    )

    text = replace_once(
        text,
        "    simp [globalStageProjectionRepresentative, hx]\n"
        "    simpa only [Pi.add_apply] using huv\n",
        "    simp [globalStageProjectionRepresentative, hx]\n"
        "    convert huv using 1 <;> rfl\n",
        "projection add hidden-instance conversion",
    )

    text = replace_once(
        text,
        "    simp [globalStageProjectionRepresentative, hx]\n"
        "    simpa only [Pi.smul_apply, smul_eq_mul] using hcu\n",
        "    simp [globalStageProjectionRepresentative, hx]\n"
        "    convert hcu using 1 <;> rfl\n",
        "projection smul hidden-instance conversion",
    )

    text = replace_once(
        text,
        "  rw [coordinateHamiltonianForm_apply,\n"
        "    inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]\n"
        "  rw [← Complex.ofReal_pow, ← Complex.ofReal_pow,\n"
        "    ← Complex.ofReal_mul, ← Complex.ofReal_add, Complex.ofReal_re]\n",
        "  rw [coordinateHamiltonianForm_apply,\n"
        "    inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]\n"
        "  simp [pow_two, Complex.mul_re]\n",
        "Hamiltonian self real-part normalization",
    )

    output.write_text(text)
    digest = hashlib.sha256(output.read_bytes()).hexdigest()
    print(f"candidate_sha256={digest}")


if __name__ == "__main__":
    main()
