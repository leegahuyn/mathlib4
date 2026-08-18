#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import hashlib
import json
import re
import sys

INPUT_SHA256 = "069c1476163e3b87670e8eae0960f7975691f83a2ac1440863387eb2036cced5"
EXPECTED = {
    "normed-only": {
        "sha256": "502f475e46ff5cea56fef150d2ba4f83f6454f50fc3c72a9e3642c89b381b293",
        "blob": "6dcf0175e1fb4e99bae3c878151ee7310744dbf4",
    },
    "codomain-module-aligned": {
        "sha256": "9073a63a5247b7975162da7e056ad3c86448d8c73c89d12d9a75b37cc3f23a5d",
        "blob": "6fa5687b7434784343a250a4c6c2ea350b179427",
    },
    "domain-codomain-module-aligned": {
        "sha256": "2f59285ad7b3c4a1ea858cdbbcfc80931220b1214787834bf4f79c61185d62b5",
        "blob": "c78d12fe3262516360c46136985f59d488b604e9",
    },
}

ANCHOR = """abbrev ActualFixedPhaseCanonicalTraceClass
    (n : ℤ) (Y : ℝ) :=
  (ActualFixedPhaseCanonicalZeroStoredSubspace n Y)ᗮ
"""

BLOCKS = {
    "normed-only": r'''

/- GPT module-alignment matrix A: capture canonical normed-space objects explicitly. -/
noncomputable def gptCapturedDomainNormedSpace
    (n : ℤ) (Y : ℝ) :
    NormedSpace ℂ (ActualFixedPhaseCuspTraceCompletion n Y) :=
  inferInstance

noncomputable def gptCapturedCodomainNormedSpace
    (n : ℤ) (Y : ℝ) :
    NormedSpace ℂ (ActualFixedPhaseCanonicalTraceClass n Y) :=
  inferInstance

noncomputable local instance (priority := 2000) gptDomainNormedSpaceInst
    (n : ℤ) (Y : ℝ) :
    NormedSpace ℂ (ActualFixedPhaseCuspTraceCompletion n Y) :=
  gptCapturedDomainNormedSpace n Y

noncomputable local instance (priority := 2000) gptCodomainNormedSpaceInst
    (n : ℤ) (Y : ℝ) :
    NormedSpace ℂ (ActualFixedPhaseCanonicalTraceClass n Y) :=
  gptCapturedCodomainNormedSpace n Y
''',
    "codomain-module-aligned": r'''

/- GPT module-alignment matrix B: bind codomain Module and NormedSpace to one captured object. -/
noncomputable def gptCapturedCodomainNormedSpace
    (n : ℤ) (Y : ℝ) :
    NormedSpace ℂ (ActualFixedPhaseCanonicalTraceClass n Y) :=
  inferInstance

noncomputable local instance (priority := 3000) gptCodomainModuleInst
    (n : ℤ) (Y : ℝ) :
    Module ℂ (ActualFixedPhaseCanonicalTraceClass n Y) :=
  (gptCapturedCodomainNormedSpace n Y).toModule

noncomputable local instance (priority := 3000) gptCodomainNormedSpaceInst
    (n : ℤ) (Y : ℝ) :
    NormedSpace ℂ (ActualFixedPhaseCanonicalTraceClass n Y) :=
  gptCapturedCodomainNormedSpace n Y
''',
    "domain-codomain-module-aligned": r'''

/- GPT module-alignment matrix C: bind domain and codomain structures to captured objects. -/
noncomputable def gptCapturedDomainNormedSpace
    (n : ℤ) (Y : ℝ) :
    NormedSpace ℂ (ActualFixedPhaseCuspTraceCompletion n Y) :=
  inferInstance

noncomputable def gptCapturedCodomainNormedSpace
    (n : ℤ) (Y : ℝ) :
    NormedSpace ℂ (ActualFixedPhaseCanonicalTraceClass n Y) :=
  inferInstance

noncomputable local instance (priority := 3000) gptDomainModuleInst
    (n : ℤ) (Y : ℝ) :
    Module ℂ (ActualFixedPhaseCuspTraceCompletion n Y) :=
  (gptCapturedDomainNormedSpace n Y).toModule

noncomputable local instance (priority := 3000) gptDomainNormedSpaceInst
    (n : ℤ) (Y : ℝ) :
    NormedSpace ℂ (ActualFixedPhaseCuspTraceCompletion n Y) :=
  gptCapturedDomainNormedSpace n Y

noncomputable local instance (priority := 3000) gptCodomainModuleInst
    (n : ℤ) (Y : ℝ) :
    Module ℂ (ActualFixedPhaseCanonicalTraceClass n Y) :=
  (gptCapturedCodomainNormedSpace n Y).toModule

noncomputable local instance (priority := 3000) gptCodomainNormedSpaceInst
    (n : ℤ) (Y : ℝ) :
    NormedSpace ℂ (ActualFixedPhaseCanonicalTraceClass n Y) :=
  gptCapturedCodomainNormedSpace n Y
''',
}

COMMON_REPLACEMENTS = [
    (
        "  (ActualFixedPhaseCanonicalTraceClass n Y).orthogonalProjection\n",
        "  (ActualFixedPhaseCanonicalTraceClass n Y).orthogonalProjectionOnto\n",
    ),
    (
        "  exact (ActualFixedPhaseCanonicalTraceClass n Y).orthogonalProjection_mem_subspace_eq_self x\n",
        "  exact (ActualFixedPhaseCanonicalTraceClass n Y).orthogonalProjectionOnto_mem_subspace_eq_self x\n",
    ),
    (
        "  (ActualFixedPhaseCanonicalTraceClass n Y).norm_orthogonalProjection_apply_le x\n",
        "  (ActualFixedPhaseCanonicalTraceClass n Y).norm_orthogonalProjectionOnto_apply_le x\n",
    ),
    (
        """theorem actualFixedPhaseCanonicalTraceClassProjection_opNorm_le
    (n : ℤ) (Y : ℝ) :
    ‖(ActualFixedPhaseCanonicalTraceClass n Y).orthogonalProjectionOnto‖ ≤ 1 :=
  (ActualFixedPhaseCanonicalTraceClass n Y).orthogonalProjectionOnto_norm_le
""",
        """theorem actualFixedPhaseCanonicalTraceClassProjection_opNorm_le
    (n : ℤ) (Y : ℝ) :
    ‖actualFixedPhaseCanonicalTraceClassProjection n Y‖ ≤ 1 :=
  (ActualFixedPhaseCanonicalTraceClass n Y).orthogonalProjectionOnto_norm_le
""",
    ),
    (
        "    ((ActualFixedPhaseCanonicalTraceClass n Y).orthogonalProjection).ker =\n",
        "    ((ActualFixedPhaseCanonicalTraceClass n Y).orthogonalProjectionOnto).ker =\n",
    ),
    (
        "  rw [Submodule.ker_orthogonalProjection]\n",
        "  rw [Submodule.ker_orthogonalProjectionOnto]\n",
    ),
]


def git_blob_sha(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def main() -> None:
    if len(sys.argv) != 3:
        raise SystemExit("usage: qym_module_alignment_matrix.py VARIANT QYM.lean")
    variant = sys.argv[1]
    path = Path(sys.argv[2])
    if variant not in BLOCKS:
        raise SystemExit(f"unknown variant: {variant}")

    raw = path.read_bytes()
    actual_input = hashlib.sha256(raw).hexdigest()
    assert actual_input == INPUT_SHA256, (actual_input, INPUT_SHA256)
    text = raw.decode("utf-8")
    assert text.count(ANCHOR) == 1
    text = text.replace(ANCHOR, ANCHOR + BLOCKS[variant], 1)

    for old, new in COMMON_REPLACEMENTS:
        count = text.count(old)
        assert count == 1, (variant, old[:100], count)
        text = text.replace(old, new, 1)

    path.write_text(text, encoding="utf-8")
    result = path.read_bytes()
    sha256 = hashlib.sha256(result).hexdigest()
    blob = git_blob_sha(result)
    expected = EXPECTED[variant]
    assert sha256 == expected["sha256"], (sha256, expected["sha256"])
    assert blob == expected["blob"], (blob, expected["blob"])

    decoded = result.decode("utf-8")
    forbidden = {
        "sorry": len(re.findall(r"\bsorry\b", decoded)),
        "admit": len(re.findall(r"\badmit\b", decoded)),
        "native_decide": len(re.findall(r"\bnative_decide\b", decoded)),
        "Lean.ofReduceBool": decoded.count("Lean.ofReduceBool"),
        "global_axiom": len(re.findall(r"(?m)^\s*axiom\s+", decoded)),
        "unsafe": len(re.findall(r"(?m)^\s*unsafe\s+", decoded)),
        "maxHeartbeats_zero": len(re.findall(r"set_option\s+maxHeartbeats\s+0\b", decoded)),
    }
    assert not any(forbidden.values()), forbidden
    print(json.dumps({
        "variant": variant,
        "input_sha256": INPUT_SHA256,
        "candidate_sha256": sha256,
        "candidate_blob": blob,
        "bytes": len(result),
        "lf": result.count(b"\n"),
        "forbidden": forbidden,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
