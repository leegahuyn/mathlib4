#!/usr/bin/env python3
from __future__ import annotations

import importlib.util
import os
import re
import sys
from pathlib import Path


ROOT = Path.cwd()
BASE = ROOT / "scripts/fa474_prepare_logheight_next.py"
spec = importlib.util.spec_from_file_location("fa474base", BASE)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load {BASE}")
fa474 = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = fa474
spec.loader.exec_module(fa474)

fa466 = fa474.fa466
b = fa474.b
orig_norm_repairs = fa474.norm_repairs


# Direct evidence from run 31398686611 fixes both upstream choices.  FA475
# remains at declaration 2791: no declaration 2792-or-later repair is applied
# until one of these final-normalization candidates closes 2791.
EXACT_FA473_WINNER = "const_add_simp"
EXACT_FA474_WINNER = "explicit_through2791"

ORIGINAL_TAIL = """  rw [hProduct.deriv]
  ring"""


def with_final_tail(tail: str) -> str:
    body = fa474.GAUGE_DERIV_CUMULATIVE
    count = body.count(ORIGINAL_TAIL)
    if count != 1:
        raise RuntimeError(
            f"expected one FA474 derivative tail, found {count}"
        )
    updated = body.replace(ORIGINAL_TAIL, tail, 1)
    if updated == body:
        raise RuntimeError("FA475 final-tail replacement produced no change")
    return updated


VARIANTS = {
    "simp_h_ring": (
        with_final_tail("""  rw [hProduct.deriv]
  simp [h] <;> ring"""),
        "unfold the local h with simp, then close commutative algebra with ring",
    ),
    "simp_h_comm_ring": (
        with_final_tail("""  rw [hProduct.deriv]
  simp [h, mul_comm, mul_left_comm, mul_assoc] <;> ring"""),
        "unfold h and normalize multiplication order before ring",
    ),
    "simp_h_ring_nf": (
        with_final_tail("""  rw [hProduct.deriv]
  simp [h] <;> ring_nf"""),
        "unfold h and use ring_nf for the remaining coerced algebra",
    ),
    "norm_cast_h_ring_nf": (
        with_final_tail("""  rw [hProduct.deriv]
  norm_cast <;> simp [h] <;> ring_nf"""),
        "normalize casts, unfold h, and finish with ring_nf",
    ),
    "norm_num_h_ring_nf": (
        with_final_tail("""  rw [hProduct.deriv]
  norm_num [h] <;> ring_nf"""),
        "normalize numeric coercions while unfolding h, then ring_nf",
    ),
}


def replace_body_once(text: str, name: str, body: str) -> str:
    pattern = re.compile(
        rf"^(?:(?:protected|private|noncomputable)\s+)*"
        rf"(?:theorem|lemma|def|abbrev)\s+{re.escape(name)}(?=[\s(:])",
        re.MULTILINE,
    )
    count = len(pattern.findall(text))
    if count != 1:
        raise RuntimeError(
            f"expected exactly one declaration header for {name}, found {count}"
        )
    replaced = b.replace_body(text, name, body)
    if replaced == text:
        raise RuntimeError(f"body replacement for {name} produced no change")
    return replaced


def _restore_env(name: str, prior: str | None) -> None:
    if prior is None:
        os.environ.pop(name, None)
    else:
        os.environ[name] = prior


def norm_repairs(text: str):
    fa473_winner = os.environ.get("FA473_WINNER")
    if fa473_winner != EXACT_FA473_WINNER:
        raise RuntimeError(
            "FA475 requires the direct-evidence FA473 winner "
            f"{EXACT_FA473_WINNER!r}, got {fa473_winner!r}"
        )
    fa474_winner = os.environ.get("FA474_WINNER")
    if fa474_winner != EXACT_FA474_WINNER:
        raise RuntimeError(
            "FA475 requires the exact run-31398686611 FA474 winner "
            f"{EXACT_FA474_WINNER!r}, got {fa474_winner!r}"
        )
    variant = os.environ.get("FA475_VARIANT")
    if variant not in VARIANTS:
        raise RuntimeError(
            f"unsupported or missing FA475_VARIANT={variant!r}"
        )

    prior_frontier = os.environ.get("FRONTIER_VARIANT")
    prior_next = os.environ.get("NEXT_VARIANT")
    os.environ["FRONTIER_VARIANT"] = fa473_winner
    os.environ["NEXT_VARIANT"] = fa474_winner
    try:
        text, repairs = orig_norm_repairs(text)
    finally:
        _restore_env("FRONTIER_VARIANT", prior_frontier)
        _restore_env("NEXT_VARIANT", prior_next)

    body, strategy = VARIANTS[variant]
    text = replace_body_once(text, "deriv_selectedLogHeightNaturalGauge", body)
    return text, repairs + [
        {
            "declaration": "deriv_selectedLogHeightNaturalGauge",
            "declaration_index": 2791,
            "strategy": strategy,
            "matrix_variant": variant,
        },
        {
            "declaration": "FA475 strict-frontier matrix",
            "strategy": variant,
            "fa473_winner": fa473_winner,
            "fa474_winner": fa474_winner,
            "frontier_declaration_index": 2791,
            "later_repair_count": 0,
            "max_errors": 32,
        },
    ]


fa466.norm_repairs = norm_repairs


if __name__ == "__main__":
    fa466.main()
