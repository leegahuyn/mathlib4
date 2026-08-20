#!/usr/bin/env python3
"""Generate a small exact reproducer for the six residual Mock1_Advanced goals."""
from __future__ import annotations

import argparse
from pathlib import Path

TACTICS = {
    "decide": "by\n  decide",
    "decide-depth": "by\n  set_option maxRecDepth 200000 in\n    decide",
    "rfl": "by\n  rfl",
    "norm-num-range": "by\n  norm_num [List.range_succ, Function.comp_def]",
    "simp-range": "by\n  simp [List.range_succ, Function.comp_def]",
    "simp-norm": "by\n  simp [List.range_succ, Function.comp_def] <;> norm_num",
}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("variant", choices=sorted(TACTICS))
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    tactic = TACTICS[args.variant]

    text = f"""import Mathlib

set_option maxRecDepth 200000

open Function

def coord (dimension index : Nat) (value : Rat) : List Rat :=
  (List.range dimension).map (fun j => if j = index then value else 0)

def signedRow (dimension row : Nat) : List Rat :=
  coord dimension row 1 ++ coord dimension row (-1)

def dotRatProbe (xs ys : List Rat) : Rat :=
  (xs.zip ys).foldl (fun acc p => acc + p.1 * p.2) 0

def matVecProbe (A : List (List Rat)) (x : List Rat) : List Rat :=
  A.map (fun row => dotRatProbe row x)

def pairSolution : List (Rat × Rat) :=
  (List.range 11).map
    (fun i => if i = 0 then ((1 / 2 : Rat), (-1 / 2 : Rat)) else (0, 0))

example :
    coord 11 0 (1 / 2) ++ coord 11 0 (-1 / 2) =
      [1 / 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
       -(1 / 2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := {tactic}

example :
    matVecProbe
        ((List.range 11).map (signedRow 11))
        [1 / 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
         -(1 / 2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] =
      [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := {tactic}

example :
    pairSolution.map (fun pair => pair.1 - pair.2) =
      [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := {tactic}

example :
    pairSolution.map Prod.fst ++ pairSolution.map Prod.snd =
      [1 / 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
       -(1 / 2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := {tactic}

example :
    (pairSolution.map (fun pair => pair.1 ^ 2 + pair.2 ^ 2)).sum =
      (1 / 2 : Rat) := {tactic}

example : (1 : Rat) = 1 * 1 := {tactic}
"""
    args.output.write_text(text, encoding="utf-8")


if __name__ == "__main__":
    main()
