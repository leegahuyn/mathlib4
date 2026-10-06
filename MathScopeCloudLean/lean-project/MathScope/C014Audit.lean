import MathScope.Claims.C014
import Lean.Util.CollectAxioms

open Lean

run_cmd do
  let axioms ← Lean.collectAxioms ``MathScope.Claims.C014.c014_slice_radius
  let report :=
    "theorem=MathScope.Claims.C014.c014_slice_radius\n" ++
    "axioms=" ++ String.intercalate "," (axioms.toList.map toString) ++ "\n"
  IO.FS.createDirAll ".mathscope-cloud"
  IO.FS.writeFile ".mathscope-cloud/c014-axioms.txt" report
