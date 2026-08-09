#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${ROOT}"

compile_module() {
  local module="$1"
  local source="PrimalitySheafVerification/${module}.lean"
  local outdir=".lake/build/lib/lean/PrimalitySheafVerification"
  local olean="${outdir}/${module}.olean"
  local ilean="${outdir}/${module}.ilean"
  mkdir -p "${outdir}"
  rm -f "${olean}" "${ilean}"
  echo "[pass389-dependency] compiling ${source}"
  lake env lean -DmaxErrors=100 -o "${olean}" -i "${ilean}" "${source}"
  test -s "${olean}"
  test -s "${ilean}"
  echo "[pass389-dependency] PASS ${module}"
}

compile_module Mock2
compile_module Mock2_Advanced
