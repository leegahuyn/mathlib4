#!/usr/bin/env bash
set -euo pipefail

ROOT='PrimalitySheafVerification'
OUTDIR='.lake/build/lib/lean/PrimalitySheafVerification'
LOGDIR="${PRIMALITY_SHEAF_LOGDIR:-/tmp/primality-sheaf-ci}"
mkdir -p "${LOGDIR}/logs" "${LOGDIR}/audit" "${LOGDIR}/artifacts"

primary=(
  Spt1 Spt2 Spt3 Spt4 Spt5 Spt6 Spt7
  Mock1 Mock1_Advanced Mock2 Mock2_Advanced Mock2_FunctionalAnalysis QYM
)
ordered=(
  Spt1 Spt2 Spt3 Spt4 Spt5 Spt6 Spt7
  Mock1 Mock1_Advanced Mock2 Mock2_Advanced Mock2_FunctionalAnalysis
  Mock2_FunctionalAnalysis_Integrated QYM
)
audit_files=(
  Spt1.lean Spt2.lean Spt3.lean Spt4.lean Spt5.lean Spt6.lean Spt7.lean
  Mock1.lean Mock1_Advanced.lean Mock2.lean Mock2_Advanced.lean
  Mock2_FunctionalAnalysis.lean Mock2_FunctionalAnalysis_Integrated.lean
  QYM.lean BuildAll.lean
)

printf '%s\n' \
  "repository=${GITHUB_REPOSITORY:-local}" \
  "source_sha=${GITHUB_SHA:-$(git rev-parse HEAD)}" \
  "lean_toolchain=$(cat lean-toolchain)" \
  "utc_started=$(date -u +%FT%TZ)" \
  | tee "${LOGDIR}/snapshot.txt"

python3 - "${LOGDIR}" "${audit_files[@]}" <<'PY' \
  | tee "${LOGDIR}/audit/forbidden-token-audit.txt"
from pathlib import Path
import re
import sys

logdir = Path(sys.argv[1])
names = sys.argv[2:]
root = Path("PrimalitySheafVerification")


def strip(src: str) -> str:
    out: list[str] = []
    i = 0
    depth = 0
    string = False
    escaped = False
    while i < len(src):
        if depth:
            if src.startswith("/-", i):
                depth += 1
                out.extend("  ")
                i += 2
            elif src.startswith("-/", i):
                depth -= 1
                out.extend("  ")
                i += 2
            else:
                out.append("\n" if src[i] == "\n" else " ")
                i += 1
        elif string:
            char = src[i]
            out.append("\n" if char == "\n" else " ")
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                string = False
            i += 1
        elif src.startswith("/-", i):
            depth = 1
            out.extend("  ")
            i += 2
        elif src.startswith("--", i):
            while i < len(src) and src[i] != "\n":
                out.append(" ")
                i += 1
        elif src[i] == '"':
            string = True
            out.append(" ")
            i += 1
        else:
            out.append(src[i])
            i += 1
    if depth or string:
        raise SystemExit("unterminated comment or string")
    return "".join(out)


patterns = {
    "sorry": r"\bsorry\b",
    "admit": r"\badmit\b",
    "line_start_global_axiom": r"(?m)^\s*axiom\b",
    "unsafe": r"\bunsafe\b",
    "native_decide": r"\bnative_decide\b",
    "Lean.ofReduceBool": r"\bLean\.ofReduceBool\b",
}
bad = False
for name in names:
    path = root / name
    if not path.is_file():
        print(f"[{name}] MISSING")
        bad = True
        continue
    code = strip(path.read_text(encoding="utf-8"))
    print(f"[{name}]")
    for label, pattern in patterns.items():
        matches = list(re.finditer(pattern, code))
        print(f"{label}={len(matches)}")
        if matches:
            bad = True
            for match in matches[:20]:
                line = code.count("\n", 0, match.start()) + 1
                print(f"  line {line}: {match.group(0)!r}")
if bad:
    raise SystemExit(1)
PY

python3 - "${LOGDIR}" <<'PY'
from pathlib import Path
import re
import sys

logdir = Path(sys.argv[1])
source = Path("PrimalitySheafVerification/Spt5.lean").read_text(encoding="utf-8")


def strip(src: str) -> str:
    out: list[str] = []
    i = 0
    depth = 0
    string = False
    escaped = False
    while i < len(src):
        if depth:
            if src.startswith("/-", i):
                depth += 1
                out.extend("  ")
                i += 2
            elif src.startswith("-/", i):
                depth -= 1
                out.extend("  ")
                i += 2
            else:
                out.append("\n" if src[i] == "\n" else " ")
                i += 1
        elif string:
            char = src[i]
            out.append("\n" if char == "\n" else " ")
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                string = False
            i += 1
        elif src.startswith("/-", i):
            depth = 1
            out.extend("  ")
            i += 2
        elif src.startswith("--", i):
            while i < len(src) and src[i] != "\n":
                out.append(" ")
                i += 1
        elif src[i] == '"':
            string = True
            out.append(" ")
            i += 1
        else:
            out.append(src[i])
            i += 1
    if depth or string:
        raise SystemExit("unterminated comment or string")
    return "".join(out)


code = strip(source)
namespace_pattern = re.compile(r"^\s*namespace\s+([A-Za-z_][A-Za-z0-9_'.]*)\s*$")
section_pattern = re.compile(r"^\s*section(?:\s+[A-Za-z_][A-Za-z0-9_']*)?\s*$")
end_pattern = re.compile(r"^\s*end(?:\s+([A-Za-z_][A-Za-z0-9_'.]*))?\s*$")
declaration_pattern = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:noncomputable|private|protected|local)\s+)*"
    r"(theorem|lemma|def|abbrev|opaque|structure|class|inductive)\s+"
    r"([A-Za-z_][A-Za-z0-9_'.]*)"
)

namespaces: list[str] = []
blocks: list[tuple[str, int]] = []
declarations: list[str] = []
for raw_line in code.splitlines():
    line = raw_line.strip()
    match = namespace_pattern.match(line)
    if match:
        parts = match.group(1).split(".")
        namespaces.extend(parts)
        blocks.append(("namespace", len(parts)))
        continue
    if section_pattern.match(line):
        blocks.append(("section", 0))
        continue
    if end_pattern.match(line):
        if blocks:
            kind, width = blocks.pop()
            if kind == "namespace" and width:
                del namespaces[-width:]
        continue
    match = declaration_pattern.match(line)
    if not match:
        continue
    normalized = f" {line} "
    if " private " in normalized or " local " in normalized:
        continue
    name = match.group(2)
    full_name = name if "." in name else ".".join([*namespaces, name])
    if full_name and full_name not in declarations:
        declarations.append(full_name)

if not declarations:
    raise SystemExit("no public Spt5 declarations parsed")
(logdir / "audit" / "Spt5-declarations.txt").write_text(
    "\n".join(declarations) + "\n", encoding="utf-8"
)
audit = Path("/tmp/Spt5WholeFileAxiomAudit.lean")
audit.write_text(
    "import PrimalitySheafVerification.Spt5\n\n"
    + "\n".join(f"#print axioms {name}" for name in declarations)
    + "\n",
    encoding="utf-8",
)
print(f"generated {len(declarations)} Spt5 axiom queries")
PY

echo 'pass,module,exit_code,error_count,warning_count,olean,ilean' \
  > "${LOGDIR}/compile-summary.csv"

compile_module() {
  local pass="$1"
  local module="$2"
  local path="${ROOT}/${module}.lean"
  local log="${LOGDIR}/logs/pass${pass}-${module}.log"
  local code errors warnings
  rm -f "${OUTDIR}/${module}.olean" "${OUTDIR}/${module}.ilean" \
    "${OUTDIR}/${module}.olean.private"
  set +e
  lake env lean "${path}" -o "${OUTDIR}/${module}.olean" \
    -i "${OUTDIR}/${module}.ilean" >"${log}" 2>&1
  code=$?
  set -e
  errors="$(grep -c 'error:' "${log}" || true)"
  warnings="$(grep -c 'warning:' "${log}" || true)"
  printf '%s,%s,%s,%s,%s,%s,%s\n' \
    "${pass}" "${module}" "${code}" "${errors}" "${warnings}" \
    "$(test -s "${OUTDIR}/${module}.olean" && echo yes || echo no)" \
    "$(test -s "${OUTDIR}/${module}.ilean" && echo yes || echo no)" \
    >> "${LOGDIR}/compile-summary.csv"
  if [[ "${code}" -ne 0 ]]; then
    grep -n 'error:' "${log}" | head -30 || true
    grep -n 'error:' "${log}" | tail -10 || true
    tail -300 "${log}" || true
    return "${code}"
  fi
  test "${errors}" -eq 0
  test -s "${OUTDIR}/${module}.olean"
  test -s "${OUTDIR}/${module}.ilean"
  if grep -Eqi \
    "maximum number of errors|missing object file|sorryAx|declaration uses 'sorry'|PANIC|segmentation fault|stack overflow" \
    "${log}"; then
    echo "forbidden compiler diagnostic in ${module}" >&2
    return 90
  fi
}

for pass in 1 2; do
  rm -rf "${OUTDIR}"
  mkdir -p "${OUTDIR}"
  for module in "${ordered[@]}"; do
    compile_module "${pass}" "${module}"
  done
  compile_module "${pass}" BuildAll
  for module in "${primary[@]}" BuildAll; do
    test -s "${OUTDIR}/${module}.olean"
    test -s "${OUTDIR}/${module}.ilean"
  done
  find "${OUTDIR}" -maxdepth 1 -type f \( -name '*.olean' -o -name '*.ilean' \) \
    -printf '%f\n' | sort > "${LOGDIR}/artifacts/pass${pass}-artifact-list.txt"
  sha256sum "${OUTDIR}"/*.olean "${OUTDIR}"/*.ilean \
    > "${LOGDIR}/artifacts/pass${pass}-artifact-sha256.txt"
done

lake env lean /tmp/Spt5WholeFileAxiomAudit.lean \
  > "${LOGDIR}/audit/Spt5-whole-file-axioms.log" 2>&1
if grep -Fq 'sorryAx' "${LOGDIR}/audit/Spt5-whole-file-axioms.log"; then
  echo 'Spt5 whole-file audit contains sorryAx' >&2
  exit 1
fi
python3 - "${LOGDIR}" <<'PY' | tee "${LOGDIR}/audit/Spt5-axiom-summary.txt"
from pathlib import Path
import re
import sys

logdir = Path(sys.argv[1])
log = (logdir / "audit" / "Spt5-whole-file-axioms.log").read_text(
    encoding="utf-8", errors="replace"
)
allowed = {"propext", "Classical.choice", "Quot.sound"}
observed: set[str] = set()
for raw in re.findall(r"depends on axioms:\s*\[([^\]]*)\]", log, re.S):
    observed.update(re.findall(r"[A-Za-z_][A-Za-z0-9_.]*", raw))
forbidden = sorted(observed - allowed)
print("observed_axioms=" + ",".join(sorted(observed)))
print("forbidden_axioms=" + ",".join(forbidden))
if forbidden:
    raise SystemExit(1)
PY

git diff --exit-code
printf '%s\n' \
  "source_sha=${GITHUB_SHA:-$(git rev-parse HEAD)}" \
  "primary_module_count=13" \
  "support_module=Mock2_FunctionalAnalysis_Integrated" \
  "BuildAll=PASS" \
  "clean_rebuild_passes=2" \
  "runtime_source_repairs=0" \
  "utc_finished=$(date -u +%FT%TZ)" \
  | tee "${LOGDIR}/final-status.txt"
