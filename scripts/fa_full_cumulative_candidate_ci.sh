#!/usr/bin/env bash
set -euo pipefail

OUT="build-logs/codex-fa-full-cumulative-max2000/candidates/norms"
SOURCE="PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean"

die() {
  printf 'FA full cumulative gate: %s\n' "$*" >&2
  exit 86
}

require_eq() {
  local name="$1" expected="$2" actual
  actual="${!name-}"
  [[ "$actual" == "$expected" ]] ||
    die "$name must equal $(printf '%q' "$expected"), got $(printf '%q' "$actual")"
}

require_sha64() {
  local name="$1" actual
  actual="${!name-}"
  [[ "$actual" =~ ^[0-9a-f]{64}$ ]] || die "$name must be hydrated lowercase SHA256"
  [[ "$actual" != "0000000000000000000000000000000000000000000000000000000000000000" ]] ||
    die "$name must not be the all-zero SHA256 sentinel"
}

require_positive() {
  local name="$1" actual
  actual="${!name-}"
  [[ "$actual" =~ ^[1-9][0-9]*$ ]] || die "$name must be a hydrated positive decimal"
}

require_file_sha() {
  local path="$1" expected="$2"
  [[ -f "$path" ]] || die "missing locked dependency $path"
  local actual
  actual="$(sha256sum "$path" | awk '{print $1}')"
  [[ "$actual" == "$expected" ]] || die "$path SHA drift: $actual; expected $expected"
}

[[ ! -e "$OUT" ]] || die "output directory already exists: $OUT"
mkdir -p "$OUT" .lake/build/lib/lean/PrimalitySheafVerification
: > "$OUT/Mock2_FunctionalAnalysis.log"

require_eq FA_COMPILE_MAX_ERRORS 2000
require_sha64 FA_FULL_EXPECTED_SHA256
require_positive FA_FULL_EXPECTED_BYTES
require_positive FA_FULL_EXPECTED_LINES
require_sha64 FA_FULL_BASE_ATTESTATION_SHA256
require_sha64 FA_FULL_LATE_LIBRARY_SHA256
require_sha64 FA_FULL_SUPPLEMENTAL_INDEX_SHA256
require_sha64 FA_FULL_PREPARER_SHA256
require_sha64 FA_FULL_COLLECTOR_WRAPPER_SHA256
require_sha64 FA_FULL_RUNNER_SHA256
require_eq FA_FULL_BASE_ATTESTATION_PATH /tmp/fa-full-base-artifact-attestation.json
require_eq FA_FULL_INVENTORY_PATH /tmp/fa-full-replayed/fa_full_compile_error_inventory.json
[[ -f "$FA_FULL_BASE_ATTESTATION_PATH" ]] || die "base artifact attestation is missing"
[[ -f "${FA_FULL_BASE_SOURCE_PATH-}" ]] || die "attested d0a3 source is missing"
[[ -f "$FA_FULL_INVENTORY_PATH" ]] || die "replayed full inventory is missing"

require_file_sha scripts/fa_full_cumulative_prepare.py "$FA_FULL_PREPARER_SHA256"
require_file_sha scripts/fa_full_cumulative_candidate_ci.sh "$FA_FULL_RUNNER_SHA256"
require_file_sha scripts/fa_full_cumulative_collect_full_diagnostics.py \
  "$FA_FULL_COLLECTOR_WRAPPER_SHA256"
require_file_sha scripts/fa506r2_collect_full_diagnostics.py \
  e6e065fedb359ee7a1fa329d5633ce9ea2d05bf8a20ac2e58f9e37ea96ee81a6
require_file_sha scripts/fa_full_compile_inventory.py \
  4804d0d73a01ca1600080f892bbd391bffd092b5a2b529ac302e06fd82079a76
require_file_sha "$FA_FULL_INVENTORY_PATH" \
  3692fd155f6029ad30678668ff83fd5f092facebd9e35829cd680b1644d59648
require_file_sha scripts/fa_full_compile_combined_known_overrides.json \
  c503ca6383d74537a058280410a013d77691b0812e57be360afd38ea20fb8da0
require_file_sha scripts/fa_d0a3_idx2974_3002_full_inventory_gated_overrides.json \
  3b22e7cff8ba4c502852b17f074bb22a431b17e4b93fd8b8af6f6a5da4a61243
require_file_sha scripts/fa_full_compile_global_core_instance_environment_override.json \
  4c90fa27cfa482dfc9ffc9588a4d3742ccc32b77519f0510715feeb2b94d6e23
require_file_sha scripts/fa_full_compile_finrank_real_complex_overrides.json \
  847133cc01d9d6551f289a80f107821aba3072e2488468ce231002496c8be3e0
require_file_sha scripts/fa_full_cumulative_standard_library_index.json \
  "$FA_FULL_SUPPLEMENTAL_INDEX_SHA256"
require_file_sha scripts/fa_d0a3_r013_r014_late_root_library.json \
  "$FA_FULL_LATE_LIBRARY_SHA256"

set +e
python3 scripts/fa_full_cumulative_prepare.py \
  --base-source "$FA_FULL_BASE_SOURCE_PATH" \
  --inventory "$FA_FULL_INVENTORY_PATH" \
  --target "$SOURCE" \
  --audit-out "$OUT/PREPARATION.json" \
  > "$OUT/prepare.log" 2>&1
prepare_exit=$?
set -e
printf '%s\n' "$prepare_exit" > "$OUT/prepare.exit"
cat "$OUT/prepare.log"
[[ "$prepare_exit" -eq 0 ]] || die "candidate preparation failed with $prepare_exit"
cp "$SOURCE" "$OUT/Mock2_FunctionalAnalysis-candidate.lean"

set +e
curl --retry 5 --retry-all-errors --fail --silent --show-error \
  https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
  -o /tmp/fa-full-elan-init.sh \
  > "$OUT/elan-download.log" 2>&1
elan_download_exit=$?
set -e
printf '%s\n' "$elan_download_exit" > "$OUT/elan-download.exit"
[[ "$elan_download_exit" -eq 0 ]] || die "elan download failed"

set +e
sh /tmp/fa-full-elan-init.sh -y --default-toolchain none \
  > "$OUT/elan-init.log" 2>&1
elan_init_exit=$?
set -e
printf '%s\n' "$elan_init_exit" > "$OUT/elan-init.exit"
[[ "$elan_init_exit" -eq 0 ]] || die "elan initialization failed"

export PATH="${HOME}/.elan/bin:${PATH}"
toolchain="$(tr -d '\r\n' < lean-toolchain)"
[[ -n "$toolchain" ]] || die "lean-toolchain is empty"
set +e
elan toolchain install "$toolchain" > "$OUT/toolchain-install.log" 2>&1
toolchain_exit=$?
set -e
printf '%s\n' "$toolchain_exit" > "$OUT/toolchain-install.exit"
[[ "$toolchain_exit" -eq 0 ]] || die "toolchain installation failed"

lean --version > "$OUT/lean-version.txt" 2>&1
lake --version > "$OUT/lake-version.txt" 2>&1
set +e
lake exe cache get > "$OUT/cache-get.log" 2>&1
cache_exit=$?
set -e
printf '%s\n' "$cache_exit" > "$OUT/cache-get.exit"
[[ "$cache_exit" -eq 0 ]] || die "lake cache retrieval failed"

compile_one() {
  local stem="$1" cap="$2"
  local src="PrimalitySheafVerification/${stem}.lean"
  local olean=".lake/build/lib/lean/PrimalitySheafVerification/${stem}.olean"
  local ilean=".lake/build/lib/lean/PrimalitySheafVerification/${stem}.ilean"
  local -a command=(
    lake env lean "-DmaxErrors=${cap}" -DwarningAsError=false
    -o "$olean" -i "$ilean" "$src"
  )
  rm -f -- "$olean" "$ilean"
  printf '%q ' "${command[@]}" > "$OUT/${stem}.command"
  printf '\n' >> "$OUT/${stem}.command"
  : > "$OUT/${stem}.executed"
  set +e
  "${command[@]}" > "$OUT/${stem}.log" 2>&1
  local result=$?
  set -e
  printf '%s\n' "$result" > "$OUT/${stem}.exit"
}

# Required execution order: Mock2, Mock2_Advanced, then the authoritative FA file.
compile_one Mock2 3
compile_one Mock2_Advanced 3
compile_one Mock2_FunctionalAnalysis 2000

export FA_FULL_OUT="$OUT"
python3 - <<'PY'
from pathlib import Path
from bisect import bisect_right
import hashlib
import json
import os
import re

root = Path(os.environ["FA_FULL_OUT"])
source_path = Path("PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean")
source_bytes = source_path.read_bytes()
source = source_bytes.decode("utf-8")
prep = json.loads((root / "PREPARATION.json").read_text())

decl_re = re.compile(
    r"(?m)^(?:protected\s+|private\s+|noncomputable\s+)?"
    r"(?:theorem|lemma|def|abbrev|instance|structure|class)\s+"
    r"(?P<name>[^\s(:]+)"
)
diagnostic_re = re.compile(
    r"^(?P<file>.+?\.lean):(?P<line>[0-9]+):(?P<col>[0-9]+): "
    r"error(?:\((?P<code>[^)\r\n]+)\))?:(?P<message>.*)$"
)
decls = list(decl_re.finditer(source))
starts = [source.count("\n", 0, match.start()) + 1 for match in decls]
errors = []
for line in (root / "Mock2_FunctionalAnalysis.log").read_text(
    encoding="utf-8", errors="replace"
).splitlines():
    match = diagnostic_re.match(line)
    if match:
        source_line = int(match.group("line"))
        position = bisect_right(starts, source_line) - 1
        errors.append(
            {
                "line": source_line,
                "col": int(match.group("col")),
                "diagnostic_code": match.group("code"),
                "message": match.group("message").lstrip(),
                "declaration": decls[position].group("name") if position >= 0 else None,
                "declaration_index": position if position >= 0 else None,
                "declaration_start_line": starts[position] if position >= 0 else None,
            }
        )

def read_exit(stem):
    return int((root / f"{stem}.exit").read_text().strip())

m2 = read_exit("Mock2")
m2a = read_exit("Mock2_Advanced")
fa = read_exit("Mock2_FunctionalAnalysis")
infra = []
if m2 != 0:
    infra.append(f"Mock2_exit={m2}")
if m2a != 0:
    infra.append(f"Mock2_Advanced_exit={m2a}")
classification = "INFRA_FAILURE" if infra else ("DIRECT_PASS" if fa == 0 else "LEAN_FAILURE")
first = errors[0] if errors else {}
metric = {
    "schema": "fa-full-cumulative-direct-metric-v1",
    "classification": classification,
    "authority": "direct Lean CLI on the statically materialized cumulative source",
    "source_path": str(source_path),
    "source_sha256": hashlib.sha256(source_bytes).hexdigest(),
    "source_bytes": len(source_bytes),
    "line_count": len(source.splitlines()),
    "declaration_count": len(decls),
    "declaration_sequence_sha256": hashlib.sha256(
        "\n".join(match.group("name") for match in decls).encode()
    ).hexdigest(),
    "source_metadata_identity": (
        hashlib.sha256(source_bytes).hexdigest() == os.environ["FA_FULL_EXPECTED_SHA256"]
        and len(source_bytes) == int(os.environ["FA_FULL_EXPECTED_BYTES"])
        and len(source.splitlines()) == int(os.environ["FA_FULL_EXPECTED_LINES"])
    ),
    "Mock2_executed": (root / "Mock2.executed").is_file(),
    "Mock2_exit": m2,
    "Mock2_Advanced_executed": (root / "Mock2_Advanced.executed").is_file(),
    "Mock2_Advanced_exit": m2a,
    "FA_executed": (root / "Mock2_FunctionalAnalysis.executed").is_file(),
    "FA_exit": fa,
    "all_required_lean_executed": all(
        (root / f"{stem}.executed").is_file()
        for stem in ("Mock2", "Mock2_Advanced", "Mock2_FunctionalAnalysis")
    ),
    "FA_error_headers_captured": len(errors),
    "FA_first_actual_error_line": first.get("line"),
    "FA_first_actual_error_col": first.get("col"),
    "FA_first_error_message": first.get("message"),
    "FA_first_error_declaration": first.get("declaration"),
    "FA_error_declaration_index": first.get("declaration_index"),
    "FA_error_declaration_start_line": first.get("declaration_start_line"),
    "exact_compile_commands": {
        stem: (root / f"{stem}.command").read_text().strip()
        for stem in ("Mock2", "Mock2_Advanced", "Mock2_FunctionalAnalysis")
    },
    "maxErrors_cap": 2000,
    "maxErrors_interpretation": "diagnostic cap only; not total errors or proof-progress evidence",
    "lean_version": (root / "lean-version.txt").read_text(errors="replace").strip(),
    "lake_version": (root / "lake-version.txt").read_text(errors="replace").strip(),
    "lean_toolchain": Path("lean-toolchain").read_text().strip(),
    "toolchain_install_exit": int((root / "toolchain-install.exit").read_text()),
    "cache_get_exit": int((root / "cache-get.exit").read_text()),
    "candidate_forbidden_counts": prep["executable_forbidden_counts_after"],
    "forbidden_clean": prep["executable_forbidden_six_zero"],
    "preparation_sha256": hashlib.sha256((root / "PREPARATION.json").read_bytes()).hexdigest(),
    "libraries": prep["libraries"],
    "infra_reasons": infra,
}
(root / "METRIC.json").write_text(
    json.dumps(metric, indent=2, sort_keys=True) + "\n", encoding="utf-8"
)
PY

set +e
python3 scripts/fa_full_cumulative_collect_full_diagnostics.py \
  --source "$SOURCE" \
  --log "$OUT/Mock2_FunctionalAnalysis.log" \
  --metric "$OUT/METRIC.json" \
  --command "$OUT/Mock2_FunctionalAnalysis.command" \
  --executed "$OUT/Mock2_FunctionalAnalysis.executed" \
  --output "$OUT/FULL_DIAGNOSTICS.json" \
  > "$OUT/collector-console.log" 2>&1
collector_exit=$?
set -e
printf '%s\n' "$collector_exit" > "$OUT/collector.exit"
cat "$OUT/collector-console.log"
[[ "$collector_exit" -eq 0 ]] || die "corrected full diagnostic collector failed"

fa_exit="$(tr -d '\r\n' < "$OUT/Mock2_FunctionalAnalysis.exit")"
[[ "$fa_exit" =~ ^[0-9]+$ ]] || die "FA exit record is invalid"
exit "$fa_exit"
