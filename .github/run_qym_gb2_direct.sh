#!/usr/bin/env bash
set -euo pipefail

BRANCH="${SOURCE_BRANCH:-gpt/qym-gb5-semantic-round4-matrix-20260820}"
QYM="PrimalitySheafVerification/QYM.lean"
FROZEN=".github/qym-frontier/GB0_TRUE_PASS/QYM_TRUE_PASS.lean"
EVIDENCE=".github/qym-frontier/GB0_TRUE_PASS"
OLEAN=".lake/build/lib/lean/PrimalitySheafVerification"
OUT="${OUT:-/tmp/qym-gb2-master-route}"
EXPECTED_SHA256="ab7c394f68b812046bcfae109b274a2d4fa42479bf8e76461c73a9c190fb3204"
EXPECTED_BLOB="7afb309d7c4da97da7bc6b922931734d72830d41"
EXPECTED_TOOLCHAIN="leanprover/lean4:v4.33.0-rc1"

mkdir -p "$OUT" "$OLEAN" "$EVIDENCE"

record_static_identity() {
  local actual_sha actual_blob
  actual_sha="$(sha256sum "$QYM" | awk '{print $1}')"
  actual_blob="$(git hash-object --no-filters "$QYM")"
  printf '%s\n' "$actual_sha" > "$OUT/source-sha256.txt"
  printf '%s\n' "$actual_blob" > "$OUT/source-blob.txt"
  awk 'END {print NR}' "$QYM" > "$OUT/line-count.txt"
  git rev-parse HEAD > "$OUT/checked-out-commit.txt"
  git branch --show-current > "$OUT/checked-out-branch.txt"
  printf '%s\n' "$EXPECTED_SHA256" > "$OUT/expected-source-sha256.txt"
  printf '%s\n' "$EXPECTED_BLOB" > "$OUT/expected-source-blob.txt"
}

echo "=== QYM GB0 independent canonical replay ==="
test "$(git branch --show-current)" = "$BRANCH"
test "$(tr -d '\r\n' < lean-toolchain)" = "$EXPECTED_TOOLCHAIN"
test -s "$QYM"
test -s "$FROZEN"
cmp -s "$QYM" "$FROZEN"
record_static_identity
test "$(cat "$OUT/source-sha256.txt")" = "$EXPECTED_SHA256"
test "$(cat "$OUT/source-blob.txt")" = "$EXPECTED_BLOB"

python3 - "$QYM" "$OUT" <<'PY'
from pathlib import Path
import json, re, sys

source = Path(sys.argv[1]).read_text(encoding="utf-8")
out_dir = Path(sys.argv[2])
out = []
i = 0
depth = 0
in_string = False
escape = False

while i < len(source):
    if depth:
        if source.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if source.startswith("-/", i):
            depth -= 1
            i += 2
            continue
        i += 1
        continue
    if in_string:
        if escape:
            escape = False
        elif source[i] == "\\":
            escape = True
        elif source[i] == '"':
            in_string = False
        i += 1
        continue
    if source.startswith("/-", i):
        depth = 1
        i += 2
        continue
    if source.startswith("--", i):
        j = source.find("\n", i)
        i = len(source) if j < 0 else j
        continue
    if source[i] == '"':
        in_string = True
        i += 1
        continue
    out.append(source[i])
    i += 1

executable = "".join(out)
audit = {
    "sorry": len(re.findall(r"\bsorry\b", executable)),
    "admit": len(re.findall(r"\badmit\b", executable)),
    "native_decide": len(re.findall(r"\bnative_decide\b", executable)),
    "Lean.ofReduceBool": executable.count("Lean.ofReduceBool"),
    "global_axiom": len(re.findall(r"(?m)^\s*axiom\s+", executable)),
    "unsafe": len(re.findall(r"(?m)^\s*unsafe\s+", executable)),
    "maxHeartbeats_zero": len(
        re.findall(r"set_option\s+maxHeartbeats\s+0\b", executable)
    ),
    "unclosed_block_comment_depth": depth,
    "unterminated_string": int(in_string),
}
audit["forbidden_count"] = sum(
    value
    for key, value in audit.items()
    if key not in {"unclosed_block_comment_depth", "unterminated_string"}
)
audit["parser_clean"] = depth == 0 and not in_string
(out_dir / "REPLAY_FORBIDDEN_AUDIT.json").write_text(
    json.dumps(audit, indent=2, sort_keys=True) + "\n", encoding="utf-8"
)
print(json.dumps(audit, indent=2, sort_keys=True))
if audit["forbidden_count"] != 0 or not audit["parser_clean"]:
    raise SystemExit(1)
PY

curl --retry 5 --retry-all-errors --fail --silent --show-error \
  https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
  -o /tmp/elan-init.sh
sh /tmp/elan-init.sh -y --default-toolchain none > "$OUT/elan-install.log" 2>&1
export PATH="$HOME/.elan/bin:$PATH"
elan toolchain install "$EXPECTED_TOOLCHAIN" > "$OUT/toolchain-install.log" 2>&1
lean --version | tee "$OUT/lean-version.txt"
lake --version | tee "$OUT/lake-version.txt"
lake exe cache get > "$OUT/mathlib-cache.log" 2>&1

dependencies=(
  Mock2
  Mock2_Advanced
  Mock2_FunctionalAnalysis
  Mock2_FunctionalAnalysis_Integrated
)
for module in "${dependencies[@]}"; do
  if [[ ! -s "$OLEAN/$module.olean" || ! -s "$OLEAN/$module.ilean" ]]; then
    max_errors=1
    if [[ "$module" == "Mock2_FunctionalAnalysis" ||
          "$module" == "Mock2_FunctionalAnalysis_Integrated" ]]; then
      max_errors=2000
    fi
    rm -f "$OLEAN/$module.olean" "$OLEAN/$module.ilean"
    lake env lean "-DmaxErrors=$max_errors" -DwarningAsError=false \
      -o "$OLEAN/$module.olean" \
      -i "$OLEAN/$module.ilean" \
      "PrimalitySheafVerification/$module.lean" \
      > "$OUT/$module.log" 2>&1
  fi
  test -s "$OLEAN/$module.olean"
  test -s "$OLEAN/$module.ilean"
done

rm -f "$OLEAN/QYM.olean" "$OLEAN/QYM.ilean" "$OLEAN/QYM.olean.private"
test ! -e "$OLEAN/QYM.olean"
test ! -e "$OLEAN/QYM.ilean"

printf '%q ' lake env lean -DmaxErrors=2000 -DwarningAsError=false \
  -o "$OLEAN/QYM.olean" \
  -i "$OLEAN/QYM.ilean" \
  "$QYM" > "$OUT/REPLAY_COMMAND.txt"
printf '\n' >> "$OUT/REPLAY_COMMAND.txt"

set +e
start_epoch="$(date +%s)"
/usr/bin/time -v -o "$OUT/REPLAY_TIME.txt" \
  lake env lean -DmaxErrors=2000 -DwarningAsError=false \
    -o "$OLEAN/QYM.olean" \
    -i "$OLEAN/QYM.ilean" \
    "$QYM" > "$OUT/REPLAY_FULL.log" 2>&1
lean_rc=$?
end_epoch="$(date +%s)"
set -e

printf '%s\n' "$lean_rc" > "$OUT/exit.txt"
printf '%s\n' "$((end_epoch - start_epoch))" > "$OUT/elapsed-seconds.txt"

# Prove the compiler did not alter or replace the source being replayed.
cmp -s "$QYM" "$FROZEN"
test "$(sha256sum "$QYM" | awk '{print $1}')" = "$EXPECTED_SHA256"
test "$(git hash-object --no-filters "$QYM")" = "$EXPECTED_BLOB"

python3 - "$QYM" "$OLEAN" "$OUT" <<'PY'
from pathlib import Path
import collections
import hashlib
import json
import os
import re
import subprocess
import sys

source = Path(sys.argv[1])
olean_root = Path(sys.argv[2])
out = Path(sys.argv[3])
raw = (out / "REPLAY_FULL.log").read_bytes()
text = raw.decode(errors="replace")
header = re.compile(
    r"^(?P<file>.*?\.lean):(?P<line>\d+):(?P<column>\d+): "
    r"(?P<severity>error|warning)(?:\((?P<code>[^)]*)\))?:\s*"
    r"(?P<message>.*)$",
    re.M,
)
rows = []
for match in header.finditer(text):
    row = match.groupdict()
    row["line"] = int(row["line"])
    row["column"] = int(row["column"])
    rows.append(row)

errors = [row for row in rows if row["severity"] == "error"]
warnings = [row for row in rows if row["severity"] == "warning"]
panic_lines = re.findall(
    r"(?im)^.*(?:internal error|uncaught exception|panic(?:!|:|\s)).*$", text
)
audit = json.loads((out / "REPLAY_FORBIDDEN_AUDIT.json").read_text())
source_raw = source.read_bytes()
source_blob = subprocess.check_output(
    ["git", "hash-object", "--no-filters", str(source)], text=True
).strip()
olean = olean_root / "QYM.olean"
ilean = olean_root / "QYM.ilean"
exit_code = int((out / "exit.txt").read_text().strip())

result = {
    "schema": "qym-gb0-independent-canonical-replay-v1",
    "authority": "actual complete canonical QYM direct Lean replay without source patching",
    "run_id": os.environ.get("GITHUB_RUN_ID"),
    "run_attempt": os.environ.get("GITHUB_RUN_ATTEMPT"),
    "workflow_sha": os.environ.get("GITHUB_SHA"),
    "checked_out_commit": subprocess.check_output(
        ["git", "rev-parse", "HEAD"], text=True
    ).strip(),
    "checked_out_branch": subprocess.check_output(
        ["git", "branch", "--show-current"], text=True
    ).strip(),
    "source_sha256": hashlib.sha256(source_raw).hexdigest(),
    "source_blob": source_blob,
    "line_count": len(source_raw.splitlines()),
    "exit": exit_code,
    "error_headers": len(errors),
    "warning_headers": len(warnings),
    "error_codes": dict(
        sorted(collections.Counter(row["code"] or "uncoded" for row in errors).items())
    ),
    "panic_lines": len(panic_lines),
    "forbidden": audit["forbidden_count"],
    "parser_clean": audit["parser_clean"],
    "first_error": errors[0] if errors else None,
    "last_error": errors[-1] if errors else None,
    "olean_exists": olean.is_file() and olean.stat().st_size > 0,
    "ilean_exists": ilean.is_file() and ilean.stat().st_size > 0,
    "olean_sha256": (
        hashlib.sha256(olean.read_bytes()).hexdigest() if olean.is_file() else None
    ),
    "ilean_sha256": (
        hashlib.sha256(ilean.read_bytes()).hexdigest() if ilean.is_file() else None
    ),
    "log_sha256": hashlib.sha256(raw).hexdigest(),
    "elapsed_seconds": int((out / "elapsed-seconds.txt").read_text().strip()),
    "lean_version": (out / "lean-version.txt").read_text().strip(),
    "lake_version": (out / "lake-version.txt").read_text().strip(),
}
result["pass"] = (
    result["source_sha256"] == os.environ.get(
        "EXPECTED_QYM_SHA256",
        "ab7c394f68b812046bcfae109b274a2d4fa42479bf8e76461c73a9c190fb3204",
    )
    and result["source_blob"] == os.environ.get(
        "EXPECTED_QYM_BLOB", "7afb309d7c4da97da7bc6b922931734d72830d41"
    )
    and result["exit"] == 0
    and result["error_headers"] == 0
    and result["panic_lines"] == 0
    and result["forbidden"] == 0
    and result["parser_clean"]
    and result["olean_exists"]
    and result["ilean_exists"]
)
(out / "REPLAY_RESULT.json").write_text(
    json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8"
)
(out / "error-headers.txt").write_text(
    "".join(
        f"{row['file']}:{row['line']}:{row['column']}: error: {row['message']}\n"
        for row in errors
    ),
    encoding="utf-8",
)
(out / "warning-count.txt").write_text(f"{len(warnings)}\n", encoding="utf-8")
(out / "panic-lines.txt").write_text(
    "".join(line + "\n" for line in panic_lines), encoding="utf-8"
)
print(json.dumps(result, indent=2, sort_keys=True))
PY

python3 - "$OUT/REPLAY_RESULT.json" <<'PY'
import json, sys
result = json.load(open(sys.argv[1], encoding="utf-8"))
if not result.get("pass"):
    raise SystemExit(result.get("exit") or 1)
PY

cp "$OUT/REPLAY_RESULT.json" "$EVIDENCE/REPLAY_RESULT.json"
cp "$OUT/REPLAY_FULL.log" "$EVIDENCE/REPLAY_FULL.log"
cp "$OUT/REPLAY_FORBIDDEN_AUDIT.json" "$EVIDENCE/REPLAY_FORBIDDEN_AUDIT.json"
cp "$OUT/REPLAY_COMMAND.txt" "$EVIDENCE/REPLAY_COMMAND.txt"
cp "$OUT/REPLAY_TIME.txt" "$EVIDENCE/REPLAY_TIME.txt"

git config user.name "github-actions[bot]"
git config user.email "41898282+github-actions[bot]@users.noreply.github.com"
git add "$EVIDENCE/REPLAY_RESULT.json" \
        "$EVIDENCE/REPLAY_FULL.log" \
        "$EVIDENCE/REPLAY_FORBIDDEN_AUDIT.json" \
        "$EVIDENCE/REPLAY_COMMAND.txt" \
        "$EVIDENCE/REPLAY_TIME.txt"
if ! git diff --cached --quiet; then
  git commit -m "QYM: confirm independent canonical GB0 replay ${GITHUB_RUN_ID:-manual} [skip ci]"
  for attempt in 1 2 3 4 5; do
    git fetch origin "$BRANCH"
    if git rebase "origin/$BRANCH" && git push origin "HEAD:$BRANCH"; then
      break
    fi
    git rebase --abort || true
    if [[ "$attempt" -eq 5 ]]; then
      exit 1
    fi
    sleep $((attempt * 5))
  done
fi

echo "QYM TRUE PASS CONFIRMED by independent canonical replay."
