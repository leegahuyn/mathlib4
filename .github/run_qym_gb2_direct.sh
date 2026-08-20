#!/usr/bin/env bash
set -euo pipefail

SOURCE_BRANCH="gpt/qym-gb5-semantic-round4-matrix-20260820"
QYM="PrimalitySheafVerification/QYM.lean"
OLEAN=".lake/build/lib/lean/PrimalitySheafVerification"
OUT="/tmp/qym-gb2-master-route"
BASE_BLOB="ac1b09ba35a642a9d2edfe1037c1a677dc524eeb"
BASE_SHA256="c798cc256e41e19073cc57aef0723e213ef234e353dde65daf47790a91efcd7f"
FA_BLOB="28f614d48e02a0f28d3f5a758e813350b3ea89cf"
INTEGRATED_BLOB="464f5dd095876b20165d12690c8127ef9d909e6a"

rm -rf "$OUT"
mkdir -p "$OUT" "$OLEAN"

{
  echo "event_repository=${GITHUB_REPOSITORY:-unknown}"
  echo "event_ref=${GITHUB_REF:-unknown}"
  echo "source_branch=$SOURCE_BRANCH"
  echo "checked_out_commit=$(git rev-parse HEAD)"
  echo "runner_os=${RUNNER_OS:-unknown}"
  echo "runner_arch=${RUNNER_ARCH:-unknown}"
  date -u +"timestamp_utc=%Y-%m-%dT%H:%M:%SZ"
} | tee "$OUT/environment.txt"

# Fail closed unless the exact verified mathematical authority is checked out.
test "$(tr -d '\r\n' < lean-toolchain)" = "leanprover/lean4:v4.33.0-rc1"
test "$(git hash-object PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean)" = "$FA_BLOB"
test "$(git hash-object PrimalitySheafVerification/Mock2_FunctionalAnalysis_Integrated.lean)" = "$INTEGRATED_BLOB"
test "$(git hash-object "$QYM")" = "$BASE_BLOB"
test "$(sha256sum "$QYM" | awk '{print $1}')" = "$BASE_SHA256"
python3 -m py_compile .github/qym_gb2_true_pass_patch.py

curl --retry 8 --retry-all-errors --fail --silent --show-error \
  https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o /tmp/elan.sh
sh /tmp/elan.sh -y --default-toolchain none > "$OUT/elan.log" 2>&1
export PATH="$HOME/.elan/bin:$PATH"

toolchain="$(tr -d '\r\n' < lean-toolchain)"
ok=0
for attempt in 1 2 3 4 5; do
  if elan toolchain install "$toolchain" >> "$OUT/toolchain.log" 2>&1; then
    ok=1
    break
  fi
  sleep $((attempt * 5))
done
test "$ok" = 1
lean --version | tee "$OUT/lean-version.txt"
lake --version | tee "$OUT/lake-version.txt"

ok=0
for attempt in 1 2 3 4 5; do
  if lake exe cache get >> "$OUT/mathlib-cache.log" 2>&1; then
    ok=1
    break
  fi
  sleep $((attempt * 5))
done
test "$ok" = 1

# Restore misses are repaired by actual direct compilation of the exact checked-in chain.
for source in Mock2 Mock2_Advanced Mock2_FunctionalAnalysis Mock2_FunctionalAnalysis_Integrated; do
  if [[ ! -s "$OLEAN/$source.olean" || ! -s "$OLEAN/$source.ilean" ]]; then
    max_errors=1
    [[ "$source" = Mock2_FunctionalAnalysis* ]] && max_errors=2000
    rm -f "$OLEAN/$source.olean" "$OLEAN/$source.ilean"
    start="$(date +%s)"
    set +e
    lake env lean "-DmaxErrors=$max_errors" -DwarningAsError=false \
      -o "$OLEAN/$source.olean" -i "$OLEAN/$source.ilean" \
      "PrimalitySheafVerification/$source.lean" > "$OUT/$source.log" 2>&1
    dep_exit=$?
    set -e
    elapsed=$(( $(date +%s) - start ))
    printf '%s\n' "$dep_exit" > "$OUT/$source.exit.txt"
    printf '%s\n' "$elapsed" > "$OUT/$source.elapsed-seconds.txt"
    if [[ "$dep_exit" != 0 ]]; then
      echo "dependency compile failed: $source exit=$dep_exit" >&2
      exit "$dep_exit"
    fi
  fi
  test -s "$OLEAN/$source.olean"
  test -s "$OLEAN/$source.ilean"
done

python3 -B .github/qym_gb2_true_pass_patch.py | tee "$OUT/candidate-sha256.txt"
git hash-object "$QYM" | tee "$OUT/candidate-blob.txt"
wc -l "$QYM" | tee "$OUT/candidate-lines.txt"
cp "$QYM" "$OUT/QYM.candidate.lean"

rm -f "$OLEAN/QYM.olean" "$OLEAN/QYM.ilean"
start="$(date +%s)"
set +e
lake env lean -DmaxErrors=2000 -DwarningAsError=false \
  -o "$OLEAN/QYM.olean" -i "$OLEAN/QYM.ilean" "$QYM" \
  > "$OUT/full.log" 2>&1
lean_exit=$?
set -e
elapsed=$(( $(date +%s) - start ))
errors="$(grep -Ec '^PrimalitySheafVerification/QYM\.lean:[0-9]+:[0-9]+: error:' "$OUT/full.log" || true)"
warnings="$(grep -Ec '^PrimalitySheafVerification/QYM\.lean:[0-9]+:[0-9]+: warning:' "$OUT/full.log" || true)"
panic="$(grep -Eic '(^|[^[:alpha:]])panic([^[:alpha:]]|$)' "$OUT/full.log" || true)"
printf '%s\n' "$lean_exit" > "$OUT/exit.txt"
printf '%s\n' "$errors" > "$OUT/error-headers.txt"
printf '%s\n' "$warnings" > "$OUT/warning-headers.txt"
printf '%s\n' "$panic" > "$OUT/panic-lines.txt"
printf '%s\n' "$elapsed" > "$OUT/elapsed-seconds.txt"

export LEAN_EXIT="$lean_exit" ERRORS="$errors" WARNINGS="$warnings" PANIC="$panic"
python3 - <<'PY'
import hashlib
import json
import os
import re
import subprocess
from pathlib import Path

qym = Path("PrimalitySheafVerification/QYM.lean")
out = Path("/tmp/qym-gb2-master-route")
text = qym.read_text(encoding="utf-8")

# Strip nested block comments, line comments, and strings before the escape audit.
cleaned: list[str] = []
i = 0
depth = 0
in_line = False
in_string = False
escape = False
while i < len(text):
    c = text[i]
    n = text[i + 1] if i + 1 < len(text) else ""
    if in_line:
        if c == "\n":
            in_line = False
            cleaned.append("\n")
        else:
            cleaned.append(" ")
        i += 1
        continue
    if depth:
        if c == "/" and n == "-":
            depth += 1
            cleaned.extend("  ")
            i += 2
            continue
        if c == "-" and n == "/":
            depth -= 1
            cleaned.extend("  ")
            i += 2
            continue
        cleaned.append("\n" if c == "\n" else " ")
        i += 1
        continue
    if in_string:
        cleaned.append("\n" if c == "\n" else " ")
        if escape:
            escape = False
        elif c == "\\":
            escape = True
        elif c == '"':
            in_string = False
        i += 1
        continue
    if c == "-" and n == "-":
        in_line = True
        cleaned.extend("  ")
        i += 2
        continue
    if c == "/" and n == "-":
        depth = 1
        cleaned.extend("  ")
        i += 2
        continue
    if c == '"':
        in_string = True
        cleaned.append(" ")
        i += 1
        continue
    cleaned.append(c)
    i += 1

code = "".join(cleaned)
names = ["sorry", "admit", "axiom", "unsafe", "native_decide", "Lean.ofReduceBool"]
counts = {
    name: len(re.findall(r"(?<![A-Za-z0-9_.])" + re.escape(name) + r"(?![A-Za-z0-9_])", code))
    for name in names
}
counts["maxHeartbeats_zero"] = len(re.findall(r"set_option\s+maxHeartbeats\s+0\b", code))
forbidden = sum(counts.values())
audit = {
    "forbidden_zero": forbidden == 0,
    "forbidden_count": forbidden,
    "counts": counts,
    "unclosed_block_comment_depth": depth,
}
(out / "FORBIDDEN_AUDIT.json").write_text(json.dumps(audit, indent=2) + "\n")

log = (out / "full.log").read_text(errors="replace")
error_rows = [
    {"line": int(m.group(1)), "column": int(m.group(2)), "message": m.group(3)}
    for m in re.finditer(
        r"^PrimalitySheafVerification/QYM\.lean:(\d+):(\d+): error: ([^\n]*)",
        log,
        re.M,
    )
]
lean_exit = int(os.environ["LEAN_EXIT"])
errors = int(os.environ["ERRORS"])
panic = int(os.environ["PANIC"])
result = {
    "schema": "qym-gb2-master-route-v1",
    "authority": "actual full-QYM direct Lean",
    "event_commit": os.environ.get("GITHUB_SHA"),
    "checked_out_commit": subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip(),
    "source_path": str(qym),
    "source_sha256": hashlib.sha256(qym.read_bytes()).hexdigest(),
    "source_blob": subprocess.check_output(["git", "hash-object", str(qym)], text=True).strip(),
    "line_count": sum(1 for _ in qym.open(encoding="utf-8")),
    "lean_version": (out / "lean-version.txt").read_text().strip(),
    "lake_version": (out / "lake-version.txt").read_text().strip(),
    "command": "lake env lean -DmaxErrors=2000 -DwarningAsError=false -o <QYM.olean> -i <QYM.ilean> PrimalitySheafVerification/QYM.lean",
    "exit": lean_exit,
    "error_headers": errors,
    "warning_headers": int(os.environ["WARNINGS"]),
    "panic_lines": panic,
    "forbidden": forbidden,
    "first_error": error_rows[0] if error_rows else None,
    "all_error_headers": error_rows,
    "olean_created": Path(".lake/build/lib/lean/PrimalitySheafVerification/QYM.olean").is_file(),
    "ilean_created": Path(".lake/build/lib/lean/PrimalitySheafVerification/QYM.ilean").is_file(),
}
result["pass"] = (
    lean_exit == 0
    and errors == 0
    and panic == 0
    and forbidden == 0
    and result["olean_created"]
    and result["ilean_created"]
)
(out / "RESULT.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
PY

pass="$(python3 -c 'import json; print(str(json.load(open("/tmp/qym-gb2-master-route/RESULT.json"))["pass"]).lower())')"
echo "exit=$lean_exit errors=$errors warnings=$warnings panic=$panic elapsed=$elapsed pass=$pass"

if [[ "$pass" = true ]]; then
  mkdir -p .github/qym-frontier/GB0_TRUE_PASS
  cp "$OUT/RESULT.json" .github/qym-frontier/GB0_TRUE_PASS/RESULT.json
  cp "$OUT/FORBIDDEN_AUDIT.json" .github/qym-frontier/GB0_TRUE_PASS/FORBIDDEN_AUDIT.json
  cp "$OUT/full.log" .github/qym-frontier/GB0_TRUE_PASS/full.log
  cp "$QYM" .github/qym-frontier/GB0_TRUE_PASS/QYM_TRUE_PASS.lean
  git config user.name "github-actions[bot]"
  git config user.email "41898282+github-actions[bot]@users.noreply.github.com"
  git add "$QYM" .github/qym-frontier/GB0_TRUE_PASS
  git commit -m "QYM: actual direct-Lean TRUE PASS ${GITHUB_RUN_ID:-manual} [skip ci]"
  git push origin "HEAD:refs/heads/$SOURCE_BRANCH"
  exit 0
fi

exit 1
