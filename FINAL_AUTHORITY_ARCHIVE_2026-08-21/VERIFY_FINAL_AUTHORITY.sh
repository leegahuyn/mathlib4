#!/usr/bin/env bash
set -euo pipefail

AUTHORITY_COMMIT="61a48f07e42bc5bf1610a8df3e7cf5ec7e1461c3"
TAG="formalization-final-2026-08-21"
EVIDENCE_SHA256="86b2525c7533562b929a573eca0ff006c6b1df1ac054329c906eae009e05954a"
MANIFEST_SHA256="672474eb93bc14c66cd1ff45203c451987fe525f7b5d13ecd83140be46434b26"
TOOLCHAIN="leanprover/lean4:v4.33.0-rc1"
PACKAGE_DIR="$(CDPATH= cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
REPO_DIR="${1:-${REPO_DIR:-$PWD}}"

die() { printf 'VERIFY_FINAL_AUTHORITY: FAIL: %s\n' "$*" >&2; exit 1; }
command -v python3 >/dev/null 2>&1 || die "python3 is required"
command -v git >/dev/null 2>&1 || die "git is required"

python3 - "$PACKAGE_DIR" <<'PY'
import hashlib, pathlib, sys
root = pathlib.Path(sys.argv[1])
sums = root / "SHA256SUMS.txt"
if not sums.is_file():
    raise SystemExit("missing SHA256SUMS.txt")
for line in sums.read_text(encoding="utf-8").splitlines():
    if not line.strip():
        continue
    expected, name = line.split(None, 1)
    name = name.lstrip(" *")
    path = root / name
    if not path.is_file():
        raise SystemExit(f"missing package file: {name}")
    h = hashlib.sha256(path.read_bytes()).hexdigest()
    if h != expected:
        raise SystemExit(f"SHA256 mismatch for {name}: {h} != {expected}")
print("package SHA256SUMS: PASS")
PY

tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
python3 - "$PACKAGE_DIR/final-authority-last-mile-32438949135-attempt1.zip" "$tmp" "$PACKAGE_DIR/FINAL_AUTHORITY_RECORD.json" <<'PY'
import hashlib, json, pathlib, sys, zipfile
evidence = pathlib.Path(sys.argv[1])
out = pathlib.Path(sys.argv[2])
record = json.loads(pathlib.Path(sys.argv[3]).read_text(encoding="utf-8"))
expected_zip = "86b2525c7533562b929a573eca0ff006c6b1df1ac054329c906eae009e05954a"
if hashlib.sha256(evidence.read_bytes()).hexdigest() != expected_zip:
    raise SystemExit("original evidence ZIP SHA256 mismatch")
with zipfile.ZipFile(evidence) as z:
    base = out.resolve()
    for info in z.infolist():
        target = (out / info.filename).resolve()
        if target != base and not str(target).startswith(str(base) + "/"):
            raise SystemExit(f"unsafe ZIP member: {info.filename}")
    z.extractall(out)
a = out / ".final_authority"
def load(name): return json.loads((a / name).read_text(encoding="utf-8"))
f13 = load("FINAL_13_BUILD_RESULTS.json")
ba = load("BUILDALL_RESULT.json")
c1 = load("CLEAN_BUILD_1_RESULT.json")
c2 = load("CLEAN_BUILD_2_RESULT.json")
ck = load("FINAL_15_CHECKLIST_RESULT.json")
fo = load("FORBIDDEN_AUDIT.json")
ax = load("AXIOM_AUDIT.json")
ident = load("FINAL_SOURCE_IDENTITY.json")
assert f13["pass"] is True and f13["counts"] == {"PASS":13,"FAIL":0,"SKIPPED":0,"NOT_RUN":0}
assert f13["bridge_counts"] == {"PASS":2,"FAIL":0,"SKIPPED":0,"NOT_RUN":0}
ar = ba["aggregate_result"]
assert ba["pass"] is True and ar["exit"] == ar["error_headers"] == ar["panic_lines"] == ar["sorry_warning_lines"] == 0
assert c1["pass"] is True and c2["pass"] is True
assert c1["source_commit"] == c2["source_commit"] == "61a48f07e42bc5bf1610a8df3e7cf5ec7e1461c3"
assert ck["pass"] is True and ck["counts"] == {"PASS":15,"FAIL":0,"SKIPPED":0,"NOT_RUN":0}
assert fo["pass"] is True and fo["forbidden_count"] == 0
assert ax["pass"] is True
assert ident["pass"] is True and ident["tested_source_commit"] == "61a48f07e42bc5bf1610a8df3e7cf5ec7e1461c3"
assert record["authority_commit"] == "61a48f07e42bc5bf1610a8df3e7cf5ec7e1461c3"
print("evidence JSON consistency: PASS")
PY

[ -d "$REPO_DIR/.git" ] || die "RepoDir is not a Git working tree: $REPO_DIR"
head="$(git -C "$REPO_DIR" rev-parse HEAD)"
[ "$head" = "$AUTHORITY_COMMIT" ] || die "HEAD $head does not equal authority commit"
target="$(git -C "$REPO_DIR" rev-parse "$TAG^{}")"
[ "$target" = "$AUTHORITY_COMMIT" ] || die "tag target $target does not equal authority commit"
tag_type="$(git -C "$REPO_DIR" cat-file -t "refs/tags/$TAG")"
[ "$tag_type" = "tag" ] || die "canonical tag is not annotated (type=$tag_type)"
[ -z "$(git -C "$REPO_DIR" status --porcelain --untracked-files=no)" ] || die "tracked working tree is dirty"

python3 - "$PACKAGE_DIR/FINAL_AUTHORITY_RECORD.json" "$REPO_DIR" <<'PY'
import hashlib, json, pathlib, subprocess, sys
record = json.loads(pathlib.Path(sys.argv[1]).read_text(encoding="utf-8"))
repo = pathlib.Path(sys.argv[2])
def git(*args):
    return subprocess.check_output(["git", "-C", str(repo), *args], text=True).strip()
rows = record["primary_roots"] + record["bridges"] + [record["buildall_fingerprint"]]
for row in rows:
    path = repo / row["path"]
    if not path.is_file(): raise SystemExit(f"missing source: {row['path']}")
    if hashlib.sha256(path.read_bytes()).hexdigest() != row["sha256"]:
        raise SystemExit(f"source SHA256 mismatch: {row['path']}")
    if git("hash-object", "--no-filters", row["path"]) != row["git_blob"]:
        raise SystemExit(f"Git blob mismatch: {row['path']}")
manifest = repo / "lake-manifest.json"
if hashlib.sha256(manifest.read_bytes()).hexdigest() != "672474eb93bc14c66cd1ff45203c451987fe525f7b5d13ecd83140be46434b26":
    raise SystemExit("lake-manifest SHA256 mismatch")
if (repo / "lean-toolchain").read_text().strip() != "leanprover/lean4:v4.33.0-rc1":
    raise SystemExit("lean-toolchain mismatch")
print("source fingerprints and manifest: PASS")
PY

if [ "${FULL_LEAN:-0}" = "1" ]; then
  printf '%s\n' "Running optional full Lean authority reproduction..."
  (cd "$REPO_DIR" && python3 scripts/final_authority_gate_v5.py)
fi

printf '%s\n' "VERIFY_FINAL_AUTHORITY: PASS"
