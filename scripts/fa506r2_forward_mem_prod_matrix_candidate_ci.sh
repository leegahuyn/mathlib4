#!/usr/bin/env bash
set -euo pipefail

die() {
  printf 'FA506-r2 evidence gate: %s\n' "$*" >&2
  exit 86
}

require_eq() {
  local name="$1" expected="$2"
  local actual="${!name-}"
  [[ "$actual" == "$expected" ]] ||
    die "$name must equal $(printf '%q' "$expected"), got $(printf '%q' "$actual")"
}

require_positive() {
  local name="$1"
  local actual="${!name-}"
  [[ "$actual" =~ ^[1-9][0-9]*$ ]] || die "$name must be a positive decimal"
}

require_sha40() {
  local name="$1"
  local actual="${!name-}"
  [[ "$actual" =~ ^[0-9a-f]{40}$ ]] || die "$name must be 40 lowercase hex"
  [[ "$actual" != 0000000000000000000000000000000000000000 ]] ||
    die "$name is the zero placeholder"
}

require_sha64() {
  local name="$1"
  local actual="${!name-}"
  [[ "$actual" =~ ^[0-9a-f]{64}$ ]] || die "$name must be 64 lowercase hex"
}

require_artifact() {
  local prefix="$1"
  require_positive "${prefix}_EVIDENCE_ARTIFACT_ID"
  require_positive "${prefix}_EVIDENCE_ARTIFACT_SIZE"
  local name_var="${prefix}_EVIDENCE_ARTIFACT_NAME"
  local digest_var="${prefix}_EVIDENCE_ARTIFACT_DIGEST"
  local artifact_name="${!name_var-}" artifact_digest="${!digest_var-}"
  [[ "$artifact_name" =~ ^[A-Za-z0-9_.-]+$ ]] || die "$name_var is invalid"
  [[ "$artifact_digest" =~ ^sha256:[0-9a-f]{64}$ ]] || die "$digest_var is invalid"
}

require_direct() {
  local prefix="$1" source_sha="$2" source_bytes="$3" source_lines="$4"
  require_eq "${prefix}_EVIDENCE_STATUS" VERIFIED
  require_eq "${prefix}_EVIDENCE_LIVE_ATTESTED" VERIFIED
  require_positive "${prefix}_EVIDENCE_RUN_ID"
  require_positive "${prefix}_EVIDENCE_JOB_ID"
  require_sha40 "${prefix}_EVIDENCE_HEAD_SHA"
  require_artifact "$prefix"
  require_eq "${prefix}_EVIDENCE_SOURCE_SHA256" "$source_sha"
  require_eq "${prefix}_EVIDENCE_SOURCE_BYTES" "$source_bytes"
  require_eq "${prefix}_EVIDENCE_SOURCE_LINES" "$source_lines"
  require_eq "${prefix}_CLASSIFICATION" LEAN_FAILURE
  require_eq "${prefix}_INFRA_REASONS" '[]'
  require_eq "${prefix}_MOCK2_EXIT" 0
  require_eq "${prefix}_MOCK2_ADVANCED_EXIT" 0
  require_eq "${prefix}_FA_EXIT" 1
  require_eq "${prefix}_PREVIOUS_FRONTIER_DECLARATION" \
    integral_selectedHeightGraphDensity_stripTail_eq_iterated
  require_eq "${prefix}_PREVIOUS_FRONTIER_INDEX" 2835
  require_eq "${prefix}_FIRST_ERROR_DECLARATION" \
    complex_image_heightStrip_eq_coe_image_selectedBaseCuspStrip
  require_eq "${prefix}_FIRST_ERROR_INDEX" 2839
  require_eq "${prefix}_FIRST_ERROR_LINE" 36111
  require_eq "${prefix}_FIRST_ERROR_COL" 4
}

require_direct FA505 \
  c56e320e31dbb4c2d80a7b6c05e3417b9683fe982a9f006bbd6166add95ea9e7 \
  2700162 60539
require_direct FA506 \
  fbf76ffa75885c76492c6795ac907d47693d964d30043fd8cced93ca71719611 \
  2700268 60541

require_eq FA506R2_UPSTREAM_ATTESTATION_PATH /tmp/fa506r2-upstream-attestation.json
require_sha64 FA506R2_UPSTREAM_ATTESTATION_SHA256
[[ -f "$FA506R2_UPSTREAM_ATTESTATION_PATH" ]] || die "attestation file missing"
actual_attestation_sha="$(sha256sum "$FA506R2_UPSTREAM_ATTESTATION_PATH" | awk '{print $1}')"
require_eq FA506R2_UPSTREAM_ATTESTATION_SHA256 "$actual_attestation_sha"

case "${FA506R2_VARIANT-}" in
  membership_only)
    expected_sha=59bc2a484f508d23f03c9d92920b3746f62754e35a814cc4d3eec7be3ed12088
    expected_bytes=2700282
    expected_lines=60541
    ;;
  membership_plus_frontier_batch)
    expected_sha=d0a3decee1c0a7a781d14fdf122e235d71d8f210bb65a894dc4e518821bf03ec
    expected_bytes=2702252
    expected_lines=60573
    ;;
  *)
    die "unsupported FA506R2_VARIANT=${FA506R2_VARIANT-}"
    ;;
esac
require_eq FA506R2_EXPECTED_SHA256 "$expected_sha"
require_eq FA506R2_EXPECTED_BYTES "$expected_bytes"
require_eq FA506R2_EXPECTED_LINES "$expected_lines"

python3 - "$FA506R2_UPSTREAM_ATTESTATION_PATH" <<'PY'
from pathlib import Path
import json
import os
import sys

payload = json.loads(Path(sys.argv[1]).read_text(encoding="utf-8"))
if payload.get("schema") != "fa506r2-upstream-evidence-v1":
    raise SystemExit("FA506-r2 attestation schema mismatch")
if payload.get("all_checks_passed") is not True:
    raise SystemExit("FA506-r2 attestation checks failed")
for prefix in ("FA505", "FA506"):
    item = payload.get(prefix.lower(), {})
    expected = {
        "run_id": int(os.environ[f"{prefix}_EVIDENCE_RUN_ID"]),
        "job_id": int(os.environ[f"{prefix}_EVIDENCE_JOB_ID"]),
        "head_sha": os.environ[f"{prefix}_EVIDENCE_HEAD_SHA"],
        "artifact_id": int(os.environ[f"{prefix}_EVIDENCE_ARTIFACT_ID"]),
    }
    if item.get("all_checks_passed") is not True:
        raise SystemExit(f"{prefix} live checks failed")
    for key, value in expected.items():
        if item.get(key) != value:
            raise SystemExit(f"{prefix} {key} mismatch")
PY

export FA506_VARIANT=explicit_upper_half_plane_coe_projections
export FA_COMPILE_MAX_ERRORS="${FA_COMPILE_MAX_ERRORS:-32}"
require_eq FA_COMPILE_MAX_ERRORS 32

python3 - <<'PY'
from pathlib import Path
import os

variant = os.environ["FA506R2_VARIANT"]
src = Path("scripts/fa506_complex_height_strip_coe_candidate_ci.sh")
dst = Path(f"/tmp/fa506r2-{variant}-candidate-ci.sh")
text = src.read_text(encoding="utf-8")


def once(old: str, new: str) -> None:
    global text
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f"expected one {old!r}, got {count}")
    text = text.replace(old, new, 1)


once(
    "build-logs/codex-fa506-complex-height-strip-coe",
    f"build-logs/codex-fa506r2-forward-mem-prod-{variant}",
)
once(
    "scripts/fa506_prepare_complex_height_strip_coe.py",
    "scripts/fa506r2_prepare_forward_mem_prod_matrix.py",
)
dst.write_text(text, encoding="utf-8")
PY

exec bash "/tmp/fa506r2-${FA506R2_VARIANT}-candidate-ci.sh"
