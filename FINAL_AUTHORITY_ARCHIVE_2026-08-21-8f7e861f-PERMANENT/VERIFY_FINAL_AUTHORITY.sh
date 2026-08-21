#!/usr/bin/env bash
set -euo pipefail
P="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
(cd "$P" && sha256sum --check --strict SHA256SUMS.txt)
jq -e '.counts.PASS==13 and .bridge_counts.PASS==2' "$P/FINAL_13_BUILD_RESULTS.json" >/dev/null
jq -e '.aggregate_result.exit==0 and .aggregate_result.error_headers==0' "$P/BUILDALL_RESULT.json" >/dev/null
jq -e '.counts.PASS==15' "$P/FINAL_15_CHECKLIST_RESULT.json" >/dev/null
jq -e '.tested_source_commit=="8f7e861f5f76c0aa5d347e0de865516a1ba23922"' "$P/FINAL_SOURCE_IDENTITY.json" >/dev/null
test "$(gzip -dc "$P/formalization-final-source-8f7e861f.tar.gz" | git get-tar-commit-id)" = 8f7e861f5f76c0aa5d347e0de865516a1ba23922
echo VERIFY_FINAL_AUTHORITY=PASS
