#!/usr/bin/env python3
"""Hot-fix the archival publisher's binary artifact download path only.

The v1 publisher used urllib across GitHub's signed artifact redirect, which
forwarded the GitHub bearer token to Azure storage and caused a 401. This
wrapper leaves every reconciliation/tag/release rule unchanged and replaces
only fetch_original_artifact with GitHub CLI's redirect-safe binary download.
"""
from __future__ import annotations

import base64
import gzip
import os
from pathlib import Path
import re

bootstrap = Path(__file__).with_name("final_authority_release_publisher.py")
text = bootstrap.read_text(encoding="utf-8")
match = re.search(r"(?m)^PAYLOAD = '([^']+)'$", text)
if not match:
    raise RuntimeError("publisher payload not found")
source = gzip.decompress(base64.b64decode(match.group(1))).decode("utf-8")

replacement = r'''def fetch_original_artifact() -> Path:
    destination = EVIDENCE / ARTIFACT_FILENAME
    # GitHub's artifact endpoint redirects to signed Azure storage.  Use gh so
    # the GitHub bearer token is not forwarded to the storage host.
    with destination.open("wb") as out:
        p = subprocess.run(
            ["gh", "api", f"repos/{REPO}/actions/artifacts/{ARTIFACT}/zip"],
            stdout=out,
            stderr=subprocess.PIPE,
            check=False,
            env=os.environ.copy(),
        )
    if p.returncode != 0:
        die(
            "ARTIFACT_DOWNLOAD_FAILURE: gh api failed "
            f"({p.returncode}): {p.stderr.decode(errors='replace')}"
        )
    if sha256(destination) != ARTIFACT_SHA:
        die("ARTIFACT_HASH_MISMATCH: downloaded original evidence ZIP")
    return destination


def build_package'''

source, count = re.subn(
    r"def fetch_original_artifact\(\) -> Path:\n.*?\n\ndef build_package",
    replacement,
    source,
    count=1,
    flags=re.S,
)
if count != 1:
    raise RuntimeError(f"expected one artifact-download function, patched {count}")

namespace = {
    "__name__": "__main__",
    "__file__": "final_authority_release_publisher.py",
    "__package__": None,
}
exec(compile(source, "final_authority_release_publisher.py", "exec"), namespace, namespace)
