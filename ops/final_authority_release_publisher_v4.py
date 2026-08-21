#!/usr/bin/env python3
"""Archive publisher infrastructure fixes without changing authority semantics.

v1 forwarded the Actions token across an artifact redirect; v2 fixed that.
The Git Data REST ref endpoint is blocked for this Actions integration despite
contents:write, so v4 creates the same annotated tag object locally and pushes
only refs/tags/formalization-final-2026-08-21 over authenticated Git.  It never
pushes or advances a source branch.
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

artifact_replacement = r'''def fetch_original_artifact() -> Path:
    destination = EVIDENCE / ARTIFACT_FILENAME
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
    lambda _match: artifact_replacement,
    source,
    count=1,
    flags=re.S,
)
if count != 1:
    raise RuntimeError(f"expected one artifact-download function, patched {count}")

tag_replacement = r'''def create_or_verify_tag() -> str:
    ref = resolve_tag()
    if ref is not None:
        return verify_tag(ref)
    if not TOKEN:
        die("TAG_WRITE_PERMISSION_FAILURE: GH_TOKEN/GITHUB_TOKEN is missing")

    run("git", "config", "user.name", "leegahuyn", cwd=AUTHORITY)
    run(
        "git", "config", "user.email",
        "102484661+leegahuyn@users.noreply.github.com", cwd=AUTHORITY,
    )
    message_path = EVIDENCE / "TAG_MESSAGE.txt"
    message_path.write_text(tag_message() + "\n", encoding="utf-8")
    subprocess.run(
        ["git", "tag", "-d", TAG], cwd=AUTHORITY,
        stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, check=False,
    )
    p = subprocess.run(
        ["git", "tag", "-a", TAG, COMMIT, "-F", str(message_path)],
        cwd=AUTHORITY, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        check=False,
    )
    if p.returncode != 0:
        die(f"TAG_WRITE_PERMISSION_FAILURE: local annotated tag: {p.stderr}")

    auth = __import__("base64").b64encode(
        f"x-access-token:{TOKEN}".encode()
    ).decode()
    p = subprocess.run(
        [
            "git", "-c",
            f"http.https://github.com/.extraheader=AUTHORIZATION: basic {auth}",
            "push", f"{REPO_URL}.git",
            f"refs/tags/{TAG}:refs/tags/{TAG}",
        ],
        cwd=AUTHORITY, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        check=False,
    )
    if p.returncode != 0:
        # A concurrent idempotent retry may have created the exact tag.
        ref = resolve_tag()
        if ref is not None:
            return verify_tag(ref)
        die(f"TAG_WRITE_PERMISSION_FAILURE: authenticated git push: {p.stderr}")

    ref = resolve_tag()
    if ref is None:
        die("TAG_WRITE_PERMISSION_FAILURE: tag ref absent after authenticated push")
    return verify_tag(ref)


def get_release'''
source, count = re.subn(
    r"def create_or_verify_tag\(\) -> str:\n.*?\n\ndef get_release",
    lambda _match: tag_replacement,
    source,
    count=1,
    flags=re.S,
)
if count != 1:
    raise RuntimeError(f"expected one tag-creation function, patched {count}")

namespace = {
    "__name__": "__main__",
    "__file__": "final_authority_release_publisher.py",
    "__package__": None,
}
exec(compile(source, "final_authority_release_publisher.py", "exec"), namespace, namespace)
