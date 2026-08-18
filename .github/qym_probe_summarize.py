#!/usr/bin/env python3
from pathlib import Path
import collections, hashlib, json, os, re, sys

root = Path(sys.argv[1])
schema = sys.argv[2]
candidate_sha = sys.argv[3]
candidate_blob = sys.argv[4]
baseline_sha = sys.argv[5]

raw = (root / "QYM.log").read_bytes() if (root / "QYM.log").exists() else b""
text = raw.decode("utf-8", errors="replace")
pat = re.compile(
    r"^(?P<file>.*?\.lean):(?P<line>\d+):(?P<column>\d+): "
    r"(?P<severity>error|warning)(?:\((?P<code>[^)]*)\))?:\s*(?P<message>.*)$",
    re.M,
)
rows = []
for m in pat.finditer(text):
    r = m.groupdict()
    r["line"] = int(r["line"])
    r["column"] = int(r["column"])
    rows.append(r)
errors = [r for r in rows if r["severity"] == "error"]
warnings = [r for r in rows if r["severity"] == "warning"]
panics = re.findall(
    r"(?im)^.*(?:internal error|uncaught exception|panic(?:!|:|\s)).*$", text
)

(root / "QYM.diagnostics.jsonl").write_text(
    "".join(json.dumps(r, sort_keys=True) + "\n" for r in rows)
)
(root / "QYM.error-headers.txt").write_text(
    "".join(
        "{}:{}:{}: error{}: {}\n".format(
            r["file"], r["line"], r["column"],
            f"({r['code']})" if r["code"] else "", r["message"]
        )
        for r in errors
    )
)
(root / "QYM.panic-lines.txt").write_text("".join(x + "\n" for x in panics))
rc = int((root / "QYM.exit").read_text().strip()) if (root / "QYM.exit").exists() else None
result = {
    "schema": schema,
    "github_sha": os.environ.get("GITHUB_SHA"),
    "baseline_qym_sha256": baseline_sha,
    "candidate_qym_sha256": candidate_sha,
    "candidate_qym_blob": candidate_blob,
    "exit": rc,
    "error_headers": len(errors),
    "warning_headers": len(warnings),
    "error_codes": dict(sorted(collections.Counter(r["code"] or "uncoded" for r in errors).items())),
    "first_error": errors[0] if errors else None,
    "last_error": errors[-1] if errors else None,
    "panic_lines": len(panics),
    "log_sha256": hashlib.sha256(raw).hexdigest(),
    "semantic_pass": rc == 0 and not errors and not panics,
}
(root / "PROBE_RESULT.json").write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
print(json.dumps(result, indent=2, sort_keys=True))
