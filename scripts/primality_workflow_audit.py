from __future__ import annotations

import re
from pathlib import Path


def main() -> int:
    bad: list[tuple[Path, int, str, str]] = []
    workflows = sorted(
        path
        for path in Path(".github/workflows").iterdir()
        if path.is_file() and path.suffix in {".yml", ".yaml"}
    )
    if not workflows:
        raise SystemExit("no workflow files found")
    for path in workflows:
        for line_number, line in enumerate(
            path.read_text(encoding="utf-8").splitlines(), 1
        ):
            match = re.match(r"^\s*uses:\s*([^\s#]+)", line)
            if not match:
                continue
            value = match.group(1).strip().strip('"').strip("'")
            if value.startswith("./") or value.startswith("docker://"):
                continue
            if "@" not in value:
                bad.append((path, line_number, value, "missing @ref"))
                continue
            reference = value.rsplit("@", 1)[1]
            if not re.fullmatch(r"[0-9a-fA-F]{40}", reference):
                bad.append(
                    (path, line_number, value, "ref is not a 40-character SHA")
                )
    for path, line_number, value, reason in bad:
        print(f"{path}:{line_number}: {reason}: {value}")
    return 1 if bad else 0


if __name__ == "__main__":
    raise SystemExit(main())
