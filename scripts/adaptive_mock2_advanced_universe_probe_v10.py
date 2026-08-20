from __future__ import annotations

import argparse
import json
from pathlib import Path

import adaptive_mock2_advanced_universe_probe_v9 as base


def prepare(
    source_path: Path,
    probe_path: Path,
    map_path: Path,
    include_bare: bool,
) -> int:
    source = source_path.read_text(encoding="utf-8")
    candidates = base.collect_candidates(source, include_bare)
    if not candidates:
        print("no unspecialized probe candidates")
        return 3

    lines = ["", "", "set_option pp.universes true", "namespace Mock2Adv"]
    for namespace in base.TARGET_NAMESPACES:
        local = [item for item in candidates if item.namespace == namespace]
        if not local:
            continue
        lines.append(f"namespace {namespace}")
        for item in local:
            lines.append(f'#check "UNIV_PROBE_BEGIN|{item.ident}"')
            lines.append(f"#check @{item.spelling}")
            lines.append(f'#check "UNIV_PROBE_END|{item.ident}"')
        lines.append(f"end {namespace}")
    lines.extend(["end Mock2Adv", ""])

    probe_path.write_text(source + "\n".join(lines), encoding="utf-8")
    map_path.write_text(
        json.dumps([item.__dict__ for item in candidates], ensure_ascii=False, indent=2),
        encoding="utf-8",
    )
    print(f"prepared {len(candidates)} file-end universe probes")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser()
    sub = parser.add_subparsers(dest="command", required=True)

    prep = sub.add_parser("prepare")
    prep.add_argument("source", type=Path)
    prep.add_argument("probe", type=Path)
    prep.add_argument("mapping", type=Path)
    prep.add_argument("--include-bare", action="store_true")

    app = sub.add_parser("apply")
    app.add_argument("source", type=Path)
    app.add_argument("mapping", type=Path)
    app.add_argument("log", type=Path)

    args = parser.parse_args()
    if args.command == "prepare":
        return prepare(args.source, args.probe, args.mapping, args.include_bare)
    return base.apply(args.source, args.mapping, args.log)


if __name__ == "__main__":
    raise SystemExit(main())
