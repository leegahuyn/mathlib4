from __future__ import annotations

import re

import scripts.fa412_strict_champion_replay as engine

_original_discover = engine.discover_scripts


def discover_only_post_champion_repairs() -> list[dict[str, str]]:
    selected: list[dict[str, str]] = []
    for script in _original_discover():
        path = script['origin'].rsplit(':', 1)[-1]
        match = re.search(r'(?:^|/)fa(\d+)[^/]*\.py$', path)
        if match is None:
            continue
        number = int(match.group(1))
        if 377 <= number <= 411:
            selected.append(script)
    return selected


engine.discover_scripts = discover_only_post_champion_repairs
engine.MAX_CANDIDATE_COMPILES = 24

if __name__ == '__main__':
    raise SystemExit(engine.main())
