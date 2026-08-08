from __future__ import annotations

import pass383_marker_watcher as watcher

watcher.WATCHER_BRANCH = 'fix/fa386-final-collector-20260809'
watcher.BRANCHES = [
    'fix/fa377-llm-loop-20260809',
    'fix/fa378-priority-beam-loop-20260809',
    'fix/fa379-blocking-priority-loop-20260809',
    'fix/fa380-blocking-cli-loop-20260809',
    'fix/fa381-instance-exhaustive-20260809',
    'fix/fa382-global-instance-probe-20260809',
    'fix/fa384-declaration-loop-20260809',
    'fix/fa385-race-supervisor-20260809',
]

if __name__ == '__main__':
    raise SystemExit(watcher.main())
