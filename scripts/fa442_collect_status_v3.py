from fa442_collect_status import TARGETS, main

TARGETS.extend([
    {
        "branch": "fix/fa442-baseline-direct-smoke-20260810",
        "workflow_name": "FA442 baseline direct metric smoke gate",
        "report_paths": [
            "build-logs/fa442-baseline-direct-smoke/METRIC.json",
            "build-logs/fa442-baseline-direct-smoke/ROOT_CAUSE.json",
            "build-logs/fa442-baseline-direct-smoke/ROOT_CAUSE.md",
        ],
    },
    {
        "branch": "fix/fa442-baseline-direct-smoke-20260810",
        "workflow_name": "FA442 baseline direct metric smoke gate v2",
        "report_paths": [
            "build-logs/fa442-baseline-direct-smoke/METRIC_V2.json",
            "build-logs/fa442-baseline-direct-smoke/ROOT_CAUSE.json",
            "build-logs/fa442-baseline-direct-smoke/ROOT_CAUSE.md",
        ],
    },
])

if __name__ == "__main__":
    main()
