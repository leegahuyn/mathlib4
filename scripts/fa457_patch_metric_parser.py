#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path

PATH = Path("scripts/fa442_record_direct_metric.py")
PATCH_MARKER = '"FA_first_error_code": fa_errors["first_code"]'


def replace_once(text: str, old: str, new: str, label: str) -> str:
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f"{label}: expected one occurrence, found {count}")
    return text.replace(old, new)


def main() -> None:
    text = PATH.read_text(encoding="utf-8")
    if PATCH_MARKER in text:
        print("coded Lean error parser already installed")
        return
    text = replace_once(
        text,
        '''    pattern = re.compile(\n        rf"(?m)^(?P<prefix>.*?{re.escape(stem)}\\.lean):"\n        r"(?P<line>\\d+):(?P<col>\\d+):\\s+error:\\s*(?P<message>.*)$"\n    )\n''',
        '''    # Lean emits both classic headers (`error:`) and coded headers such as\n    # `error(lean.invalidField):`. Omitting coded headers can create a false\n    # first-error advance and therefore a false selector promotion.\n    pattern = re.compile(\n        rf"(?m)^(?P<prefix>.*?{re.escape(stem)}\\.lean):"\n        r"(?P<line>\\d+):(?P<col>\\d+):\\s+"\n        r"error(?:\\((?P<code>[^)\\r\\n]+)\\))?:\\s*(?P<message>.*)$"\n    )\n''',
        "error header regex",
    )
    text = replace_once(
        text,
        '''            if index > 0 and re.match(\n                r"^.*\\.lean:\\d+:\\d+:\\s+(?:error|warning):", raw\n            ):\n''',
        '''            if index > 0 and re.match(\n                r"^.*\\.lean:\\d+:\\d+:\\s+"\n                r"(?:error|warning)(?:\\([^)\\r\\n]+\\))?:", raw\n            ):\n''',
        "continuation header regex",
    )
    text = replace_once(
        text,
        '''        "first_message": message,\n        "log_path": str(log_path),\n''',
        '''        "first_code": matches[0].group("code") if matches else None,\n        "first_message": message,\n        "log_path": str(log_path),\n''',
        "first error code result",
    )
    text = replace_once(
        text,
        '''        "FA_first_error_message": fa_errors["first_message"],\n        "FA_first_error_declaration": first_declaration,\n''',
        '''        "FA_first_error_code": fa_errors["first_code"],\n        "FA_first_error_message": fa_errors["first_message"],\n        "FA_first_error_declaration": first_declaration,\n''',
        "metric error code field",
    )
    PATH.write_text(text, encoding="utf-8")
    print("installed coded Lean error parser")


if __name__ == "__main__":
    main()
