from __future__ import annotations

from pathlib import Path

SOURCE = Path(__file__).with_name("github_models_fa_tournament_agent.py")
text = SOURCE.read_text(encoding="utf-8")

old = '''        improving = [
            result for result in candidate_results
            if result.signature_ok
            and result.forbidden is None
            and result.source_file is not None
            and improves(
                rc,
                current_errors,
                result.exit_code,
                [] if result.first_error is None else [result.first_error],
                args.max_errors,
            )
        ]
'''

new = '''        improving = []
        old_first_line = current_errors[0].line if current_errors else 0
        old_error_count = len(current_errors)
        for result in candidate_results:
            if not result.signature_ok or result.forbidden is not None or result.source_file is None:
                continue
            if result.exit_code == 0 and result.first_error is None:
                improving.append(result)
                continue
            if result.first_error is None:
                continue
            frontier_advanced = result.first_error.line > old_first_line + 2
            error_count_decreased = result.error_count < old_error_count
            if frontier_advanced or error_count_decreased:
                improving.append(result)
'''

count = text.count(old)
if count != 1:
    raise RuntimeError(f"expected one tournament improving block, found {count}")
text = text.replace(old, new)

namespace = {"__name__": "__main__", "__file__": str(SOURCE)}
exec(compile(text, str(SOURCE), "exec"), namespace)
