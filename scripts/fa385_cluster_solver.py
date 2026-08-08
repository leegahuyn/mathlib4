from __future__ import annotations

import argparse
import importlib.util
import json
import re
import shutil
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"


def import_base():
    path = ROOT / "scripts" / "fa383_parallel_solver.py"
    spec = importlib.util.spec_from_file_location("fa383_cluster_base", path)
    if spec is None or spec.loader is None:
        raise RuntimeError("cannot import fa383_parallel_solver.py")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


B = import_base()
ERROR_HEADER = B.ERROR_HEADER


def model_order(primary: str) -> list[str]:
    models = [
        primary,
        "openai/gpt-5",
        "openai/gpt-4.1",
        "openai/gpt-4o",
        "xai/grok-3",
        "deepseek/DeepSeek-V3-0324",
        "mistral-ai/Mistral-Large-2411",
        "meta/Llama-4-Scout-17B-16E-Instruct",
        "microsoft/Phi-4",
    ]
    result: list[str] = []
    for model in models:
        if model and model not in result:
            result.append(model)
    return result


def declaration_start(lines: list[str], line: int) -> int:
    pattern = re.compile(
        r"^\s*(?:(?:private|public|protected|noncomputable)\s+)*"
        r"(?:theorem|lemma|corollary|def|abbrev|instance|example)\b"
    )
    for index in range(line, max(1, line - 800), -1):
        if pattern.match(lines[index - 1]):
            return index
    return max(1, line - 40)


def clustered_errors(log: str, limit: int = 12):
    selected = []
    seen: set[tuple[int, int, str]] = set()
    for match in ERROR_HEADER.finditer(log):
        key = (
            int(match.group("line")),
            int(match.group("col")),
            match.group("message"),
        )
        if key in seen:
            continue
        seen.add(key)
        selected.append(match)
        if len(selected) >= limit:
            break
    return selected


def build_cluster_prompt(metric, log: str, cluster_round: int, feedback: str) -> str:
    source_lines = TARGET.read_text(encoding="utf-8").splitlines()
    matches = clustered_errors(log)
    if not matches:
        raise RuntimeError("no parsable FunctionalAnalysis error headers")
    declaration_groups: dict[int, list] = {}
    for match in matches:
        start = declaration_start(source_lines, int(match.group("line")))
        declaration_groups.setdefault(start, []).append(match)

    parts = [
        "Return ONLY a unified diff for PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean.",
        "Do not use Markdown fences and do not add prose.",
        "",
        "Hard constraints:",
        "- Preserve every existing public theorem/lemma/corollary name, binder, assumption, and conclusion.",
        "- Do not change imports.",
        "- Never add sorry, admit, global axiom, unsafe, native_decide, or Lean.ofReduceBool.",
        "- You may rewrite proof bodies and add small private helper lemmas immediately before use.",
        "- The candidate is compiled with Lean 4.33.0-rc1 and the pinned current Mathlib cache.",
        "",
        "Task:",
        "- Diagnose the shared root of the first error cluster rather than patching each cascade independently.",
        "- Fix only declarations represented below and their immediate shared private helper/API layer.",
        "- Prefer explicit current Mathlib APIs, typed calc blocks, extensionality, and local bridge lemmas.",
        "- Do not replace the mathematical construction by a weaker one.",
        "",
        f"Cluster round: {cluster_round}",
        f"Source SHA-256: {metric.source_sha256}",
        f"Current metric: exit={metric.exit_code}, errors={metric.errors}, first_line={metric.first_line}",
    ]

    for group_index, (start, group) in enumerate(sorted(declaration_groups.items()), 1):
        first_line = int(group[0].group("line"))
        last_line = max(int(match.group("line")) for match in group)
        context_start = max(1, start - 8)
        context_end = min(len(source_lines), max(last_line + 70, start + 120))
        parts.extend(
            [
                "",
                f"## Declaration cluster {group_index}",
                "Errors:",
            ]
        )
        for match in group:
            parts.extend(
                [
                    f"### {match.group('line')}:{match.group('col')} — {match.group('message')}",
                    "```text",
                    B.compiler_block(log, match),
                    "```",
                ]
            )
        parts.extend(
            [
                "Source context:",
                "```lean",
                "\n".join(
                    f"{index}: {source_lines[index - 1]}"
                    for index in range(context_start, context_end + 1)
                ),
                "```",
            ]
        )

    all_blocks = "\n".join(B.compiler_block(log, match) for match in matches)
    parts.extend(
        [
            "",
            "Exact-checkout API search for this cluster:",
            B.exact_api_search(all_blocks) or "(no additional exact-name hits)",
            "",
            "Prior compiler feedback for earlier revisions of this same cluster:",
            "```text",
            feedback[-18000:],
            "```",
            "",
            "Earlier pass summaries to avoid repeating:",
            "```text",
            B.previous_diagnosis(),
            "```",
        ]
    )
    return "\n".join(parts)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--primary-model", required=True)
    parser.add_argument("--output-dir", required=True)
    parser.add_argument("--max-clusters", type=int, default=10)
    parser.add_argument("--max-revisions", type=int, default=4)
    args = parser.parse_args()

    output = Path(args.output_dir)
    output.mkdir(parents=True, exist_ok=True)
    models = model_order(args.primary_model)
    metric, log = B.compile_source(output, "baseline", max_errors=120)
    history: list[dict[str, object]] = []
    accepted = 0
    feedback_history = ""

    if metric.exit_code == 0 and metric.errors == 0:
        shutil.copy2(TARGET, output / "best-source.lean")
        (output / "best-metric.json").write_text(
            json.dumps(metric.__dict__, indent=2), encoding="utf-8"
        )
        (output / "state.json").write_text(
            json.dumps({"complete_fa": True, "accepted": 0}, indent=2),
            encoding="utf-8",
        )
        return 0

    for cluster_round in range(1, args.max_clusters + 1):
        original = TARGET.read_bytes()
        prompt = build_cluster_prompt(metric, log, cluster_round, feedback_history)
        (output / f"cluster-{cluster_round:02d}-prompt.md").write_text(
            prompt, encoding="utf-8"
        )
        messages = [
            {
                "role": "system",
                "content": (
                    "You are a senior Lean/mathlib maintainer. "
                    "Return a minimal, statement-preserving unified diff only."
                ),
            },
            {"role": "user", "content": prompt},
        ]
        improved = None
        outcomes: list[dict[str, object]] = []
        for revision in range(1, args.max_revisions + 1):
            tag = f"cluster-{cluster_round:02d}-revision-{revision:02d}"
            try:
                model, response = B.query_model(models, messages, output, tag)
            except Exception as exc:
                outcomes.append({"revision": revision, "exception": repr(exc)})
                break
            source, candidate_metric, feedback, candidate_log = B.evaluate_response(
                original,
                response,
                output,
                f"{tag}-{model.replace('/', '-')}",
                metric,
            )
            outcomes.append(
                {
                    "revision": revision,
                    "model": model,
                    "metric": (
                        candidate_metric.__dict__
                        if candidate_metric is not None
                        else None
                    ),
                    "feedback": feedback[-8000:],
                }
            )
            if source is not None and candidate_metric is not None:
                improved = (
                    source,
                    candidate_metric,
                    candidate_log,
                    model,
                    revision,
                )
                break
            messages.append({"role": "assistant", "content": response})
            messages.append({"role": "user", "content": feedback})
            feedback_history += "\n" + feedback[-10000:]
        record = {
            "cluster_round": cluster_round,
            "baseline": metric.__dict__,
            "outcomes": outcomes,
        }
        if improved is None:
            record["result"] = "no improving cluster candidate"
            history.append(record)
            (output / "history.json").write_text(
                json.dumps(history, indent=2), encoding="utf-8"
            )
            continue
        source, metric, log, model, revision = improved
        TARGET.write_bytes(source)
        accepted += 1
        record.update(
            {
                "result": "accepted",
                "model": model,
                "revision": revision,
                "metric": metric.__dict__,
            }
        )
        history.append(record)
        shutil.copy2(TARGET, output / "best-source.lean")
        (output / "best-metric.json").write_text(
            json.dumps(metric.__dict__, indent=2), encoding="utf-8"
        )
        (output / "history.json").write_text(
            json.dumps(history, indent=2), encoding="utf-8"
        )
        print(
            f"[fa385] accepted cluster={cluster_round} model={model} "
            f"revision={revision} metric={metric}"
        )
        if metric.exit_code == 0 and metric.errors == 0:
            break

    state = {
        "primary_model": args.primary_model,
        "accepted": accepted,
        "complete_fa": metric.exit_code == 0 and metric.errors == 0,
        "metric": metric.__dict__,
    }
    if not (output / "best-source.lean").exists():
        shutil.copy2(TARGET, output / "best-source.lean")
    if not (output / "best-metric.json").exists():
        (output / "best-metric.json").write_text(
            json.dumps(metric.__dict__, indent=2), encoding="utf-8"
        )
    (output / "state.json").write_text(
        json.dumps(state, indent=2), encoding="utf-8"
    )
    return 0 if state["complete_fa"] else 2


if __name__ == "__main__":
    raise SystemExit(main())
