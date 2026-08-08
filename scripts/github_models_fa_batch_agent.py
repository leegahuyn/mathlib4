from __future__ import annotations

import argparse
import dataclasses
import hashlib
import json
import os
import re
import shutil
import subprocess
import time
import urllib.error
import urllib.request
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
OUT = ROOT / "build-logs" / "fa-batch-agent"
WORK = OUT / "working.lean"
STATE = OUT / "state.json"
ERR = re.compile(r"^(.*?\.lean):(\d+):(\d+):\s+(?:error[^:]*:|error:)\s*(.*)$")
DECL = re.compile(
    r"^(\s*)(?:(?:private|protected|noncomputable|local)\s+)*"
    r"(theorem|lemma|corollary|example|instance|def|abbrev)\b"
)
FORBIDDEN = re.compile(
    r"(?m)^\s*(?:sorry|admit)\b|(?m)^\s*axiom\b|(?m)^\s*unsafe\b|"
    r"\bnative_decide\b|\bLean\.ofReduceBool\b"
)


@dataclasses.dataclass(frozen=True)
class Failure:
    line: int
    col: int
    message: str
    raw: str


@dataclasses.dataclass(frozen=True)
class Decl:
    start: int
    end: int
    proof_line: int
    header: tuple[str, ...]
    body: tuple[str, ...]
    name: str


def digest(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def strip_comments(text: str) -> str:
    text = re.sub(r"/-.*?-\/", "", text, flags=re.S)
    return re.sub(r"--.*$", "", text, flags=re.M)


def compile_lean(path: Path, max_errors: int = 80, timeout: int = 1500) -> tuple[int, str, float]:
    started = time.monotonic()
    try:
        proc = subprocess.run(
            ["lake", "env", "lean", f"-DmaxErrors={max_errors}", str(path)],
            cwd=ROOT,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=timeout,
            env={**os.environ, "LC_ALL": "C.UTF-8"},
        )
        return proc.returncode, proc.stdout, time.monotonic() - started
    except subprocess.TimeoutExpired as exc:
        output = exc.stdout or ""
        if isinstance(output, bytes):
            output = output.decode("utf-8", errors="replace")
        return 124, output + "\nFA_BATCH_COMPILE_TIMEOUT\n", time.monotonic() - started


def parse_failures(log: str) -> list[Failure]:
    result: list[Failure] = []
    for line in log.splitlines():
        match = ERR.match(line)
        if match:
            result.append(
                Failure(
                    line=int(match.group(2)),
                    col=int(match.group(3)),
                    message=match.group(4),
                    raw=line,
                )
            )
    return result


def declaration_bounds(lines: list[str]) -> list[tuple[int, int]]:
    starts = [i for i, line in enumerate(lines) if DECL.match(line)]
    return [
        (start, starts[index + 1] if index + 1 < len(starts) else len(lines))
        for index, start in enumerate(starts)
    ]


def declaration_for_line(lines: list[str], line_no: int) -> Decl | None:
    index = line_no - 1
    for start, end in declaration_bounds(lines):
        if start <= index < end:
            for proof_line in range(start, min(end, start + 200)):
                if ":= by" in lines[proof_line]:
                    left, right = lines[proof_line].split(":= by", 1)
                    header = tuple(lines[start:proof_line] + [left + ":= by"])
                    body_lines = ([right] if right.strip() else []) + lines[proof_line + 1 : end]
                    first = DECL.match(lines[start])
                    assert first is not None
                    rest = lines[start][first.end() :].strip()
                    name_match = re.match(r"(?:_root_\.)?([A-Za-z0-9_'.]+)", rest)
                    name = name_match.group(1) if name_match else f"line-{start + 1}"
                    return Decl(
                        start=start,
                        end=end,
                        proof_line=proof_line,
                        header=header,
                        body=tuple(body_lines),
                        name=name,
                    )
            return None
    return None


def grouped_declarations(lines: list[str], failures: list[Failure], limit: int) -> list[tuple[Decl, list[Failure]]]:
    result: list[tuple[Decl, list[Failure]]] = []
    seen: dict[int, int] = {}
    for failure in failures:
        decl = declaration_for_line(lines, failure.line)
        if decl is None:
            continue
        if decl.start in seen:
            result[seen[decl.start]][1].append(failure)
            continue
        if len(result) >= limit:
            continue
        seen[decl.start] = len(result)
        result.append((decl, [failure]))
    return result


def clean_model_body(raw: str) -> list[str]:
    text = raw.strip()
    fence = re.search(r"```(?:lean)?\s*(.*?)```", text, flags=re.S)
    if fence:
        text = fence.group(1).strip()
    if text.startswith(":= by"):
        text = text[len(":= by") :].lstrip()
    elif text.startswith("by\n"):
        text = text[2:].lstrip()
    if text.startswith("{\")"):
        raise ValueError("unexpected JSON-as-proof response")
    return text.splitlines()


def indent_body(header: tuple[str, ...], body: list[str]) -> list[str]:
    indent = re.match(r"^\s*", header[-1]).group(0) + "  "
    nonempty = [len(line) - len(line.lstrip()) for line in body if line.strip()]
    minimum = min(nonempty) if nonempty else 0
    return [indent + line[minimum:] if line.strip() else "" for line in body]


def call_model(prompt: str, token: str) -> tuple[str, str]:
    endpoint = "https://models.github.ai/inference/chat/completions"
    models = ["openai/gpt-4.1", "openai/gpt-4o", "openai/gpt-4.1-mini"]
    errors: list[str] = []
    for model in models:
        payload = json.dumps(
            {
                "model": model,
                "temperature": 0,
                "max_tokens": 8000,
                "messages": [
                    {
                        "role": "system",
                        "content": (
                            "You repair one Lean 4.33.0-rc1 proof against the pinned current Mathlib. "
                            "The declaration header is immutable. Return only the proof body after `:= by`, "
                            "without markdown fences. Never use sorry, admit, axiom, unsafe, native_decide, "
                            "or Lean.ofReduceBool. Do not add assumptions or weaken conclusions. Use explicit "
                            "namespace-qualified lemmas, `change`, `calc`, `convert`, and type annotations when API "
                            "elaboration is ambiguous. The returned text must compile in the supplied context."
                        ),
                    },
                    {"role": "user", "content": prompt},
                ],
            }
        ).encode("utf-8")
        request = urllib.request.Request(
            endpoint,
            data=payload,
            method="POST",
            headers={
                "Authorization": f"Bearer {token}",
                "Content-Type": "application/json",
                "Accept": "application/json",
                "X-GitHub-Api-Version": "2022-11-28",
            },
        )
        try:
            with urllib.request.urlopen(request, timeout=240) as response:
                data = json.loads(response.read().decode("utf-8"))
            return model, data["choices"][0]["message"]["content"]
        except (urllib.error.HTTPError, urllib.error.URLError, TimeoutError, KeyError, IndexError, json.JSONDecodeError) as exc:
            errors.append(f"{model}: {exc}")
    raise RuntimeError("all GitHub Models calls failed: " + " | ".join(errors))


def prompt_for(lines: list[str], decl: Decl, failures: list[Failure], attempt: int) -> str:
    context_start = max(0, decl.start - 120)
    context_end = min(len(lines), decl.end + 80)
    context = "\n".join(f"{i + 1}: {lines[i]}" for i in range(context_start, context_end))
    diagnostics = "\n".join(f.raw for f in failures)
    return f"""
Immutable declaration header:

{chr(10).join(decl.header)}

Current proof body:

{chr(10).join(decl.body)}

Compiler errors located in this declaration:

{diagnostics}

Nearby source context:

{context}

Return only a complete replacement proof body after `:= by`.
This is repair attempt {attempt}. Keep every binder, type, assumption, and conclusion in the header unchanged.
""".strip()


def apply_replacements(lines: list[str], replacements: list[tuple[Decl, list[str]]]) -> list[str]:
    output = list(lines)
    for decl, body in sorted(replacements, key=lambda item: item[0].start, reverse=True):
        replacement = list(decl.header) + indent_body(decl.header, body)
        output[decl.start : decl.end] = replacement
    return output


def metric(rc: int, failures: list[Failure], cap: int) -> tuple[int, int, int]:
    if rc == 0 and not failures:
        return (-1, -10**9, -10**9)
    count = min(len(failures), cap)
    first_line = failures[0].line if failures else 0
    distinct_lines = len({failure.line for failure in failures})
    return (count, -first_line, -distinct_lines)


def better(old_rc: int, old_failures: list[Failure], new_rc: int,
           new_failures: list[Failure], cap: int) -> bool:
    if new_rc == 0 and not new_failures:
        return True
    if not old_failures or not new_failures:
        return False
    if new_failures[0].line > old_failures[0].line + 2:
        return True
    old_metric = metric(old_rc, old_failures, cap)
    new_metric = metric(new_rc, new_failures, cap)
    return new_metric < old_metric


def write_state(payload: dict) -> None:
    OUT.mkdir(parents=True, exist_ok=True)
    STATE.write_text(json.dumps(payload, indent=2, ensure_ascii=False), encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--seed", type=Path, default=TARGET)
    parser.add_argument("--rounds", type=int, default=8)
    parser.add_argument("--declarations", type=int, default=4)
    parser.add_argument("--attempts", type=int, default=2)
    parser.add_argument("--max-errors", type=int, default=80)
    parser.add_argument("--materialize-progress", action="store_true")
    args = parser.parse_args()

    token = os.environ.get("GITHUB_TOKEN") or os.environ.get("GH_TOKEN")
    if not token:
        raise SystemExit("GITHUB_TOKEN is required")
    OUT.mkdir(parents=True, exist_ok=True)
    shutil.copy2(args.seed, WORK)
    history: list[dict] = []
    any_progress = False

    for round_no in range(1, args.rounds + 1):
        text = WORK.read_text(encoding="utf-8")
        rc, log, elapsed = compile_lean(WORK, args.max_errors)
        (OUT / f"round-{round_no}-before.log").write_text(log, encoding="utf-8")
        current_failures = parse_failures(log)
        entry: dict = {
            "round": round_no,
            "input_sha256": digest(text),
            "input_exit": rc,
            "input_elapsed_seconds": elapsed,
            "input_error_count": len(current_failures),
            "input_first_error": dataclasses.asdict(current_failures[0]) if current_failures else None,
            "repairs": [],
        }
        history.append(entry)
        write_state({"status": "running", "history": history})
        print(json.dumps(entry, ensure_ascii=False), flush=True)

        if rc == 0 and not current_failures:
            rc2, log2, elapsed2 = compile_lean(WORK, 2000)
            (OUT / "compile-second.log").write_text(log2, encoding="utf-8")
            second = parse_failures(log2)
            result = {
                "status": "pass" if rc2 == 0 and not second else "second-run-failed",
                "sha256": digest(text),
                "first_exit": rc,
                "second_exit": rc2,
                "second_elapsed_seconds": elapsed2,
                "second_first_error": dataclasses.asdict(second[0]) if second else None,
                "history": history,
            }
            write_state(result)
            if result["status"] == "pass":
                shutil.copy2(WORK, OUT / "Mock2_FunctionalAnalysis.PASS.lean")
                if args.materialize_progress:
                    shutil.copy2(WORK, TARGET)
                return 0
            return 2

        lines = text.splitlines()
        groups = grouped_declarations(lines, current_failures, args.declarations)
        if not groups:
            entry["status"] = "no-repairable-proof-declarations"
            write_state({"status": "stuck", "history": history})
            break

        proposed: list[tuple[Decl, list[str]]] = []
        for decl, decl_failures in groups:
            accepted_response: tuple[str, list[str], int] | None = None
            records: list[dict] = []
            for attempt in range(1, args.attempts + 1):
                try:
                    model, raw = call_model(prompt_for(lines, decl, decl_failures, attempt), token)
                    (OUT / f"round-{round_no}-{decl.name}-attempt-{attempt}.txt").write_text(
                        raw, encoding="utf-8"
                    )
                    body = clean_model_body(raw)
                    candidate_fragment = "\n".join(decl.header) + "\n" + "\n".join(indent_body(decl.header, body))
                    bad = FORBIDDEN.search(strip_comments(candidate_fragment))
                    record = {"attempt": attempt, "model": model, "forbidden": bad.group(0) if bad else None}
                    records.append(record)
                    if bad is None and body:
                        accepted_response = (model, body, attempt)
                        break
                except Exception as exc:
                    records.append({"attempt": attempt, "error": str(exc)})
            entry["repairs"].append({"declaration": decl.name, "attempts": records})
            if accepted_response:
                proposed.append((decl, accepted_response[1]))

        if not proposed:
            entry["status"] = "no-model-proposals"
            write_state({"status": "stuck", "history": history})
            break

        candidate_lines = apply_replacements(lines, proposed)
        candidate_text = "\n".join(candidate_lines) + "\n"
        if FORBIDDEN.search(strip_comments(candidate_text)):
            entry["status"] = "forbidden-in-candidate"
            write_state({"status": "stuck", "history": history})
            break
        candidate_path = OUT / "candidate.lean"
        candidate_path.write_text(candidate_text, encoding="utf-8")
        crc, clog, celapsed = compile_lean(candidate_path, args.max_errors)
        (OUT / f"round-{round_no}-batch.log").write_text(clog, encoding="utf-8")
        candidate_failures = parse_failures(clog)
        entry.update(
            {
                "candidate_sha256": digest(candidate_text),
                "candidate_exit": crc,
                "candidate_elapsed_seconds": celapsed,
                "candidate_error_count": len(candidate_failures),
                "candidate_first_error": dataclasses.asdict(candidate_failures[0]) if candidate_failures else None,
            }
        )
        if better(rc, current_failures, crc, candidate_failures, args.max_errors):
            shutil.copy2(candidate_path, WORK)
            any_progress = True
            entry["accepted"] = "batch"
            write_state({"status": "running", "history": history})
            continue

        # Fall back to testing the proposed declaration repairs independently.
        individual_accepted = False
        for decl, body in proposed:
            one_lines = apply_replacements(lines, [(decl, body)])
            one_text = "\n".join(one_lines) + "\n"
            one_path = OUT / "candidate-one.lean"
            one_path.write_text(one_text, encoding="utf-8")
            orc, olog, oelapsed = compile_lean(one_path, args.max_errors)
            (OUT / f"round-{round_no}-{decl.name}-individual.log").write_text(
                olog, encoding="utf-8"
            )
            one_failures = parse_failures(olog)
            if better(rc, current_failures, orc, one_failures, args.max_errors):
                shutil.copy2(one_path, WORK)
                any_progress = True
                individual_accepted = True
                entry["accepted"] = f"individual:{decl.name}"
                entry["individual_exit"] = orc
                entry["individual_error_count"] = len(one_failures)
                entry["individual_first_error"] = dataclasses.asdict(one_failures[0]) if one_failures else None
                write_state({"status": "running", "history": history})
                break
        if not individual_accepted:
            entry["status"] = "no-kernel-improvement"
            write_state({"status": "stuck", "history": history})
            break

    final_text = WORK.read_text(encoding="utf-8")
    if any_progress:
        if args.materialize_progress:
            shutil.copy2(WORK, TARGET)
        write_state(
            {
                "status": "progress",
                "output_sha256": digest(final_text),
                "history": history,
            }
        )
        return 10
    write_state({"status": "stuck", "history": history})
    return 5


if __name__ == "__main__":
    raise SystemExit(main())
