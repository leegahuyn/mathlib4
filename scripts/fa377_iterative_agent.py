from __future__ import annotations

import json
import os
import re
import shutil
import subprocess
import sys
import time
import urllib.error
import urllib.request
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
STATE_DIR = ROOT / "build-logs" / "fa377-agent"
STATE_FILE = STATE_DIR / "state.json"
TOKEN = os.environ.get("GITHUB_TOKEN", "")
MAX_ITERATIONS = int(os.environ.get("FA_AGENT_MAX_ITERATIONS", "16"))
MAX_TOTAL_ITERATIONS = int(os.environ.get("FA_AGENT_MAX_TOTAL_ITERATIONS", "160"))
MODELS = [
    m.strip()
    for m in os.environ.get(
        "FA_AGENT_MODELS", "openai/gpt-5,openai/gpt-4.1,openai/gpt-4o"
    ).split(",")
    if m.strip()
]
FORBIDDEN_ADDITION = re.compile(
    r"(?m)^\+.*\b(?:sorry|admit|native_decide|Lean\.ofReduceBool)\b"
    r"|^\+\s*(?:public\s+)?axiom\b|^\+\s*unsafe\b"
)
PUBLIC_HEADER_CHANGE = re.compile(
    r"(?m)^[+-]\s*(?!private\b)(?:public\s+)?(?:theorem|lemma|corollary)\b"
)
IMPORT_CHANGE = re.compile(r"(?m)^[+-]\s*(?:public\s+)?import\b")
ERROR_HEADER = re.compile(
    r"(?P<file>[^\n:]*Mock2_FunctionalAnalysis[^\n:]*\.lean):"
    r"(?P<line>\d+):(?P<col>\d+):\s*error:\s*(?P<message>.*)"
)


@dataclass(frozen=True)
class Metric:
    exit_code: int
    errors: int
    first_line: int | None
    source_sha256: str

    def better_than(self, old: "Metric") -> bool:
        if self.exit_code == 0 and self.errors == 0:
            return True
        if self.errors < old.errors:
            return True
        if (
            self.errors <= old.errors
            and self.first_line is not None
            and old.first_line is not None
            and self.first_line > old.first_line
        ):
            return True
        return False


def run(
    args: list[str],
    *,
    cwd: Path = ROOT,
    input_text: str | None = None,
    timeout: int | None = None,
) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        args,
        cwd=cwd,
        input=input_text,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=timeout,
        check=False,
    )


def sha256_file(path: Path) -> str:
    import hashlib

    return hashlib.sha256(path.read_bytes()).hexdigest()


def metric_from_log(exit_code: int, log: str, source: Path) -> Metric:
    matches = list(ERROR_HEADER.finditer(log))
    first_line = int(matches[0].group("line")) if matches else None
    return Metric(
        exit_code=exit_code,
        errors=len(matches),
        first_line=first_line,
        source_sha256=sha256_file(source),
    )


def compile_source(label: str, max_errors: int = 120) -> tuple[Metric, str]:
    log_path = STATE_DIR / f"{label}.log"
    proc = run(
        [
            "lake",
            "env",
            "lean",
            f"-DmaxErrors={max_errors}",
            str(TARGET.relative_to(ROOT)),
        ],
        timeout=1800,
    )
    log_path.write_text(proc.stdout, encoding="utf-8")
    metric = metric_from_log(proc.returncode, proc.stdout, TARGET)
    (STATE_DIR / f"{label}-metric.json").write_text(
        json.dumps(metric.__dict__, indent=2), encoding="utf-8"
    )
    return metric, proc.stdout


def reconstruct_pass376_source() -> None:
    scripts: list[tuple[int, Path]] = []
    for path in (ROOT / "scripts").glob("diagnose_pass*_fa.sh"):
        match = re.search(r"pass(\d+)", path.name)
        if match:
            scripts.append((int(match.group(1)), path))
    if not scripts:
        raise RuntimeError("no FunctionalAnalysis diagnostic script found")
    pass_number, script = max(scripts)
    if pass_number < 376:
        raise RuntimeError(f"latest diagnostic is PASS {pass_number}, expected at least 376")
    print(f"[agent] reconstructing from {script}")
    proc = run(["bash", str(script.relative_to(ROOT))], timeout=1800)
    (STATE_DIR / "reconstruct.log").write_text(proc.stdout, encoding="utf-8")
    candidates = sorted(
        Path("/tmp").glob("diagnose-pass*-fa/source/Mock2_FunctionalAnalysis-pass*.lean"),
        key=lambda p: (p.stat().st_mtime_ns, p.stat().st_size),
        reverse=True,
    )
    if not candidates:
        raise RuntimeError("diagnostic script did not materialize a candidate source")
    shutil.copy2(candidates[0], TARGET)
    print(f"[agent] reconstructed {candidates[0]} sha256={sha256_file(TARGET)}")


def source_context(source_lines: list[str], line: int, before: int = 14, after: int = 22) -> str:
    start = max(1, line - before)
    end = min(len(source_lines), line + after)
    return "\n".join(f"{index}: {source_lines[index - 1]}" for index in range(start, end + 1))


def error_block(log: str, match: re.Match[str], limit: int = 9000) -> str:
    tail = log[match.start() :]
    next_match = re.search(
        r"\n[^\n:]*Mock2_FunctionalAnalysis[^\n:]*\.lean:\d+:\d+:\s*error:",
        tail[1:],
    )
    if next_match:
        return tail[: next_match.start() + 1]
    return tail[:limit]


def build_prompt(metric: Metric, log: str, iteration: int) -> str:
    source_lines = TARGET.read_text(encoding="utf-8").splitlines()
    matches = list(ERROR_HEADER.finditer(log))
    selected: list[re.Match[str]] = []
    seen: set[tuple[int, int, str]] = set()
    for match in matches:
        key = (
            int(match.group("line")),
            int(match.group("col")),
            match.group("message"),
        )
        if key in seen:
            continue
        seen.add(key)
        selected.append(match)
        if len(selected) >= 14:
            break
    parts = [
        "You are repairing a Lean 4.33.0-rc1 / current Mathlib source file.",
        "Return ONLY a unified diff against PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean.",
        "Do not wrap the diff in Markdown fences and do not add prose.",
        "",
        "Hard constraints:",
        "- Do not modify any existing public theorem, lemma, or corollary name, statement, binder, assumption, or conclusion.",
        "- Do not weaken mathematics or replace a proof with sorry/admit/native_decide/Lean.ofReduceBool/global axiom/unsafe.",
        "- Do not remove or rewrite imports.",
        "- You may change proof bodies and add small private helper lemmas immediately before their use.",
        "- Use current Mathlib APIs and explicit type annotations/change/ext/simpa only when definitional equality is insufficient.",
        "- Fix common roots rather than hard-coding downstream goals.",
        "- Touch only the error clusters shown below.",
        "",
        f"Iteration: {iteration}",
        f"Current source SHA-256: {metric.source_sha256}",
        f"Current error headers: {metric.errors}",
        f"Current first error line: {metric.first_line}",
        "",
    ]
    for index, match in enumerate(selected, 1):
        line = int(match.group("line"))
        col = int(match.group("col"))
        parts.extend(
            [
                f"## Error {index} at {line}:{col}",
                "Compiler block:",
                "```text",
                error_block(log, match),
                "```",
                "Source context:",
                "```lean",
                source_context(source_lines, line),
                "```",
                "",
            ]
        )
    return "\n".join(parts)


def query_model(prompt: str, iteration: int) -> tuple[str, str]:
    if not TOKEN:
        raise RuntimeError("GITHUB_TOKEN is unavailable")
    endpoint = "https://models.github.ai/inference/chat/completions"
    errors: list[str] = []
    for model in MODELS:
        payload = {
            "model": model,
            "temperature": 0.1,
            "max_tokens": 12000,
            "messages": [
                {
                    "role": "system",
                    "content": "You are an expert Lean/mathlib maintainer. Produce a minimal, kernel-checkable unified diff only.",
                },
                {"role": "user", "content": prompt},
            ],
        }
        request = urllib.request.Request(
            endpoint,
            data=json.dumps(payload).encode("utf-8"),
            headers={
                "Authorization": f"Bearer {TOKEN}",
                "Content-Type": "application/json",
                "Accept": "application/vnd.github+json",
                "X-GitHub-Api-Version": "2022-11-28",
                "User-Agent": "primality-sheaf-fa377-agent",
            },
            method="POST",
        )
        try:
            with urllib.request.urlopen(request, timeout=300) as response:
                body = json.load(response)
            content = body["choices"][0]["message"]["content"]
            (STATE_DIR / f"iteration-{iteration:03d}-{model.replace('/', '-')}.txt").write_text(
                content, encoding="utf-8"
            )
            return model, content
        except (urllib.error.HTTPError, urllib.error.URLError, TimeoutError, KeyError) as exc:
            detail = getattr(exc, "read", lambda: b"")()
            errors.append(f"{model}: {exc}; {detail[:1000]!r}")
            time.sleep(3)
    raise RuntimeError("all GitHub Models calls failed: " + " | ".join(errors))


def extract_patch(text: str) -> str:
    starts = [position for position in (text.find("diff --git "), text.find("--- a/")) if position >= 0]
    if not starts:
        raise ValueError("model response did not contain a unified diff")
    patch = text[min(starts) :]
    fence = patch.find("\n```")
    if fence >= 0:
        patch = patch[:fence] + "\n"
    patch = re.sub(
        r"(?m)^(---|\+\+\+) [ab]/[^\n]*Mock2_FunctionalAnalysis\.lean$",
        lambda match: (
            f"{match.group(1)} "
            f"{'a' if match.group(1) == '---' else 'b'}"
            "/PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean"
        ),
        patch,
    )
    return patch


def patch_is_safe(patch: str) -> tuple[bool, str]:
    if FORBIDDEN_ADDITION.search(patch):
        return False, "forbidden proof escape added"
    if PUBLIC_HEADER_CHANGE.search(patch):
        return False, "public theorem/lemma/corollary header changed"
    if IMPORT_CHANGE.search(patch):
        return False, "import changed"
    if "PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean" not in patch:
        return False, "patch targets the wrong file"
    return True, "ok"


def try_patch(patch: str, iteration: int, old_metric: Metric) -> tuple[bool, Metric, str]:
    original = TARGET.read_bytes()
    patch_path = STATE_DIR / f"iteration-{iteration:03d}.patch"
    patch_path.write_text(patch, encoding="utf-8")
    check = run(["git", "apply", "--check", str(patch_path)])
    if check.returncode != 0:
        return False, old_metric, "git apply --check failed: " + check.stdout[-4000:]
    applied = run(["git", "apply", "--whitespace=nowarn", str(patch_path)])
    if applied.returncode != 0:
        TARGET.write_bytes(original)
        return False, old_metric, "git apply failed: " + applied.stdout[-4000:]
    new_metric, new_log = compile_source(f"iteration-{iteration:03d}")
    if new_metric.better_than(old_metric):
        shutil.copy2(TARGET, STATE_DIR / "best-source.lean")
        (STATE_DIR / "best-metric.json").write_text(
            json.dumps(new_metric.__dict__, indent=2), encoding="utf-8"
        )
        return True, new_metric, new_log
    TARGET.write_bytes(original)
    return False, old_metric, (
        f"candidate did not improve: old={old_metric.__dict__} new={new_metric.__dict__}"
    )


def remove_target_artifacts(stem: str) -> None:
    candidates = [
        ROOT / "PrimalitySheafVerification" / f"{stem}.olean",
        ROOT / "PrimalitySheafVerification" / f"{stem}.ilean",
        ROOT / ".lake" / "build" / "lib" / "lean" / "PrimalitySheafVerification" / f"{stem}.olean",
        ROOT / ".lake" / "build" / "lib" / "lean" / "PrimalitySheafVerification" / f"{stem}.ilean",
    ]
    for path in candidates:
        path.unlink(missing_ok=True)


def compile_module_twice(path: Path, label: str) -> None:
    stem = path.stem
    for run_number in (1, 2):
        remove_target_artifacts(stem)
        proc = run(
            ["lake", "env", "lean", "-DmaxErrors=200", str(path.relative_to(ROOT))],
            timeout=2400,
        )
        (STATE_DIR / f"{label}-run{run_number}.log").write_text(proc.stdout, encoding="utf-8")
        if proc.returncode != 0 or "error:" in proc.stdout:
            raise RuntimeError(
                f"{label} run {run_number} failed with exit {proc.returncode}"
            )


def verify_required_order() -> None:
    compile_module_twice(TARGET, "Mock2_FunctionalAnalysis")
    integrated = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis_Integrated.lean"
    if not integrated.exists():
        raise RuntimeError("Mock2_FunctionalAnalysis_Integrated.lean is missing")
    compile_module_twice(integrated, "Mock2_FunctionalAnalysis_Integrated")
    mock3_files = sorted((ROOT / "PrimalitySheafVerification").glob("Mock3*.lean"))
    for path in mock3_files:
        compile_module_twice(path, path.stem)
    qym = ROOT / "PrimalitySheafVerification" / "QYM.lean"
    if not qym.exists():
        raise RuntimeError("QYM.lean is missing")
    compile_module_twice(qym, "QYM")
    (STATE_DIR / "ALL_REQUIRED_TARGETS_2X_PASS").write_text(
        "Mock2_FunctionalAnalysis=PASSx2\n"
        "Mock2_FunctionalAnalysis_Integrated=PASSx2\n"
        + "".join(f"{path.stem}=PASSx2\n" for path in mock3_files)
        + "QYM=PASSx2\n",
        encoding="utf-8",
    )


def load_state() -> dict[str, object]:
    if not STATE_FILE.exists():
        return {"total_iterations": 0, "accepted": 0, "complete": False}
    return json.loads(STATE_FILE.read_text(encoding="utf-8"))


def save_state(state: dict[str, object]) -> None:
    STATE_FILE.write_text(json.dumps(state, indent=2, sort_keys=True), encoding="utf-8")


def main() -> int:
    STATE_DIR.mkdir(parents=True, exist_ok=True)
    state = load_state()
    if state.get("complete"):
        print("[agent] already complete")
        return 0
    if not (STATE_DIR / "materialized-pass376").exists():
        reconstruct_pass376_source()
        (STATE_DIR / "materialized-pass376").write_text(sha256_file(TARGET), encoding="utf-8")
    current_metric, current_log = compile_source("baseline")
    print(f"[agent] baseline={current_metric}")
    if current_metric.exit_code == 0 and current_metric.errors == 0:
        verify_required_order()
        state.update({"complete": True, "final_sha256": sha256_file(TARGET)})
        save_state(state)
        return 0
    for local_iteration in range(1, MAX_ITERATIONS + 1):
        total = int(state.get("total_iterations", 0)) + 1
        if total > MAX_TOTAL_ITERATIONS:
            raise RuntimeError("maximum total iteration safety bound reached")
        state["total_iterations"] = total
        prompt = build_prompt(current_metric, current_log, total)
        (STATE_DIR / f"iteration-{total:03d}-prompt.md").write_text(prompt, encoding="utf-8")
        try:
            model, response = query_model(prompt, total)
            patch = extract_patch(response)
            safe, reason = patch_is_safe(patch)
            if not safe:
                raise ValueError(reason)
            accepted, candidate_metric, detail = try_patch(patch, total, current_metric)
            (STATE_DIR / f"iteration-{total:03d}-result.txt").write_text(
                f"model={model}\naccepted={accepted}\n{detail}\n", encoding="utf-8"
            )
            if accepted:
                current_metric = candidate_metric
                current_log = (STATE_DIR / f"iteration-{total:03d}.log").read_text(
                    encoding="utf-8", errors="replace"
                )
                state["accepted"] = int(state.get("accepted", 0)) + 1
                state["best_metric"] = current_metric.__dict__
                save_state(state)
                print(f"[agent] accepted iteration {total}: {current_metric}")
                if current_metric.exit_code == 0 and current_metric.errors == 0:
                    verify_required_order()
                    state.update({"complete": True, "final_sha256": sha256_file(TARGET)})
                    save_state(state)
                    return 0
            else:
                print(f"[agent] rejected iteration {total}: {detail}")
        except Exception as exc:  # preserve evidence and allow the next model/iteration
            (STATE_DIR / f"iteration-{total:03d}-exception.txt").write_text(
                repr(exc), encoding="utf-8"
            )
            print(f"[agent] iteration {total} exception: {exc}")
        save_state(state)
    # A partial improvement is useful evidence but not a PASS.
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
