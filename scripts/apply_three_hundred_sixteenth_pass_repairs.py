from __future__ import annotations

from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_Advanced.lean"


def replace_idempotent(text: str, old: str, new: str, label: str) -> str:
    old_count = text.count(old)
    new_count = text.count(new)
    print(f"{label}: old={old_count} new={new_count}")
    if old_count == 1 and new_count == 0:
        return text.replace(old, new)
    if old_count == 0 and new_count == 1:
        print(f"{label}: already applied")
        return text
    raise RuntimeError(
        f"{label}: expected exactly one unrepaired or repaired occurrence, "
        f"found old={old_count}, new={new_count}"
    )


def compile_target(label: str) -> tuple[int, str]:
    outdir = Path(tempfile.gettempdir()) / "mock2-advanced-pass316-auto"
    outdir.mkdir(parents=True, exist_ok=True)
    olean = outdir / f"{label}.olean"
    ilean = outdir / f"{label}.ilean"
    for path in (olean, ilean, Path(str(olean) + ".private")):
        path.unlink(missing_ok=True)
    proc = subprocess.run(
        [
            "lake",
            "env",
            "lean",
            str(TARGET.relative_to(ROOT)),
            "-o",
            str(olean),
            "-i",
            str(ilean),
        ],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    log_path = outdir / f"{label}.log"
    log_path.write_text(proc.stdout, encoding="utf-8")
    errors = proc.stdout.count("error:")
    print(f"[{label}] exit={proc.returncode} errors={errors} log={log_path}")
    return proc.returncode, proc.stdout


def namespace_span(text: str, namespace: str) -> tuple[int, int]:
    start_token = f"namespace {namespace}"
    start = text.find(start_token)
    if start < 0:
        raise RuntimeError(f"cannot find {start_token!r}")
    end_token = f"end {namespace}"
    end = text.find(end_token, start)
    if end < 0:
        raise RuntimeError(f"cannot find {end_token!r}")
    return start, end + len(end_token)


def diagnostic_block(log: str, declaration: str) -> str:
    needle = f"declaration `{declaration}` contains universe level metavariables"
    start = log.find(needle)
    if start < 0:
        return ""
    next_error = log.find("\nPrimalitySheafVerification/Mock2_Advanced.lean:", start + len(needle))
    if next_error < 0:
        next_error = min(len(log), start + 16000)
    return log[start:next_error]


def unspecialized_names(fragment: str) -> list[str]:
    names: list[str] = []
    pattern = re.compile(r"@([A-Za-z_][A-Za-z0-9_'.]*)(?!\.\{)")
    for match in pattern.finditer(fragment):
        name = match.group(1)
        if name not in names:
            names.append(name)
    return names


def specialize_once_in_span(
    text: str,
    span: tuple[int, int],
    name: str,
    arity: int,
) -> str | None:
    start, end = span
    fragment = text[start:end]
    pattern = re.compile(rf"@{re.escape(name)}(?!\.\{{)")
    matches = list(pattern.finditer(fragment))
    if len(matches) != 1:
        return None
    suffix = ".{" + ", ".join("0" for _ in range(arity)) + "}"
    pos = start + matches[0].end()
    return text[:pos] + suffix + text[pos:]


def target_error_count(log: str, declaration: str) -> int:
    return log.count(f"declaration `{declaration}` contains universe level metavariables")


def repair_declaration(
    text: str,
    namespace: str,
    declaration: str,
    initial_log: str,
    attempt_seed: int,
) -> tuple[str, str, int]:
    if target_error_count(initial_log, declaration) == 0:
        return text, initial_log, attempt_seed

    span = namespace_span(text, namespace)
    block = diagnostic_block(initial_log, declaration)
    fragment = text[span[0]:span[1]]
    all_names = unspecialized_names(fragment)
    mentioned = [name for name in all_names if name in block]
    candidates = mentioned + [name for name in all_names if name not in mentioned]

    print(f"[{declaration}] diagnostic candidates={mentioned}")
    print(f"[{declaration}] fallback candidates={len(candidates) - len(mentioned)}")

    baseline_total = initial_log.count("error:")
    baseline_target = target_error_count(initial_log, declaration)

    for name in candidates:
        for arity in range(1, 9):
            trial = specialize_once_in_span(text, span, name, arity)
            if trial is None:
                continue
            TARGET.write_text(trial, encoding="utf-8")
            label = f"try-{attempt_seed:03d}-{namespace}-{name.split('.')[-1]}-u{arity}"
            attempt_seed += 1
            code, trial_log = compile_target(label)
            trial_total = trial_log.count("error:")
            trial_target = target_error_count(trial_log, declaration)
            print(
                f"[{declaration}] {name}.{{{'0,' * (arity - 1)}0}} "
                f"target={trial_target} total={trial_total}"
            )
            improved = (
                code == 0
                or trial_target < baseline_target
                or (trial_target == 0 and trial_total < baseline_total)
            )
            if improved:
                print(f"[{declaration}] accepted {name} with {arity} universe argument(s)")
                return trial, trial_log, attempt_seed
            TARGET.write_text(text, encoding="utf-8")

    TARGET.write_text(text, encoding="utf-8")
    raise RuntimeError(
        f"unable to close universe metavariables in {declaration}; "
        f"see /tmp/mock2-advanced-pass316-auto logs"
    )


def main() -> int:
    text = TARGET.read_text(encoding="utf-8")

    # Previously isolated universe specializations.  Keep them here so the
    # pass-316 path is self-contained and idempotent.
    replacements = [
        (
            "  | Sum.inr (Sum.inl c) => UnnumberedFormulaLedger.ClaimEvidence c\n",
            "  | Sum.inr (Sum.inl c) => UnnumberedFormulaLedger.ClaimEvidence.{0} c\n",
            "Mock2 Advanced specialize unnumbered checklist evidence universe",
        ),
        (
            "    · exact UnnumberedFormulaLedger.claimEvidence c\n",
            "    · exact UnnumberedFormulaLedger.claimEvidence.{0} c\n",
            "Mock2 Advanced specialize unnumbered checklist proof universe",
        ),
        (
            "      KernelEvidence (@UnnumberedFormulaLedger.section7C_quantitativeTailBound_proved)\n",
            "      KernelEvidence (@UnnumberedFormulaLedger.section7C_quantitativeTailBound_proved.{0})\n",
            "Mock2 Advanced Section7 quantitative-tail evidence universe",
        ),
        (
            "      KernelEvidence (@p07_typedCurvature_correctedAndProved)\n",
            "      KernelEvidence (@p07_typedCurvature_correctedAndProved.{0, 0, 0, 0})\n",
            "Mock2 Advanced P0 typed-curvature evidence universes",
        ),
        (
            "      KernelEvidence\n        (@UnnumberedFormulaLedger.section7F_uniformMajorantConvergence_proved)\n",
            "      KernelEvidence\n        (@UnnumberedFormulaLedger.section7F_uniformMajorantConvergence_proved.{0, 0})\n",
            "Mock2 Advanced Section7 uniform-majorant evidence universes",
        ),
        (
            "      KernelEvidence (@p07_automorphicSeriesLimit_correctedAndProved)\n",
            "      KernelEvidence (@p07_automorphicSeriesLimit_correctedAndProved.{0})\n",
            "Mock2 Advanced P0 automorphic-series evidence universe",
        ),
    ]
    for old, new, label in replacements:
        text = replace_idempotent(text, old, new, label)
    TARGET.write_text(text, encoding="utf-8")

    code, log = compile_target("initial")
    if code == 0:
        print("[pass316] Mock2_Advanced candidate already compiles")
        return 0

    attempt = 1
    targets = [
        (
            "Section7WorkaroundLedger",
            "Mock2Adv.Section7WorkaroundLedger.RequirementEvidence",
        ),
        (
            "P0RepairLedger",
            "Mock2Adv.P0RepairLedger.RequirementEvidence",
        ),
    ]
    for namespace, declaration in targets:
        text, log, attempt = repair_declaration(
            text, namespace, declaration, log, attempt
        )
        TARGET.write_text(text, encoding="utf-8")
        if log.count("error:") == 0:
            break

    final_code, final_log = compile_target("final")
    if final_code != 0 or "error:" in final_log:
        raise RuntimeError(
            "pass316 automatic universe specialization did not produce a clean compile"
        )

    print("[pass316] Mock2_Advanced universe frontier compiles cleanly")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())