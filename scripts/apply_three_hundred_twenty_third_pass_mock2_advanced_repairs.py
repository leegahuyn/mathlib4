from __future__ import annotations

from dataclasses import dataclass
from hashlib import sha256
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_Advanced.lean"
PROBE = ROOT / "PrimalitySheafVerification" / "_Pass323UniverseProbe.lean"
LOG_ROOT = Path(tempfile.gettempdir()) / "mock2-advanced-pass323"
OUT_ROOT = LOG_ROOT / "objects"


@dataclass(frozen=True)
class TargetDecl:
    namespace: str
    short_name: str
    full_name: str


TARGET_DECLS = (
    TargetDecl(
        "Section7WorkaroundLedger",
        "RequirementEvidence",
        "Mock2Adv.Section7WorkaroundLedger.RequirementEvidence",
    ),
    TargetDecl(
        "P0RepairLedger",
        "RequirementEvidence",
        "Mock2Adv.P0RepairLedger.RequirementEvidence",
    ),
)

KNOWN_REPLACEMENTS = (
    (
        "  | Sum.inr (Sum.inl c) => UnnumberedFormulaLedger.ClaimEvidence c\n",
        "  | Sum.inr (Sum.inl c) => UnnumberedFormulaLedger.ClaimEvidence.{0} c\n",
        "unnumbered checklist evidence universe",
    ),
    (
        "    · exact UnnumberedFormulaLedger.claimEvidence c\n",
        "    · exact UnnumberedFormulaLedger.claimEvidence.{0} c\n",
        "unnumbered checklist proof universe",
    ),
    (
        "      KernelEvidence (@UnnumberedFormulaLedger.section7C_quantitativeTailBound_proved)\n",
        "      KernelEvidence (@UnnumberedFormulaLedger.section7C_quantitativeTailBound_proved.{0})\n",
        "Section7 quantitative-tail evidence universe",
    ),
    (
        "      KernelEvidence (@p07_typedCurvature_correctedAndProved)\n",
        "      KernelEvidence (@p07_typedCurvature_correctedAndProved.{0, 0, 0, 0})\n",
        "P0 typed-curvature evidence universes",
    ),
    (
        "      KernelEvidence\n        (@UnnumberedFormulaLedger.section7F_uniformMajorantConvergence_proved)\n",
        "      KernelEvidence\n        (@UnnumberedFormulaLedger.section7F_uniformMajorantConvergence_proved.{0, 0})\n",
        "Section7 uniform-majorant evidence universes",
    ),
    (
        "      KernelEvidence (@p07_automorphicSeriesLimit_correctedAndProved)\n",
        "      KernelEvidence (@p07_automorphicSeriesLimit_correctedAndProved.{0})\n",
        "P0 automorphic-series evidence universe",
    ),
)


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
        f"{label}: expected one unrepaired or repaired occurrence, "
        f"found old={old_count}, new={new_count}"
    )


def run_lean(path: Path, label: str) -> tuple[int, str]:
    LOG_ROOT.mkdir(parents=True, exist_ok=True)
    OUT_ROOT.mkdir(parents=True, exist_ok=True)
    safe = re.sub(r"[^A-Za-z0-9_.-]+", "-", label)
    olean = OUT_ROOT / f"{safe}.olean"
    ilean = OUT_ROOT / f"{safe}.ilean"
    for artifact in (olean, ilean, Path(str(olean) + ".private")):
        artifact.unlink(missing_ok=True)
    proc = subprocess.run(
        [
            "lake",
            "env",
            "lean",
            str(path.relative_to(ROOT)),
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
    (LOG_ROOT / f"{safe}.log").write_text(proc.stdout, encoding="utf-8")
    print(f"[{label}] exit={proc.returncode} errors={proc.stdout.count('error:')}")
    return proc.returncode, proc.stdout


def compile_target(label: str) -> tuple[int, str]:
    return run_lean(TARGET, label)


def namespace_span(text: str, namespace: str) -> tuple[int, int]:
    start = text.find(f"namespace {namespace}")
    if start < 0:
        raise RuntimeError(f"namespace {namespace} not found")
    end_token = f"end {namespace}"
    end = text.find(end_token, start)
    if end < 0:
        raise RuntimeError(f"end {namespace} not found")
    return start, end + len(end_token)


def declaration_span(text: str, target: TargetDecl) -> tuple[int, int]:
    ns_start, ns_end = namespace_span(text, target.namespace)
    fragment = text[ns_start:ns_end]
    header = re.search(
        rf"(?m)^(?:noncomputable\s+)?(?:def|abbrev|theorem)\s+"
        rf"{re.escape(target.short_name)}\b",
        fragment,
    )
    if header is None:
        raise RuntimeError(f"declaration {target.full_name} not found")
    start = ns_start + header.start()
    search_from = ns_start + header.end()
    following = re.search(
        r"(?m)^\s*(?:noncomputable\s+)?(?:def|abbrev|theorem|lemma|instance|"
        r"structure|inductive|class)\s+[A-Za-z_]",
        text[search_from:ns_end],
    )
    end = ns_end if following is None else search_from + following.start()
    return start, end


def declaration_error_count(log: str, target: TargetDecl) -> int:
    return log.count(
        f"declaration `{target.full_name}` contains universe level metavariables"
    )


def diagnostic_block(log: str, target: TargetDecl) -> str:
    needle = (
        f"declaration `{target.full_name}` contains universe level metavariables"
    )
    start = log.find(needle)
    if start < 0:
        return ""
    next_error = log.find(
        "\nPrimalitySheafVerification/Mock2_Advanced.lean:",
        start + len(needle),
    )
    if next_error < 0:
        next_error = min(len(log), start + 30000)
    return log[start:next_error]


def unresolved_constant_names(source: str, diagnostic: str) -> list[str]:
    names: list[str] = []

    def add(name: str) -> None:
        if name and name not in names:
            names.append(name)

    # Lean's printed expression is the strongest signal: constants carrying
    # an unresolved universe level are listed first.
    for match in re.finditer(
        r"([A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)"
        r"\.\{[^}\n]*\?u[^}\n]*\}",
        diagnostic,
    ):
        add(match.group(1))

    for match in re.finditer(
        r"@([A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)",
        diagnostic,
    ):
        add(match.group(1))

    # Then include explicit constants from the source declaration itself.
    for match in re.finditer(
        r"@([A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)",
        source,
    ):
        if not source.startswith(".{", match.end()):
            add(match.group(1))

    # Some constructors are printed without `@` even though their universe is
    # implicit.  They are probed only when they occur in both source and error.
    for name in ("KernelEvidence", "ClaimEvidence", "Nonempty", "PUnit", "ULift", "PLift"):
        if name in source and name in diagnostic:
            add(name)

    return names


def source_occurrence_names(source: str, requested: str) -> list[str]:
    variants = [requested]
    short = requested.rsplit(".", 1)[-1]
    if short != requested:
        variants.append(short)
    return variants


def token_matches(source: str, name: str) -> list[re.Match[str]]:
    pattern = re.compile(
        rf"(?<![A-Za-z0-9_'.]){re.escape(name)}(?=$|[^A-Za-z0-9_'.])"
    )
    return [
        match
        for match in pattern.finditer(source)
        if not source.startswith(".{", match.end())
    ]


def write_probe(prefix: str, name: str, explicit_arity: int | None) -> None:
    if explicit_arity is None:
        check = f"set_option pp.universes true in\n#check @{name}\n"
    else:
        levels = ", ".join(["0"] * explicit_arity)
        check = f"#check @{name}.{{{levels}}}\n"
    PROBE.write_text(prefix + "\n\n" + check, encoding="utf-8")


def parse_printed_arity(output: str, name: str) -> int | None:
    short = re.escape(name.rsplit(".", 1)[-1])
    qualified = re.escape(name)
    patterns = (
        rf"(?:{qualified}|{short})\.\{{([^}}]*)\}}",
        rf"@(?:{qualified}|{short})\.\{{([^}}]*)\}}",
    )
    for pattern in patterns:
        matches = re.findall(pattern, output)
        if matches:
            levels = matches[-1].strip()
            if not levels:
                return 0
            return len([part for part in levels.split(",") if part.strip()])
    return None


def determine_arity(prefix: str, name: str, cache: dict[tuple[str, str], int]) -> int:
    prefix_key = sha256(prefix.encode("utf-8")).hexdigest()
    key = (prefix_key, name)
    if key in cache:
        return cache[key]

    write_probe(prefix, name, None)
    code, output = run_lean(PROBE, f"probe-print-{name}")
    printed = parse_printed_arity(output, name)
    if code == 0 and printed is not None:
        cache[key] = printed
        print(f"[arity] {name}: {printed} (pretty-printer)")
        return printed

    # Fallback: ask Lean directly which explicit universe arity elaborates.
    for arity in range(1, 17):
        write_probe(prefix, name, arity)
        probe_code, _ = run_lean(PROBE, f"probe-arity-{name}-{arity}")
        if probe_code == 0:
            cache[key] = arity
            print(f"[arity] {name}: {arity} (elaboration probe)")
            return arity

    raise RuntimeError(f"could not determine universe arity for {name}")


def specialize_all_occurrences(
    text: str,
    span: tuple[int, int],
    requested_name: str,
    arity: int,
) -> tuple[str, int]:
    if arity == 0:
        return text, 0
    start, end = span
    fragment = text[start:end]
    chosen_name: str | None = None
    matches: list[re.Match[str]] = []
    for variant in source_occurrence_names(fragment, requested_name):
        candidate_matches = token_matches(fragment, variant)
        if candidate_matches:
            chosen_name = variant
            matches = candidate_matches
            break
    if chosen_name is None:
        return text, 0

    suffix = ".{" + ", ".join(["0"] * arity) + "}"
    pieces: list[str] = []
    cursor = 0
    for match in matches:
        pieces.append(fragment[cursor:match.end()])
        pieces.append(suffix)
        cursor = match.end()
    pieces.append(fragment[cursor:])
    new_fragment = "".join(pieces)
    return text[:start] + new_fragment + text[end:], len(matches)


def repair_one(
    text: str,
    log: str,
    target: TargetDecl,
    arity_cache: dict[tuple[str, str], int],
) -> tuple[str, str]:
    rounds = 0
    while declaration_error_count(log, target):
        rounds += 1
        if rounds > 12:
            raise RuntimeError(f"too many repair rounds for {target.full_name}")

        start, end = declaration_span(text, target)
        source = text[start:end]
        diagnostic = diagnostic_block(log, target)
        names = unresolved_constant_names(source, diagnostic)
        if not names:
            raise RuntimeError(f"no universe-bearing constants found for {target.full_name}")

        prefix = text[:start]
        print(f"[{target.full_name}] round={rounds} candidates={names}")
        changed = 0
        for name in names:
            try:
                arity = determine_arity(prefix, name, arity_cache)
            except RuntimeError as exc:
                print(f"[{target.full_name}] probe skipped for {name}: {exc}")
                continue
            current_span = declaration_span(text, target)
            text, count = specialize_all_occurrences(text, current_span, name, arity)
            if count:
                print(
                    f"[{target.full_name}] specialized {count} occurrence(s) "
                    f"of {name} at arity {arity}"
                )
                changed += count

        if changed == 0:
            raise RuntimeError(f"no source occurrence changed for {target.full_name}")

        TARGET.write_text(text, encoding="utf-8")
        code, new_log = compile_target(f"{target.namespace}-round{rounds}")
        if code == 0:
            return text, new_log
        if new_log == log:
            raise RuntimeError(f"universe repair made no diagnostic progress for {target.full_name}")
        log = new_log

    return text, log


def main() -> int:
    text = TARGET.read_text(encoding="utf-8")
    for old, new, label in KNOWN_REPLACEMENTS:
        text = replace_idempotent(text, old, new, label)
    TARGET.write_text(text, encoding="utf-8")

    code, log = compile_target("initial")
    if code == 0:
        print("[pass323] Mock2_Advanced candidate already compiles")
        return 0

    cache: dict[tuple[str, str], int] = {}
    try:
        for target in TARGET_DECLS:
            text, log = repair_one(text, log, target, cache)
            TARGET.write_text(text, encoding="utf-8")

        final_code, final_log = compile_target("final")
        if final_code != 0 or "error:" in final_log:
            raise RuntimeError("pass323 did not produce a clean Mock2_Advanced compile")
        print("[pass323] Mock2_Advanced compiles cleanly")
        return 0
    finally:
        PROBE.unlink(missing_ok=True)


if __name__ == "__main__":
    raise SystemExit(main())