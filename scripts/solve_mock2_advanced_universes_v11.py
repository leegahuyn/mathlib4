from __future__ import annotations

import os
import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_Advanced.lean"
OUTDIR = ROOT / ".lake" / "build" / "lib" / "lean" / "PrimalitySheafVerification"
LOGROOT = Path(os.environ.get("MOCK2_ADVANCED_SOLVER_LOGDIR", "/tmp/mock2-advanced-solver-v11"))
TARGET_DECLARATIONS = (
    "Mock2Adv.Section7WorkaroundLedger.RequirementEvidence",
    "Mock2Adv.P0RepairLedger.RequirementEvidence",
)
DECLARATION_KINDS = {
    "theorem",
    "lemma",
    "def",
    "abbrev",
    "opaque",
    "instance",
    "structure",
    "class",
    "inductive",
}
DECLARATION_PREFIXES = {"noncomputable", "private", "protected", "local", "partial"}
KEYWORDS = {
    "match",
    "with",
    "fun",
    "if",
    "then",
    "else",
    "let",
    "in",
    "by",
    "where",
    "do",
    "return",
    "exact",
    "true",
    "false",
    "Prop",
    "Sort",
    "Type",
    "namespace",
    "section",
    "end",
    "open",
    "universe",
    "variable",
}


@dataclass(frozen=True)
class Region:
    declaration: str
    start: int
    end: int
    namespaces: tuple[str, ...]


@dataclass(frozen=True)
class Candidate:
    ident: str
    region_index: int
    spelling: str


def run(command: list[str], log: Path | None = None) -> int:
    environment = dict(os.environ)
    environment["PATH"] = str(Path.home() / ".elan" / "bin") + ":" + environment.get("PATH", "")
    if log is None:
        result = subprocess.run(command, cwd=ROOT, env=environment, check=False)
    else:
        log.parent.mkdir(parents=True, exist_ok=True)
        with log.open("w", encoding="utf-8") as output:
            result = subprocess.run(
                command,
                cwd=ROOT,
                env=environment,
                stdout=output,
                stderr=subprocess.STDOUT,
                check=False,
            )
    return result.returncode


def compile_source(path: Path, label: str) -> tuple[int, Path]:
    log = LOGROOT / "logs" / f"{label}.log"
    OUTDIR.mkdir(parents=True, exist_ok=True)
    module = path.stem
    for suffix in (".olean", ".ilean", ".olean.private"):
        (OUTDIR / f"{module}{suffix}").unlink(missing_ok=True)
    exit_code = run(
        [
            "lake",
            "env",
            "lean",
            str(path.relative_to(ROOT)),
            "-o",
            str(OUTDIR / f"{module}.olean"),
            "-i",
            str(OUTDIR / f"{module}.ilean"),
        ],
        log=log,
    )
    return exit_code, log


def namespace_stack(lines: list[str], stop: int) -> tuple[str, ...]:
    blocks: list[tuple[str, int]] = []
    namespaces: list[str] = []
    for line in lines[:stop]:
        stripped = line.strip()
        match = re.match(r"^namespace\s+([A-Za-z_][A-Za-z0-9_'.]*)\s*$", stripped)
        if match:
            parts = match.group(1).split(".")
            namespaces.extend(parts)
            blocks.append(("namespace", len(parts)))
            continue
        if re.match(r"^section(?:\s+[A-Za-z_][A-Za-z0-9_']*)?\s*$", stripped):
            blocks.append(("section", 0))
            continue
        if re.match(r"^end(?:\s+[A-Za-z_][A-Za-z0-9_'.]*)?\s*$", stripped):
            if blocks:
                kind, width = blocks.pop()
                if kind == "namespace" and width:
                    del namespaces[-width:]
    return tuple(namespaces)


def starts_declaration(stripped: str) -> bool:
    if not stripped or stripped.startswith(("--", "/-", "@[", "|")):
        return False
    tokens = stripped.replace("(", " ").replace(":", " ").split()
    index = 0
    while index < len(tokens) and tokens[index] in DECLARATION_PREFIXES:
        index += 1
    return index < len(tokens) and tokens[index] in DECLARATION_KINDS


def target_error_lines(log: str) -> dict[str, int]:
    result: dict[str, int] = {}
    for declaration in TARGET_DECLARATIONS:
        pattern = re.compile(
            rf"Mock2_Advanced\.lean:(\d+):\d+: error: declaration "
            rf"`{re.escape(declaration)}` contains universe level metavariables"
        )
        match = pattern.search(log)
        if match:
            result[declaration] = int(match.group(1)) - 1
    return result


def find_region(lines: list[str], declaration: str, error_line: int) -> Region:
    final_name = declaration.rsplit(".", 1)[-1]
    start = error_line
    for index in range(error_line, max(-1, error_line - 250), -1):
        line = lines[index]
        if final_name in line and re.search(
            r"\b(?:def|abbrev|opaque)\s+" + re.escape(final_name) + r"\b", line
        ):
            start = index
            break
    indentation = len(lines[start]) - len(lines[start].lstrip(" "))
    end = min(len(lines), start + 500)
    for index in range(start + 1, min(len(lines), start + 500)):
        stripped = lines[index].strip()
        if not stripped:
            continue
        current_indentation = len(lines[index]) - len(lines[index].lstrip(" "))
        if current_indentation <= indentation and (
            starts_declaration(stripped) or stripped.startswith("end ")
        ):
            end = index
            break
    return Region(
        declaration=declaration,
        start=start,
        end=end,
        namespaces=namespace_stack(lines, start),
    )


def collect_candidates(
    lines: list[str], regions: list[Region], include_bare: bool
) -> list[Candidate]:
    values: list[Candidate] = []
    seen: set[tuple[int, str]] = set()
    explicit = re.compile(
        r"@([A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)"
        r"(?![A-Za-z0-9_']|\.\{)"
    )
    qualified = re.compile(
        r"(?<![A-Za-z0-9_'.])"
        r"([A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)+)"
        r"(?![A-Za-z0-9_']|\.\{)"
    )
    theorem_like = re.compile(
        r"(?<![A-Za-z0-9_'.])"
        r"([A-Za-z_][A-Za-z0-9_']*"
        r"(?:_proved|_correctedAndProved|claimEvidence|KernelEvidence))"
        r"(?![A-Za-z0-9_']|\.\{)"
    )
    for region_index, region in enumerate(regions):
        block = "\n".join(lines[region.start : region.end])
        for match in explicit.finditer(block):
            spelling = match.group(1)
            key = (region_index, spelling)
            if key not in seen:
                seen.add(key)
                values.append(Candidate("", region_index, spelling))
        if include_bare:
            for pattern in (qualified, theorem_like):
                for match in pattern.finditer(block):
                    spelling = match.group(1)
                    if spelling in KEYWORDS or spelling.endswith("RequirementEvidence"):
                        continue
                    key = (region_index, spelling)
                    if key not in seen:
                        seen.add(key)
                        values.append(Candidate("", region_index, spelling))
            for special in ("KernelEvidence", "PUnit", "ULift", "PLift", "Nonempty"):
                if re.search(
                    rf"(?<![A-Za-z0-9_'.]){special}"
                    rf"(?![A-Za-z0-9_']|\.\{{)",
                    block,
                ):
                    key = (region_index, special)
                    if key not in seen:
                        seen.add(key)
                        values.append(Candidate("", region_index, special))
    return [
        Candidate(f"Q{index:04d}", candidate.region_index, candidate.spelling)
        for index, candidate in enumerate(values)
    ]


def make_probe(
    source: str,
    regions: list[Region],
    candidates: list[Candidate],
    path: Path,
) -> None:
    output = [source, "", "set_option pp.universes true"]
    for region_index, region in enumerate(regions):
        opened: list[str] = []
        for namespace in region.namespaces:
            output.append(f"namespace {namespace}")
            opened.append(namespace)
        for candidate in candidates:
            if candidate.region_index != region_index:
                continue
            output.append(f'#check "BEGIN|{candidate.ident}"')
            output.append(f"#check @{candidate.spelling}")
            output.append(f'#check "END|{candidate.ident}"')
        for namespace in reversed(opened):
            output.append(f"end {namespace}")
    output.append("")
    path.write_text("\n".join(output), encoding="utf-8")


def split_levels(raw: str) -> list[str]:
    values: list[str] = []
    start = 0
    paren = bracket = brace = 0
    for index, character in enumerate(raw):
        if character == "(":
            paren += 1
        elif character == ")":
            paren -= 1
        elif character == "[":
            bracket += 1
        elif character == "]":
            bracket -= 1
        elif character == "{":
            brace += 1
        elif character == "}":
            brace -= 1
        elif character == "," and paren == bracket == brace == 0:
            values.append(raw[start:index].strip())
            start = index + 1
    values.append(raw[start:].strip())
    return [value for value in values if value]


def parse_arities(log: str, candidates: list[Candidate]) -> dict[str, int]:
    result: dict[str, int] = {}
    constant = re.compile(
        r"@?[A-Za-z_][A-Za-z0-9_']*"
        r"(?:\.[A-Za-z_][A-Za-z0-9_']*)*\.\{([^}\n]+)\}"
    )
    for candidate in candidates:
        begin = f"BEGIN|{candidate.ident}"
        end = f"END|{candidate.ident}"
        begin_at = log.find(begin)
        end_at = log.find(end, begin_at + len(begin)) if begin_at >= 0 else -1
        if begin_at < 0 or end_at < 0:
            continue
        segment = log[begin_at + len(begin) : end_at]
        match = constant.search(segment)
        if match:
            result[candidate.ident] = len(split_levels(match.group(1)))
    return result


def apply_arities(
    lines: list[str],
    regions: list[Region],
    candidates: list[Candidate],
    arities: dict[str, int],
) -> tuple[list[str], int, list[str]]:
    patches = 0
    notes: list[str] = []
    for region_index in reversed(range(len(regions))):
        region = regions[region_index]
        block = "\n".join(lines[region.start : region.end])
        for candidate in candidates:
            if candidate.region_index != region_index or candidate.ident not in arities:
                continue
            arity = arities[candidate.ident]
            if arity <= 0:
                continue
            levels = ", ".join("0" for _ in range(arity))
            patterns = (
                (
                    re.compile(
                        rf"@{re.escape(candidate.spelling)}"
                        rf"(?![A-Za-z0-9_']|\.\{{)"
                    ),
                    f"@{candidate.spelling}.{{{levels}}}",
                ),
                (
                    re.compile(
                        rf"(?<![A-Za-z0-9_'.]){re.escape(candidate.spelling)}"
                        rf"(?![A-Za-z0-9_']|\.\{{)"
                    ),
                    f"{candidate.spelling}.{{{levels}}}",
                ),
            )
            for pattern, replacement in patterns:
                count = len(pattern.findall(block))
                if count:
                    block = pattern.sub(replacement, block)
                    patches += count
                    notes.append(f"{candidate.spelling}.{arity}x{count}")
                    break
        lines[region.start : region.end] = block.splitlines()
    return lines, patches, notes


def main() -> int:
    LOGROOT.mkdir(parents=True, exist_ok=True)
    (LOGROOT / "logs").mkdir(parents=True, exist_ok=True)
    for iteration in range(1, 8):
        exit_code, log_path = compile_source(TARGET, f"candidate-{iteration}")
        log = log_path.read_text(encoding="utf-8", errors="replace")
        if exit_code == 0 and "error:" not in log:
            (LOGROOT / "SUCCESS").write_text(str(iteration), encoding="utf-8")
            return 0
        errors = target_error_lines(log)
        if set(errors) != set(TARGET_DECLARATIONS):
            (LOGROOT / "unexpected.log").write_text(log, encoding="utf-8")
            return 20
        lines = TARGET.read_text(encoding="utf-8").splitlines()
        regions = [
            find_region(lines, declaration, errors[declaration])
            for declaration in TARGET_DECLARATIONS
        ]
        candidates = collect_candidates(lines, regions, include_bare=iteration > 1)
        (LOGROOT / f"candidates-{iteration}.txt").write_text(
            "\n".join(
                f"{candidate.ident}|{candidate.region_index}|{candidate.spelling}"
                for candidate in candidates
            ),
            encoding="utf-8",
        )
        if not candidates:
            return 21
        probe = Path(f"/tmp/Mock2_Advanced_solver_v11_probe_{iteration}.lean")
        make_probe(TARGET.read_text(encoding="utf-8"), regions, candidates, probe)
        probe_log = LOGROOT / "logs" / f"probe-{iteration}.log"
        run(["lake", "env", "lean", str(probe)], log=probe_log)
        arities = parse_arities(
            probe_log.read_text(encoding="utf-8", errors="replace"), candidates
        )
        (LOGROOT / f"arities-{iteration}.txt").write_text(
            "\n".join(f"{name}|{arity}" for name, arity in arities.items()),
            encoding="utf-8",
        )
        if not arities:
            return 22
        new_lines, patches, notes = apply_arities(lines, regions, candidates, arities)
        if not patches:
            return 23
        TARGET.write_text("\n".join(new_lines) + "\n", encoding="utf-8")
        (LOGROOT / f"patches-{iteration}.txt").write_text(
            "\n".join(notes), encoding="utf-8"
        )
    return 24


if __name__ == "__main__":
    raise SystemExit(main())
