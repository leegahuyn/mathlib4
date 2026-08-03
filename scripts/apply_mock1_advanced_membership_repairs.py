from __future__ import annotations

import re
from pathlib import Path

PATH = Path("PrimalitySheafVerification/Mock1_Advanced.lean")

REQUIREMENT_CASES = [
    "domain_q_cusp",
    "qseries_principal_polar",
    "appell_completion_shadow",
    "xi_operator",
    "slash_transport",
    "linear_systems",
    "entropy_asymptotic",
    "rademacher_expansion",
    "degeneracy_cardy",
    "spt_crt",
    "tor_surrogate",
    "padic_mahler",
    "rational_ols",
    "abstract_concrete_chain",
]


def mem_term(index: int) -> str:
    term = "List.Mem.head _"
    for _ in range(index):
        term = f"List.Mem.tail _ ({term})"
    return term


def parse_targets(text: str, layer: str) -> list[str]:
    marker = f"  | {layer} =>"
    start = text.find(marker)
    if start < 0:
        raise RuntimeError(f"missing targets branch {layer}")
    block_start = text.find("[", start)
    if block_start < 0:
        raise RuntimeError(f"missing list for targets branch {layer}")
    lines = text[block_start:].splitlines()
    block: list[str] = []
    for line in lines:
        block.append(line)
        if line.rstrip().endswith("]"):
            break
    return re.findall(r'"([^"]+)"', "\n".join(block))


def repair_requirement_mem_all(text: str) -> tuple[str, bool]:
    pattern = re.compile(
        r"theorem mem_all \(key : RequirementKey\) :\n"
        r"    List\.Mem key all := by\n"
        r"(?:  classical\n)?"
        r"  cases key <;> (?:simp \[all\]|decide)\n"
    )
    lines = [
        "theorem mem_all (key : RequirementKey) :",
        "    List.Mem key all := by",
        "  cases key with",
    ]
    for index, case in enumerate(REQUIREMENT_CASES):
        lines.append(f"  | {case} => exact {mem_term(index)}")
    replacement = "\n".join(lines) + "\n"
    repaired, count = pattern.subn(replacement, text, count=1)
    if count:
        print("Mock1Advanced RequirementKey.mem_all: direct membership proof applied")
    else:
        print("Mock1Advanced RequirementKey.mem_all: already applied/source changed")
    return repaired, bool(count)


def repair_target_memberships(text: str) -> tuple[str, bool]:
    target_lists = {
        layer: parse_targets(text, layer)
        for layer in ("coverage", "reference")
    }
    pattern = re.compile(
        r"(theorem\s+[A-Za-z0-9_']+\s*:\s*\n?\s*"
        r"List\.Mem\s+\"([^\"]+)\"\s*\n?\s*"
        r"\(targets AxiomAuditLayer\.(coverage|reference)\)\s*:= by)\n"
        r"(?:  classical\n)?"
        r"  (?:simp \[targets\]|decide)"
    )

    replaced = 0

    def repl(match: re.Match[str]) -> str:
        nonlocal replaced
        target = match.group(2)
        layer = match.group(3)
        values = target_lists[layer]
        if target not in values:
            raise RuntimeError(f"{target!r} is absent from targets {layer}")
        replaced += 1
        return match.group(1) + "\n  exact " + mem_term(values.index(target))

    repaired = pattern.sub(repl, text)
    if replaced:
        print(f"Mock1Advanced concrete target memberships: applied {replaced}")
    else:
        print("Mock1Advanced concrete target memberships: already applied/source changed")
    return repaired, replaced > 0


def main() -> int:
    text = PATH.read_text(encoding="utf-8")
    text, changed_a = repair_requirement_mem_all(text)
    text, changed_b = repair_target_memberships(text)
    if changed_a or changed_b:
        PATH.write_text(text, encoding="utf-8", newline="\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
