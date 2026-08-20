#!/usr/bin/env python3
"""Deterministic first-pass Lean 4.33 compatibility transform for canonical QYM.

This is an experimental runtime probe transformer.  It refuses any source
other than the exact checked-in QYM authority and records every broad rewrite
count so that a successful result can later be promoted as checked-in source.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path


EXPECTED_INPUT_SHA256 = (
    "698c7625628ccc654ca7be713944930fdccf12dd78a26937d3f45c9b6982a9f0"
)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def replace_exact(text: str, old: str, new: str, expected: int, label: str,
                  audit: list[dict[str, object]]) -> str:
    count = text.count(old)
    if count != expected:
        raise AssertionError(f"{label}: expected {expected} occurrence(s), found {count}")
    audit.append({"label": label, "occurrences": count})
    return text.replace(old, new)


def expand_legacy_namespace_aliases(
    text: str, audit: list[dict[str, object]]
) -> str:
    """Expand the obsolete `namespace A := Long.Path` syntax in place.

    The aliases are local to 46 named outer namespaces.  We expand `A.foo`
    and `open A` only inside the matching named outer namespace, and replace
    each one- or two-line alias command with comments that preserve its exact
    line count.  Other bare capital identifiers are intentionally untouched:
    many of them are local variables, named arguments, or prose.
    """

    lines = text.splitlines(keepends=True)
    alias_re = re.compile(
        r"^(?P<indent>\s*)namespace\s+(?P<alias>[A-Za-z_][A-Za-z0-9_]*)"
        r"\s*:=\s*(?P<target>.*?)\s*$"
    )
    namespace_re = re.compile(r"^\s*namespace\s+(?P<name>[^\s]+)\s*$")
    aliases: list[dict[str, object]] = []
    for index, line in enumerate(lines):
        body = line[:-1] if line.endswith("\n") else line
        match = alias_re.fullmatch(body)
        if match is None:
            continue
        target = match.group("target").strip()
        consumed = 1
        if not target:
            if index + 1 >= len(lines):
                raise AssertionError("truncated namespace alias command")
            target = lines[index + 1].strip()
            consumed = 2
        if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'.]*", target):
            raise AssertionError(f"invalid namespace alias target: {target!r}")
        outer_index = None
        outer_name = None
        for prior in range(index - 1, -1, -1):
            prior_body = lines[prior].strip()
            outer_match = namespace_re.fullmatch(prior_body)
            if outer_match is not None and ":=" not in prior_body:
                outer_index = prior
                outer_name = outer_match.group("name")
                break
        if outer_index is None or outer_name is None:
            raise AssertionError(f"namespace alias without enclosing namespace at {index + 1}")
        aliases.append({
            "index": index,
            "alias": match.group("alias"),
            "target": target,
            "consumed": consumed,
            "indent": match.group("indent"),
            "outer_index": outer_index,
            "outer_name": outer_name,
        })

    if len(aliases) != 230:
        raise AssertionError(f"legacy namespace alias inventory changed: {len(aliases)}")
    groups: dict[tuple[int, str], list[dict[str, object]]] = {}
    for row in aliases:
        key = (int(row["outer_index"]), str(row["outer_name"]))
        groups.setdefault(key, []).append(row)
    if len(groups) != 46:
        raise AssertionError(f"namespace alias scope inventory changed: {len(groups)}")

    prefix_replacements = 0
    open_replacements = 0
    consumed_indices: dict[int, tuple[dict[str, object], bool]] = {}
    for (outer_index, outer_name), rows in groups.items():
        aliases_in_scope = [str(row["alias"]) for row in rows]
        if len(aliases_in_scope) != len(set(aliases_in_scope)):
            raise AssertionError(f"duplicate alias inside {outer_name}")
        last_alias_line = max(int(row["index"]) + int(row["consumed"]) - 1 for row in rows)
        end_index = None
        expected_end = f"end {outer_name}"
        for candidate in range(last_alias_line + 1, len(lines)):
            if lines[candidate].strip() == expected_end:
                end_index = candidate
                break
        if end_index is None:
            raise AssertionError(f"missing exact namespace end for {outer_name}")

        for row in rows:
            start = int(row["index"])
            consumed_indices[start] = (row, False)
            if int(row["consumed"]) == 2:
                consumed_indices[start + 1] = (row, True)

        for line_index in range(outer_index, end_index + 1):
            if line_index in consumed_indices:
                row, continuation = consumed_indices[line_index]
                newline = "\n" if lines[line_index].endswith("\n") else ""
                indent = str(row["indent"])
                if continuation:
                    lines[line_index] = (
                        f"{indent}-- expanded namespace alias continuation{newline}"
                    )
                else:
                    lines[line_index] = (
                        f"{indent}-- expanded namespace alias {row['alias']} = "
                        f"{row['target']}{newline}"
                    )
                continue
            current = lines[line_index]
            is_open_command = re.match(r"^\s*open(?:\s+scoped)?\s+", current) is not None
            for row in rows:
                alias = str(row["alias"])
                target = str(row["target"])
                current, count = re.subn(
                    rf"\b{re.escape(alias)}\.", target + ".", current
                )
                prefix_replacements += count
                if is_open_command:
                    current, count = re.subn(
                        rf"\b{re.escape(alias)}\b", target, current
                    )
                    open_replacements += count
            lines[line_index] = current

    result = "".join(lines)
    remaining = re.findall(
        r"^\s*namespace\s+[A-Za-z_][A-Za-z0-9_]*\s*:=", result, re.M
    )
    if remaining:
        raise AssertionError(f"unexpanded namespace aliases remain: {len(remaining)}")
    if prefix_replacements != 3639:
        raise AssertionError(
            f"namespace alias prefix inventory changed: {prefix_replacements}"
        )
    if open_replacements != 9:
        raise AssertionError(f"namespace alias open inventory changed: {open_replacements}")
    audit.extend([
        {"label": "expand_legacy_namespace_alias_commands", "occurrences": len(aliases)},
        {"label": "expand_legacy_namespace_alias_prefixes", "occurrences": prefix_replacements},
        {"label": "expand_legacy_namespace_alias_opens", "occurrences": open_replacements},
    ])
    return result


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", required=True)
    parser.add_argument("--output", required=True)
    parser.add_argument("--audit", required=True)
    args = parser.parse_args()

    source_path = Path(args.input)
    output_path = Path(args.output)
    audit_path = Path(args.audit)
    raw = source_path.read_bytes()
    if sha256(raw) != EXPECTED_INPUT_SHA256:
        raise AssertionError("canonical QYM SHA-256 mismatch")
    if b"\r" in raw or b"\x00" in raw or not raw.endswith(b"\n"):
        raise AssertionError("canonical QYM encoding/newline invariant mismatch")
    text = raw.decode("utf-8")
    audit: list[dict[str, object]] = []

    text = replace_exact(
        text,
        "open scoped BigOperators ComplexOrder ENNReal UpperHalfPlane",
        "open scoped BigOperators ComplexOrder ENNReal UpperHalfPlane InnerProductSpace",
        1,
        "activate_inner_product_notation_globally",
        audit,
    )

    old_density = """def positiveDiagonalDensity : Mat2ˣ :=
  ⟨!![2, 0; 0, 1], !![(1 / 2 : ℂ), 0; 0, 1],
    by norm_num [Matrix.mul_fin_two, Matrix.one_fin_two],
    by norm_num [Matrix.mul_fin_two, Matrix.one_fin_two]⟩"""
    new_density = """def positiveDiagonalDensity : Mat2ˣ :=
  ⟨!![2, 0; 0, 1], !![(1 / 2 : ℂ), 0; 0, 1],
    by
      norm_num [Matrix.mul_fin_two]
      exact (Matrix.one_fin_two (α := ℂ)).symm,
    by
      norm_num [Matrix.mul_fin_two]
      exact (Matrix.one_fin_two (α := ℂ)).symm⟩"""
    text = replace_exact(
        text, old_density, new_density, 1, "close_positive_diagonal_density_units", audit
    )

    lambda_count = text.count("λ")
    if lambda_count != 338:
        raise AssertionError(f"unicode lambda identifier inventory changed: {lambda_count}")
    text = text.replace("λ", "lambda")
    audit.append({"label": "rename_reserved_unicode_lambda_identifiers", "occurrences": lambda_count})

    text = replace_exact(
        text, "Complex.conj_conj", "star_star", 1,
        "modernize_complex_conj_conj", audit,
    )
    complex_conj_count = text.count("Complex.conj")
    if complex_conj_count != 27:
        raise AssertionError(f"Complex.conj inventory changed: {complex_conj_count}")
    text = text.replace("Complex.conj", "star")
    audit.append({"label": "modernize_complex_conj", "occurrences": complex_conj_count})

    rclike_conj_count = text.count("RCLike.conj")
    if rclike_conj_count != 11:
        raise AssertionError(f"RCLike.conj inventory changed: {rclike_conj_count}")
    text = text.replace("RCLike.conj", "star")
    audit.append({"label": "modernize_rclike_conj", "occurrences": rclike_conj_count})

    set_frontier_count = text.count("Set.frontier")
    if set_frontier_count != 44:
        raise AssertionError(f"Set.frontier inventory changed: {set_frontier_count}")
    text = text.replace("Set.frontier", "frontier")
    audit.append({"label": "modernize_frontier_name", "occurrences": set_frontier_count})

    text, sum_in_count = re.subn(r"∑ ([A-Za-z][A-Za-z0-9_]*) in ", r"∑ \1 ∈ ", text)
    if sum_in_count != 7:
        raise AssertionError(f"finite-sum old binder inventory changed: {sum_in_count}")
    audit.append({"label": "modernize_finite_sum_binder", "occurrences": sum_in_count})

    text = replace_exact(
        text,
        "#print axioms FullCertification.NoGo.no_realSpectralParameter_of_lt_quarter",
        "#print axioms QYM.FullCertification.NoGo.no_realSpectralParameter_of_lt_quarter",
        1,
        "fully_qualify_early_axiom_audit",
        audit,
    )

    candidate = text.encode("utf-8")
    if b"\r" in candidate or b"\x00" in candidate or not candidate.endswith(b"\n"):
        raise AssertionError("candidate encoding/newline invariant mismatch")
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_bytes(candidate)
    result = {
        "schema": "qym-lean433-broad-repair-pass1-v1",
        "input_sha256": EXPECTED_INPUT_SHA256,
        "output_sha256": sha256(candidate),
        "input_bytes": len(raw),
        "output_bytes": len(candidate),
        "input_lf": raw.count(b"\n"),
        "output_lf": candidate.count(b"\n"),
        "rewrites": audit,
    }
    audit_path.parent.mkdir(parents=True, exist_ok=True)
    with audit_path.open("w", encoding="utf-8", newline="\n") as handle:
        handle.write(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
