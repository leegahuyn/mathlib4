#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import re
from dataclasses import dataclass
from pathlib import Path

TRUST = ("sorry", "admit", "axiom", "unsafe", "native_decide", "Lean.ofReduceBool")
DECL_RE = re.compile(
    r"(?m)^(?:protected\s+|private\s+|noncomputable\s+|local\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance|structure|class)\s+([^\s(:]+)"
)
HEADER_RE = re.compile(r"(?m)^.*?:(\d+):(\d+):\s+error:\s*(.*)$")


@dataclass(frozen=True)
class Error:
    line: int
    col: int
    message: str
    declaration: str | None = None


def strip_noncode(text: str) -> str:
    out = list(text)
    i = 0
    depth = 0
    string = False
    esc = False
    while i < len(out):
        if depth:
            if text.startswith("/-", i):
                out[i] = out[i + 1] = " "
                depth += 1
                i += 2
                continue
            if text.startswith("-/", i):
                out[i] = out[i + 1] = " "
                depth -= 1
                i += 2
                continue
            if out[i] != "\n":
                out[i] = " "
            i += 1
            continue
        if string:
            ch = out[i]
            if ch != "\n":
                out[i] = " "
            if esc:
                esc = False
            elif ch == "\\":
                esc = True
            elif ch == '"':
                string = False
            i += 1
            continue
        if text.startswith("/-", i):
            out[i] = out[i + 1] = " "
            depth = 1
            i += 2
            continue
        if text.startswith("--", i):
            while i < len(out) and out[i] != "\n":
                out[i] = " "
                i += 1
            continue
        if out[i] == '"':
            out[i] = " "
            string = True
        i += 1
    return "".join(out)


def trust_counts(text: str) -> dict[str, int]:
    code = strip_noncode(text)
    return {
        token: len(
            re.findall(
                r"(?<![A-Za-z0-9_])" + re.escape(token) + r"(?![A-Za-z0-9_])",
                code,
            )
        )
        for token in TRUST
    }


def declaration_metadata(text: str):
    matches = list(DECL_RE.finditer(text))
    result = []
    for index, match in enumerate(matches):
        start = match.start()
        end = matches[index + 1].start() if index + 1 < len(matches) else len(text)
        start_line = text.count("\n", 0, start) + 1
        end_line = text.count("\n", 0, end) + 1
        result.append(
            {
                "name": match.group(1),
                "index": index + 1,
                "start": start,
                "end": end,
                "start_line": start_line,
                "end_line": end_line,
            }
        )
    return result


def int_from(row: dict, keys: tuple[str, ...]) -> int | None:
    for key in keys:
        value = row.get(key)
        if isinstance(value, int):
            return value
        if isinstance(value, str) and value.isdigit():
            return int(value)
    position = row.get("position")
    if isinstance(position, dict):
        for key in keys:
            value = position.get(key)
            if isinstance(value, int):
                return value
    return None


def str_from(row: dict, keys: tuple[str, ...]) -> str | None:
    for key in keys:
        value = row.get(key)
        if isinstance(value, str) and value:
            return value
    return None


def read_errors(diagnostics: Path | None, raw_log: Path | None) -> list[Error]:
    errors: list[Error] = []
    if diagnostics is not None and diagnostics.exists():
        for line in diagnostics.read_text(errors="replace").splitlines():
            try:
                row = json.loads(line)
            except json.JSONDecodeError:
                continue
            severity = str(row.get("severity", row.get("kind", ""))).lower()
            if severity and severity != "error":
                continue
            line_no = int_from(row, ("line", "line_number", "start_line", "row"))
            col = int_from(row, ("col", "column", "start_col")) or 1
            message = str_from(row, ("message", "text", "diagnostic", "normalized_message"))
            declaration = str_from(
                row,
                ("declaration", "declaration_name", "enclosing_declaration"),
            )
            if line_no is not None and message is not None:
                errors.append(Error(line_no, col, message, declaration))
    if not errors and raw_log is not None and raw_log.exists():
        raw = raw_log.read_text(errors="replace")
        for match in HEADER_RE.finditer(raw):
            errors.append(Error(int(match.group(1)), int(match.group(2)), match.group(3), None))
    dedup: list[Error] = []
    seen = set()
    for error in sorted(errors, key=lambda item: (item.line, item.col, item.message)):
        key = (error.line, error.col, error.message)
        if key not in seen:
            seen.add(key)
            dedup.append(error)
    return dedup


def declaration_for_error(meta, error: Error):
    if error.declaration:
        for item in meta:
            if item["name"] == error.declaration:
                return item
    for item in meta:
        if item["start_line"] <= error.line <= item["end_line"]:
            return item
    return None


def nearest_line(lines: list[str], relative_line: int, predicate, radius: int = 35) -> int | None:
    if not lines:
        return None
    center = max(0, min(len(lines) - 1, relative_line))
    order = [center]
    for distance in range(1, radius + 1):
        if center - distance >= 0:
            order.append(center - distance)
        if center + distance < len(lines):
            order.append(center + distance)
    for index in order:
        if predicate(lines[index]):
            return index
    return None


def local_let_names(lines: list[str], through: int) -> list[str]:
    names: list[str] = []
    pattern = re.compile(r"^\s*let\s+([A-Za-z_][A-Za-z0-9_']*)\b")
    for line in lines[: through + 1]:
        match = pattern.match(line)
        if match and match.group(1) not in names:
            names.append(match.group(1))
    return names


def add_simp_terms(line: str, terms: list[str], relax_only: bool) -> str:
    terms = list(dict.fromkeys(term for term in terms if term))
    if relax_only:
        line = re.sub(r"\bsimpa\s+only\s*\[", "simpa [", line, count=1)
        line = re.sub(r"\bsimp\s+only\s*\[", "simp [", line, count=1)
    if not terms:
        return line
    joined = ", ".join(terms)
    if re.search(r"\bsimpa\s+(?:only\s*)?\[", line):
        return re.sub(
            r"\bsimpa\s+(?:only\s*)?\[",
            f"simpa [{joined}, ",
            line,
            count=1,
        )
    if re.search(r"\bsimp\s+(?:only\s*)?\[", line):
        return re.sub(
            r"\bsimp\s+(?:only\s*)?\[",
            f"simp [{joined}, ",
            line,
            count=1,
        )
    if re.search(r"\bsimpa\s+using\b", line):
        return re.sub(r"\bsimpa\s+using\b", f"simpa [{joined}] using", line, count=1)
    if re.search(r"\bsimp\s+at\b", line):
        return re.sub(r"\bsimp\s+at\b", f"simp [{joined}] at", line, count=1)
    return line


QUALIFY = {
    "one_re": "Complex.one_re",
    "one_im": "Complex.one_im",
    "I_re": "Complex.I_re",
    "I_im": "Complex.I_im",
    "star_def": "Complex.star_def",
    "conj_ofReal": "Complex.conj_ofReal",
}


def common_terms(body: str) -> list[str]:
    terms: list[str] = []
    if "Function.comp" in body or "∘" in body:
        terms.append("Function.comp_def")
    if "ContinuousMap" in body:
        terms.append("ContinuousMap.coe_mk")
    if "ambientPlaneToUpper" in body:
        terms.append("ambientPlaneToUpper")
    if "Complex.measurableEquivPi" in body:
        terms.append("Complex.measurableEquivPi_apply")
    if "Pi.smul" in body:
        terms.append("Pi.smul_apply")
    if "literalStageNegativePlaneWave" in body:
        terms.extend(
            [
                "literalStageNegativePlaneWave",
                "literalStagePhysicalTorusPoint",
                "UnitAddTorus.mFourier",
            ]
        )
    return list(dict.fromkeys(terms))


def transform_declaration(
    body: str,
    relative_line: int,
    message: str,
    *,
    let_unfold: bool,
    relax_simp: bool,
    enrich_simp: bool,
    ring_nf: bool,
    qualify: bool,
    funext: bool,
) -> tuple[str, dict[str, object]]:
    lines = body.splitlines(keepends=True)
    details: dict[str, object] = {"message": message[:300], "changes": []}

    if qualify:
        before = "".join(lines)
        after = before
        unknown_match = re.search(r"unknown identifier ['‘`]?([^'’`\s]+)", message, re.I)
        candidates = [unknown_match.group(1)] if unknown_match else list(QUALIFY)
        for name in candidates:
            bare = name.split(".")[-1]
            replacement = QUALIFY.get(bare)
            if replacement:
                after = re.sub(
                    rf"(?<![A-Za-z0-9_.]){re.escape(bare)}(?![A-Za-z0-9_])",
                    replacement,
                    after,
                )
        if after != before:
            lines = after.splitlines(keepends=True)
            details["changes"].append("qualify_unknown_identifier")

    simpa_index = nearest_line(
        lines,
        relative_line,
        lambda line: bool(re.search(r"\b(?:simpa|simp)\b", line)),
    )
    if simpa_index is not None and (let_unfold or relax_simp or enrich_simp):
        terms: list[str] = []
        if let_unfold:
            terms.extend(local_let_names(lines, simpa_index))
        if enrich_simp:
            terms.extend(common_terms("".join(lines)))
        old = lines[simpa_index]
        new = add_simp_terms(old, terms, relax_simp)
        if new != old:
            lines[simpa_index] = new
            details["changes"].append(
                {
                    "simp_line": simpa_index + 1,
                    "let_terms": local_let_names(lines, simpa_index) if let_unfold else [],
                    "common_terms": common_terms("".join(lines)) if enrich_simp else [],
                    "relaxed_only": relax_simp,
                }
            )

    if ring_nf:
        ring_index = nearest_line(
            lines,
            relative_line,
            lambda line: bool(re.match(r"^\s*ring\s*(?:<;>.*)?$", line.rstrip("\n"))),
        )
        if ring_index is not None:
            old = lines[ring_index]
            new = re.sub(r"^(\s*)ring\b", r"\1ring_nf", old, count=1)
            if new != old:
                lines[ring_index] = new
                details["changes"].append({"ring_nf_line": ring_index + 1})

    if funext and any(token in message.lower() for token in ("function", "fun x", "funext")):
        target = nearest_line(
            lines,
            relative_line,
            lambda line: bool(re.match(r"^\s*(?:rfl|simpa\b|exact\b)", line)),
        )
        if target is not None:
            indent = re.match(r"^(\s*)", lines[target]).group(1)
            lines.insert(target, f"{indent}funext x\n")
            details["changes"].append({"funext_before_line": target + 1})

    return "".join(lines), details


RULES = {
    "first_let": {"limit": 1, "let_unfold": True},
    "first_relax": {"limit": 1, "relax_simp": True},
    "first_enrich": {"limit": 1, "let_unfold": True, "enrich_simp": True},
    "first_ring": {"limit": 1, "ring_nf": True},
    "first_qualify": {"limit": 1, "qualify": True},
    "first_funext": {"limit": 1, "let_unfold": True, "enrich_simp": True, "funext": True},
    "first3_safe": {
        "limit": 3,
        "let_unfold": True,
        "relax_simp": True,
        "enrich_simp": True,
        "ring_nf": True,
        "qualify": True,
    },
    "first8_safe": {
        "limit": 8,
        "let_unfold": True,
        "relax_simp": True,
        "enrich_simp": True,
        "ring_nf": True,
        "qualify": True,
        "funext": True,
    },
}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--base", type=Path, required=True)
    parser.add_argument("--base-sha256", required=True)
    parser.add_argument("--diagnostics", type=Path)
    parser.add_argument("--raw-log", type=Path)
    parser.add_argument("--rule", choices=RULES, required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--audit", type=Path, required=True)
    args = parser.parse_args()

    raw = args.base.read_bytes()
    text = raw.decode()
    actual_sha = hashlib.sha256(raw).hexdigest()
    if actual_sha != args.base_sha256:
        raise RuntimeError(f"base SHA mismatch: {actual_sha} != {args.base_sha256}")
    before_decls = DECL_RE.findall(text)
    before_trust = trust_counts(text)
    if any(before_trust.values()):
        raise RuntimeError(f"base source trust audit failed: {before_trust}")

    errors = read_errors(args.diagnostics, args.raw_log)
    if not errors:
        raise RuntimeError("no actual Lean errors were recovered from baseline evidence")
    meta = declaration_metadata(text)
    config = RULES[args.rule]
    chosen: list[tuple[Error, dict]] = []
    seen_decls = set()
    for error in errors:
        declaration = declaration_for_error(meta, error)
        if declaration is None or declaration["name"] in seen_decls:
            continue
        seen_decls.add(declaration["name"])
        chosen.append((error, declaration))
        if len(chosen) >= int(config["limit"]):
            break
    if not chosen:
        raise RuntimeError("no enclosing declarations were mapped for actual errors")

    audit_changes: list[dict[str, object]] = []
    # Reverse source order keeps previously computed character ranges valid.
    chosen.sort(key=lambda pair: pair[1]["start"], reverse=True)
    for error, declaration in chosen:
        start = declaration["start"]
        end = declaration["end"]
        body = text[start:end]
        relative_line = max(0, error.line - declaration["start_line"])
        new_body, detail = transform_declaration(
            body,
            relative_line,
            error.message,
            let_unfold=bool(config.get("let_unfold")),
            relax_simp=bool(config.get("relax_simp")),
            enrich_simp=bool(config.get("enrich_simp")),
            ring_nf=bool(config.get("ring_nf")),
            qualify=bool(config.get("qualify")),
            funext=bool(config.get("funext")),
        )
        if new_body != body:
            text = text[:start] + new_body + text[end:]
        audit_changes.append(
            {
                "declaration": declaration["name"],
                "declaration_index": declaration["index"],
                "error_line": error.line,
                "error_col": error.col,
                "changed": new_body != body,
                **detail,
            }
        )

    after_decls = DECL_RE.findall(text)
    after_trust = trust_counts(text)
    if after_decls != before_decls:
        raise RuntimeError("public declaration sequence changed")
    if any(after_trust.values()):
        raise RuntimeError(f"candidate source trust audit failed: {after_trust}")

    data = text.encode()
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_bytes(data)
    audit = {
        "schema": "fa-iterative-frontier-repair-audit-v1",
        "rule": args.rule,
        "rule_config": config,
        "base_sha256": actual_sha,
        "base_bytes": len(raw),
        "base_lines": len(raw.decode().splitlines()),
        "base_declarations": len(before_decls),
        "source_sha256": hashlib.sha256(data).hexdigest(),
        "source_bytes": len(data),
        "source_lines": len(text.splitlines()),
        "source_declarations": len(after_decls),
        "declaration_sequence_identical": before_decls == after_decls,
        "trust_before": before_trust,
        "trust_after": after_trust,
        "actual_error_count_recovered": len(errors),
        "targeted_error_declarations": [item[1]["name"] for item in chosen],
        "changes": audit_changes,
        "candidate_differs_from_base": data != raw,
        "public_header_changes": False,
        "comments_changed": False,
        "attributes_changed": False,
    }
    args.audit.parent.mkdir(parents=True, exist_ok=True)
    args.audit.write_text(json.dumps(audit, indent=2, sort_keys=True) + "\n")
    print(json.dumps(audit, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
