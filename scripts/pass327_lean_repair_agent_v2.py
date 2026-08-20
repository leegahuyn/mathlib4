from __future__ import annotations

from pathlib import Path
import re
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import pass327_lean_repair_agent as base


def public_declaration_headers(source: str) -> list[str]:
    """Fingerprint only existing public theorem-like statements.

    Private helper lemmas may be introduced by a repair.  Public theorem,
    lemma, and corollary statements remain byte-normalized and invariant.
    """
    lines = source.splitlines()
    result: list[str] = []
    start_re = re.compile(
        r"^\s*(?P<mods>(?:(?:private|protected|nonrec)\s+)*)"
        r"(?P<kind>theorem|lemma|corollary)\b"
    )
    index = 0
    while index < len(lines):
        match = start_re.match(lines[index])
        if not match:
            index += 1
            continue
        is_private = "private" in match.group("mods").split()
        collected: list[str] = []
        paren = bracket = brace = 0
        while index < len(lines):
            line = lines[index]
            collected.append(line)
            # Header lines normally do not contain a cross-line block comment;
            # mask same-line comments/strings conservatively without failing on
            # an unrelated preceding doc comment.
            code = re.sub(r'"(?:\\.|[^"\\])*"', '""', line)
            code = code.split('--', 1)[0]
            code = re.sub(r'/\-.*?\-/', '', code)
            paren += code.count("(") - code.count(")")
            bracket += code.count("[") - code.count("]")
            brace += code.count("{") - code.count("}")
            marker_position = None
            if paren <= 0 and bracket <= 0 and brace <= 0:
                positions = [position for token in (":=", " where")
                             if (position := code.find(token)) >= 0]
                marker_position = min(positions) if positions else None
            if marker_position is not None:
                joined = "\n".join(collected)
                positions = [position for token in (":=", " where")
                             if (position := joined.find(token)) >= 0]
                header = joined[:min(positions)]
                if not is_private:
                    result.append(re.sub(r"\s+", " ", header).strip())
                index += 1
                break
            index += 1
        else:
            break
    return result


def validate_diff_v2(diff: str, path: Path, before_source: str) -> None:
    relative = str(path.relative_to(base.ROOT))
    if len(diff) > 220000:
        raise RuntimeError("diff is unreasonably large")
    headers = re.findall(r"^diff --git a/(.+?) b/(.+?)$", diff, flags=re.M)
    if not headers or any(left != relative or right != relative for left, right in headers):
        raise RuntimeError(f"diff may modify only {relative}; headers={headers}")

    changed = 0
    declaration = re.compile(
        r"^\s*(?P<mods>(?:(?:private|protected|nonrec)\s+)*)"
        r"(?P<kind>theorem|lemma|corollary)\b"
    )
    for line in diff.splitlines():
        if not line or line.startswith(("+++", "---", "@@", "diff --git", "index ")):
            continue
        if line[0] not in "+-":
            continue
        changed += 1
        body = line[1:]
        match = declaration.match(body)
        if line.startswith("-") and match:
            raise RuntimeError("repair attempted to delete or edit an existing theorem-like header")
        if line.startswith("+") and match:
            modifiers = set(match.group("mods").split())
            if "private" not in modifiers:
                raise RuntimeError("repair attempted to add or edit a public theorem-like header")
        if re.match(r"^\s*import\b", body):
            if line.startswith("-"):
                raise RuntimeError("repair attempted to remove an existing import")
            if not re.match(
                r"^\s*import\s+(?:Mathlib|PrimalitySheafVerification)(?:\.|\s|$)", body
            ):
                raise RuntimeError(f"unapproved added import: {body}")
        if line.startswith("+"):
            if re.search(
                r"\b(sorry|admit|axiom|unsafe|native_decide|Lean\.ofReduceBool)\b",
                body,
            ):
                raise RuntimeError("repair attempted to add a forbidden proof escape")
            if "set_option maxErrors" in body:
                raise RuntimeError("repair attempted to hide the error frontier")
        if "#print axioms" in body:
            raise RuntimeError("repair attempted to alter an axiom audit command")
    if changed > 1400:
        raise RuntimeError(f"diff changes too many lines: {changed}")


def build_prompt_v2(path: Path, compile_result: dict) -> str:
    prompt = base.build_prompt(path, compile_result)
    prompt = prompt.replace(
        "- Prefer qualified current Mathlib names, explicit type annotations,",
        "- You may add a necessary Mathlib or project import, but never remove an existing import.\n"
        "- You may add small `private lemma`/`private theorem` helpers; never edit an existing public statement.\n"
        "- Prefer qualified current Mathlib names, explicit type annotations,",
    )
    return prompt


# Monkey-patch the audited base engine.  All compilation, source audit, patch
# application, progress measurement, checkpointing, and final two-pass gates
# remain the same.
base.declaration_headers = public_declaration_headers
base.validate_diff = validate_diff_v2
base.build_prompt = build_prompt_v2


if __name__ == "__main__":
    raise SystemExit(base.main())
