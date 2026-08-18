#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import hashlib
import json
import re
import sys


def git_blob(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def locate_declaration(text: str, owner: str | None, line: int) -> tuple[int, int, int, str, str]:
    decl_re = re.compile(
        r"(?m)^(?:set_option[^\n]* in\n)*(?:theorem|lemma|def|abbrev|instance|"
        r"noncomputable\s+def|noncomputable\s+instance)\s+([^\s:(]+)"
    )
    decls: list[tuple[int, str, int]] = []
    for match in decl_re.finditer(text):
        line_no = text.count("\n", 0, match.start()) + 1
        decls.append((line_no, match.group(1), match.start()))
    target: tuple[int, str, int] | None = None
    if owner:
        matches = [item for item in decls if item[1] == owner]
        if matches:
            target = matches[0]
    if target is None:
        prior = [item for item in decls if item[0] <= line]
        if prior:
            target = prior[-1]
    if target is None:
        raise RuntimeError("target declaration not found")
    index = decls.index(target)
    start = target[2]
    end = decls[index + 1][2] if index + 1 < len(decls) else len(text)
    return target[0], start, end, target[1], text[start:end]


def explicit_structure_variant(decl: str) -> str:
    patterns = [
        (
            r"InnerProductSpace\s+ℂ\s+(\([^\n]+\))\s*:=\s*\n?\s*inferInstance",
            lambda m: f"InnerProductSpace ℂ {m.group(1)} :=\n  {m.group(1)}.innerProductSpace",
        ),
        (
            r"NormedSpace\s+ℂ\s+(\([^\n]+\))\s*:=\s*\n?\s*inferInstance",
            lambda m: f"NormedSpace ℂ {m.group(1)} :=\n  {m.group(1)}.normedSpace",
        ),
        (
            r"CompleteSpace\s+(\([^\n]+\))\s*:=\s*\n?\s*inferInstance",
            lambda m: f"CompleteSpace {m.group(1)} :=\n  {m.group(1)}.completeSpace",
        ),
    ]
    for pattern, replacement in patterns:
        candidate, count = re.subn(pattern, replacement, decl, count=1)
        if count:
            return candidate
    raise RuntimeError("explicit structure producer pattern absent")


def remove_local_shadow_variant(decl: str) -> str:
    # Remove only a single explicitly shadowing local instance. The full declaration is always
    # direct-compiled, so this never becomes authoritative without kernel verification.
    patterns = [
        r"(?ms)^\s*letI\s*:\s*AddCommGroup\s+ℂ\s*:=.*?(?=^\s*(?:letI|have|show|exact|refine|apply|simpa|rw|constructor|·|\Z))",
        r"(?ms)^\s*letI\s*:\s*Module\s+ℂ\s+[^\n]+:=.*?(?=^\s*(?:letI|have|show|exact|refine|apply|simpa|rw|constructor|·|\Z))",
        r"(?ms)^\s*letI\s*:\s*NormedSpace\s+ℂ\s+[^\n]+:=.*?(?=^\s*(?:letI|have|show|exact|refine|apply|simpa|rw|constructor|·|\Z))",
    ]
    for pattern in patterns:
        candidate, count = re.subn(pattern, "", decl, count=1)
        if count:
            return candidate
    raise RuntimeError("local shadow producer pattern absent")


def transform(decl: str, variant: str) -> str:
    if variant == "baseline":
        return decl
    if variant == "heartbeat-both":
        return (
            "set_option maxHeartbeats 4000000 in\n"
            "set_option synthInstance.maxHeartbeats 4000000 in\n" + decl
        )
    if variant == "heartbeat-synth":
        return "set_option synthInstance.maxHeartbeats 8000000 in\n" + decl
    if variant == "infer-by":
        candidate, count = re.subn(r":=\s*inferInstance\b", ":= by\n  infer_instance", decl, count=1)
        if count == 0:
            candidate, count = re.subn(
                r":=\s*by\s*\n\s*exact\s+inferInstance\b",
                ":= by\n  infer_instance",
                decl,
                count=1,
            )
        if count == 0:
            raise RuntimeError("inferInstance producer pattern absent")
        return candidate
    if variant == "explicit-structure":
        return explicit_structure_variant(decl)
    if variant == "remove-local-shadow":
        return remove_local_shadow_variant(decl)
    if variant == "api-migrate":
        replacements = {
            ".orthogonalProjection\n": ".orthogonalProjectionOnto\n",
            ".orthogonalProjection ": ".orthogonalProjectionOnto ",
            "orthogonalProjection_mem_subspace_eq_self": "orthogonalProjectionOnto_mem_subspace_eq_self",
            "norm_orthogonalProjection_apply_le": "norm_orthogonalProjectionOnto_apply_le",
            "orthogonalProjection_norm_le": "orthogonalProjectionOnto_norm_le",
            "ker_orthogonalProjection": "ker_orthogonalProjectionOnto",
        }
        candidate = decl
        changed = False
        for old, new in replacements.items():
            if old in candidate:
                candidate = candidate.replace(old, new)
                changed = True
        if not changed:
            raise RuntimeError("known API migration pattern absent")
        return candidate
    if variant == "simp-flex":
        candidate, count = re.subn(r"\bsimpa\s+only\s*\[", "simpa [", decl)
        if count == 0:
            raise RuntimeError("simpa only pattern absent")
        return candidate
    raise RuntimeError(f"unknown variant: {variant}")


def forbidden_audit(text: str) -> dict[str, int]:
    return {
        "sorry": len(re.findall(r"\bsorry\b", text)),
        "admit": len(re.findall(r"\badmit\b", text)),
        "native_decide": len(re.findall(r"\bnative_decide\b", text)),
        "Lean.ofReduceBool": text.count("Lean.ofReduceBool"),
        "global_axiom": len(re.findall(r"(?m)^\s*axiom\s+", text)),
        "unsafe": len(re.findall(r"(?m)^\s*unsafe\s+", text)),
        "maxHeartbeats_zero": len(re.findall(r"set_option\s+maxHeartbeats\s+0\b", text)),
    }


def main() -> None:
    if len(sys.argv) != 5:
        raise SystemExit("usage: qym_auto_producer_builder.py QYM NEXT OUT VARIANT")
    source = Path(sys.argv[1])
    next_path = Path(sys.argv[2])
    out = Path(sys.argv[3])
    variant = sys.argv[4]
    out.mkdir(parents=True, exist_ok=True)

    text = source.read_text(encoding="utf-8")
    next_data = json.loads(next_path.read_text(encoding="utf-8"))
    owner_data = next_data.get("first_owner") or {}
    owner = owner_data.get("name")
    line = int(owner_data.get("line") or (next_data.get("first_error") or {}).get("line") or 0)
    owner_line, start, end, owner_name, original = locate_declaration(text, owner, line)
    candidate_decl = transform(original, variant)
    if variant != "baseline" and candidate_decl == original:
        raise RuntimeError("candidate is a no-op")
    candidate_text = text[:start] + candidate_decl + text[end:]
    source.write_text(candidate_text, encoding="utf-8")

    raw = source.read_bytes()
    audit = forbidden_audit(raw.decode("utf-8"))
    if any(audit.values()):
        raise RuntimeError(f"forbidden token audit failed: {audit}")
    result = {
        "schema": "qym-auto-producer-candidate-v2",
        "variant": variant,
        "owner": owner_name,
        "owner_line": owner_line,
        "candidate_qym_sha256": hashlib.sha256(raw).hexdigest(),
        "candidate_qym_blob": git_blob(raw),
        "bytes": len(raw),
        "lf": raw.count(b"\n"),
        "forbidden": audit,
    }
    (out / "PATCH_RESULT.json").write_text(
        json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    (out / "TARGET_ORIGINAL.lean").write_text(original, encoding="utf-8")
    (out / "TARGET_CANDIDATE.lean").write_text(candidate_decl, encoding="utf-8")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
