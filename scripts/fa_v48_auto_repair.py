#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path

BASE_SHA = "c255c100f33c09cafc37276f967b9cd535e0ddd76460df149d71d632d8644a63"
BASE_BYTES = 2795882
BASE_LINES = 62555
BASE_DECLS = 4416
TRUST = ("sorry", "admit", "axiom", "unsafe", "native_decide", "Lean.ofReduceBool")
DECL_RE = re.compile(
    r"(?m)^(?:protected\s+|private\s+|noncomputable\s+|local\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance|structure|class)\s+([^\s(:]+)"
)


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


def declaration_ranges(text: str) -> dict[str, tuple[int, int]]:
    matches = list(DECL_RE.finditer(text))
    result: dict[str, tuple[int, int]] = {}
    for i, match in enumerate(matches):
        start = match.start()
        end = matches[i + 1].start() if i + 1 < len(matches) else len(text)
        result[match.group(1)] = (start, end)
    return result


def replace_declaration(text: str, name: str, transform) -> tuple[str, dict[str, object]]:
    ranges = declaration_ranges(text)
    if name not in ranges:
        raise RuntimeError(f"declaration not found: {name}")
    start, end = ranges[name]
    before = text[start:end]
    after, detail = transform(before)
    if after == before:
        raise RuntimeError(f"declaration patch made no change: {name}")
    return text[:start] + after + text[end:], {"declaration": name, **detail}


def replace_optional_once(text: str, old: str, new: str, label: str) -> tuple[str, dict[str, object]]:
    count = text.count(old)
    if count > 1:
        raise RuntimeError(f"{label}: expected at most one exact block, got {count}")
    if count == 0:
        return text, {"patch": label, "applied": False, "reason": "old block absent"}
    return text.replace(old, new, 1), {"patch": label, "applied": True, "exact_count": 1}


PLANE_CONJ_OLD = '''  rw [literalStagePlaneWaveRepresentative, if_pos hw]
  calc
    literalStageNegativePlaneWave Y k w =
        ((literalStageFourierScale Y)⁻¹ : ℂ) *
          UnitAddTorus.mFourier (-k)
            (literalStagePhysicalTorusPoint Y w) := by
      simp only [literalStageNegativePlaneWave, UnitAddTorus.mFourier,
        literalStagePhysicalTorusPoint, ContinuousMap.coe_mk, Pi.neg_apply]
      rw [Fin.prod_univ_two]
      ring
    _ = ((literalStageFourierScale Y)⁻¹ : ℂ) *
          Complex.conj (UnitAddTorus.mFourier k
            (literalStagePhysicalTorusPoint Y w)) := by
      rw [UnitAddTorus.mFourier_neg]
    _ = star (((literalStageFourierScale Y)⁻¹ : ℂ) *
          UnitAddTorus.mFourier k
            (literalStagePhysicalTorusPoint Y w)) := by
      simp only [star_mul', Complex.star_def, Complex.conj_ofReal]'''

PLANE_CONJ_NEW = '''  rw [literalStagePlaneWaveRepresentative, if_pos hw]
  calc
    literalStageNegativePlaneWave Y k w =
        ((literalStageFourierScale Y)⁻¹ : ℂ) *
          UnitAddTorus.mFourier (-k)
            (literalStagePhysicalTorusPoint Y w) := by
      simp only [literalStageNegativePlaneWave, UnitAddTorus.mFourier,
        literalStagePhysicalTorusPoint, Complex.measurableEquivPi_apply,
        ContinuousMap.coe_mk, Pi.neg_apply]
      rw [Fin.prod_univ_two]
      ring_nf
    _ = ((literalStageFourierScale Y)⁻¹ : ℂ) *
          star (UnitAddTorus.mFourier k
            (literalStagePhysicalTorusPoint Y w)) := by
      simpa only [starRingEnd_apply] using
        congrArg (fun z : ℂ => ((literalStageFourierScale Y)⁻¹ : ℂ) * z)
          (UnitAddTorus.mFourier_neg (n := k)
            (x := literalStagePhysicalTorusPoint Y w))
    _ = star (((literalStageFourierScale Y)⁻¹ : ℂ) *
          UnitAddTorus.mFourier k
            (literalStagePhysicalTorusPoint Y w)) := by
      simp [star_mul']'''

ONE_NAMES_OLD = '''    simp only [one_div, one_re, one_im, Complex.add_re, Complex.add_im,
      Complex.real_smul, smul_eq_mul, mul_one, add_zero, zero_mul,
      Complex.ofReal_inv, Complex.ofReal_mul] <;>
    field_simp [literalStageFourierScale_ne_zero Y] <;> ring'''
ONE_NAMES_NEW = '''    try simp only [one_div, Complex.one_re, Complex.one_im,
      Complex.add_re, Complex.add_im, Complex.real_smul, smul_eq_mul,
      mul_one, add_zero, zero_mul, Complex.ofReal_inv, Complex.ofReal_mul] <;>
    field_simp [literalStageFourierScale_ne_zero Y] <;> ring'''

I_NAMES_OLD = '''    simp only [one_div, Complex.I_re, Complex.I_im, Complex.add_re,
      Complex.add_im, Complex.real_smul, smul_eq_mul, mul_one, add_zero,
      zero_mul, Complex.ofReal_inv, Complex.ofReal_mul] <;>
    field_simp [literalStageFourierScale_ne_zero Y] <;> ring'''
I_NAMES_NEW = '''    try simp only [one_div, Complex.I_re, Complex.I_im, Complex.add_re,
      Complex.add_im, Complex.real_smul, smul_eq_mul, mul_one, add_zero,
      zero_mul, Complex.ofReal_inv, Complex.ofReal_mul] <;>
    field_simp [literalStageFourierScale_ne_zero Y] <;> ring'''


def patch_frontier_ut(text: str) -> tuple[str, dict[str, object]]:
    name = "integrable_fullPlaneTest_mul_kernel_mul_translate"

    def transform(body: str):
        pattern = re.compile(
            r"(?ms)(?P<indent>^[ \t]*)simpa"
            r"(?P<middle>(?:\s+only)?(?:\s*\[[^\]]*\])?)\s+using\s+h(?P<tail>[ \t]*)(?=\n|$)"
        )
        matches = list(pattern.finditer(body))
        if not matches:
            raise RuntimeError(f"{name}: no simpa ... using h frontier found")
        target = matches[-1]
        replacement = f"{target.group('indent')}simpa [ut] using h{target.group('tail')}"
        return body[: target.start()] + replacement + body[target.end() :], {
            "patch": "frontier_ut_unfold",
            "frontier_matches": len(matches),
            "selected_match": len(matches),
        }

    return replace_declaration(text, name, transform)


def patch_plane_conj(text: str) -> tuple[str, dict[str, object]]:
    return replace_optional_once(text, PLANE_CONJ_OLD, PLANE_CONJ_NEW, "plane_conj_exact")


def patch_one_names(text: str) -> tuple[str, dict[str, object]]:
    return replace_optional_once(text, ONE_NAMES_OLD, ONE_NAMES_NEW, "complex_one_names")


def patch_i_names(text: str) -> tuple[str, dict[str, object]]:
    return replace_optional_once(text, I_NAMES_OLD, I_NAMES_NEW, "complex_I_names")


def diagnostic_declarations(path: Path | None) -> list[str]:
    if path is None or not path.exists():
        return []
    names: list[str] = []
    for line in path.read_text(errors="replace").splitlines():
        try:
            row = json.loads(line)
        except json.JSONDecodeError:
            continue
        if str(row.get("severity", "")).lower() != "error":
            continue
        for key in ("declaration", "declaration_name", "enclosing_declaration"):
            value = row.get(key)
            if isinstance(value, str) and value and value not in names:
                names.append(value)
                break
    return names


def patch_error_declarations(
    text: str,
    names: list[str],
    *,
    enrich_simpa: bool,
    ring_nf: bool,
    negative_wave: bool,
) -> tuple[str, dict[str, object]]:
    ranges = declaration_ranges(text)
    targets = [name for name in names if name in ranges]
    if not targets:
        # The artifact format may omit declaration fields. Use narrowly scoped names/keywords,
        # never all declarations.
        targets = [
            name
            for name in ranges
            if any(
                token in name
                for token in (
                    "fullPlaneTest",
                    "literalStageNegativePlaneWave",
                    "ambientPlaneToUpper",
                    "HalfWeightCompactCoordinateGreen",
                    "adjoint",
                )
            )
        ]
    applied: list[dict[str, object]] = []
    for name in reversed(targets):
        ranges = declaration_ranges(text)
        start, end = ranges[name]
        body = text[start:end]
        before = body
        extras: list[str] = []
        if enrich_simpa:
            if "Function.comp" in body or "∘" in body:
                extras.append("Function.comp_def")
            if "ContinuousMap" in body:
                extras.append("ContinuousMap.coe_mk")
            if "ambientPlaneToUpper" in body:
                extras.append("ambientPlaneToUpper")
            if "Complex.measurableEquivPi" in body:
                extras.append("Complex.measurableEquivPi_apply")
            if "Pi.smul" in body:
                extras.append("Pi.smul_apply")
            if negative_wave and "literalStageNegativePlaneWave" in body:
                extras.extend(
                    [
                        "literalStageNegativePlaneWave",
                        "literalStagePhysicalTorusPoint",
                        "UnitAddTorus.mFourier",
                        "ContinuousMap.coe_mk",
                    ]
                )
            # Preserve order while removing duplicates.
            extras = list(dict.fromkeys(extras))
            if extras:
                extra_text = ", ".join(extras)
                body = re.sub(
                    r"(?m)^(?P<i>[ \t]*)simpa\s+using\s+",
                    rf"\g<i>simpa [{extra_text}] using ",
                    body,
                )
                body = re.sub(
                    r"(?m)^(?P<i>[ \t]*)simpa\s+only\s*\[",
                    rf"\g<i>simpa only [{extra_text}, ",
                    body,
                )
        if ring_nf:
            body = re.sub(r"(?m)^(?P<i>[ \t]*)ring(?P<t>[ \t]*)$", r"\g<i>ring_nf\g<t>", body)
        if body != before:
            text = text[:start] + body + text[end:]
            applied.append(
                {
                    "declaration": name,
                    "extras": extras,
                    "ring_nf": ring_nf,
                    "negative_wave": negative_wave,
                }
            )
    return text, {
        "patch": "diagnostic_declaration_enrichment",
        "requested_declarations": len(names),
        "targeted_declarations": len(targets),
        "changed_declarations": len(applied),
        "changes": applied,
    }


VARIANTS = {
    "frontier": ("ut",),
    "frontier_plane": ("ut", "plane"),
    "frontier_names": ("ut", "one", "i"),
    "frontier_plane_names": ("ut", "plane", "one", "i"),
    "frontier_enrich": ("ut", "plane", "one", "i", "enrich"),
    "frontier_ring": ("ut", "plane", "one", "i", "ring"),
    "frontier_enrich_ring": ("ut", "plane", "one", "i", "enrich", "ring"),
    "frontier_broad": ("ut", "plane", "one", "i", "enrich", "ring", "negative"),
}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--base", type=Path, required=True)
    parser.add_argument("--variant", choices=VARIANTS, required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--audit", type=Path, required=True)
    parser.add_argument("--diagnostics", type=Path)
    args = parser.parse_args()

    raw = args.base.read_bytes()
    text = raw.decode()
    if hashlib.sha256(raw).hexdigest() != BASE_SHA:
        raise RuntimeError("v47 base source SHA mismatch")
    if len(raw) != BASE_BYTES or len(text.splitlines()) != BASE_LINES:
        raise RuntimeError("v47 base source size/line mismatch")
    before_decls = DECL_RE.findall(text)
    if len(before_decls) != BASE_DECLS:
        raise RuntimeError("v47 declaration count mismatch")
    before_trust = trust_counts(text)
    if any(before_trust.values()):
        raise RuntimeError(f"v47 base trust audit failed: {before_trust}")

    error_decls = diagnostic_declarations(args.diagnostics)
    operations = VARIANTS[args.variant]
    patch_audit: list[dict[str, object]] = []

    if "ut" in operations:
        text, detail = patch_frontier_ut(text)
        patch_audit.append(detail)
    if "plane" in operations:
        text, detail = patch_plane_conj(text)
        patch_audit.append(detail)
    if "one" in operations:
        text, detail = patch_one_names(text)
        patch_audit.append(detail)
    if "i" in operations:
        text, detail = patch_i_names(text)
        patch_audit.append(detail)
    if any(key in operations for key in ("enrich", "ring", "negative")):
        text, detail = patch_error_declarations(
            text,
            error_decls,
            enrich_simpa="enrich" in operations,
            ring_nf="ring" in operations,
            negative_wave="negative" in operations,
        )
        patch_audit.append(detail)

    after_decls = DECL_RE.findall(text)
    after_trust = trust_counts(text)
    if after_decls != before_decls:
        raise RuntimeError("public declaration sequence changed")
    if any(after_trust.values()):
        raise RuntimeError(f"candidate trust audit failed: {after_trust}")

    data = text.encode()
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_bytes(data)
    audit = {
        "schema": "fa-v48-auto-repair-audit-v1",
        "variant": args.variant,
        "operations": list(operations),
        "base_sha256": BASE_SHA,
        "base_bytes": BASE_BYTES,
        "base_lines": BASE_LINES,
        "base_declarations": BASE_DECLS,
        "source_sha256": hashlib.sha256(data).hexdigest(),
        "source_bytes": len(data),
        "source_lines": len(text.splitlines()),
        "source_declarations": len(after_decls),
        "declaration_sequence_identical": after_decls == before_decls,
        "trust_before": before_trust,
        "trust_after": after_trust,
        "diagnostic_declarations": error_decls,
        "patch_audit": patch_audit,
        "public_header_changes": False,
        "comments_changed": False,
        "attributes_changed": False,
    }
    args.audit.parent.mkdir(parents=True, exist_ok=True)
    args.audit.write_text(json.dumps(audit, indent=2, sort_keys=True) + "\n")
    print(json.dumps(audit, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
