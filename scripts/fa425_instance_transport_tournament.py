from __future__ import annotations

import hashlib
from typing import Any

import fa424_cross_donor_hunk_tournament as cross

engine = cross.engine
core = cross.core
cross_collect = cross.collect_candidates
mod = cross.prior.mod


def sha256(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def mutate_block(
    source: str,
    current: Any,
    label: str,
    replacements: list[tuple[str, str]],
) -> tuple[str, str] | None:
    block = mod.declaration_block(source, current)
    mutated = block
    for old, new in replacements:
        if mutated.count(old) != 1:
            return None
        mutated = mutated.replace(old, new)
    candidate = mod.rebuild_candidate(source, current, mutated)
    if candidate is None:
        return None
    return label, candidate


def local_transport_candidates(source: str, current: Any) -> list[tuple[str, str]]:
    if current.name != "actualEdgeAmbientParam_hasDerivAt":
        return []

    canonical = (
        "  letI : AddCommGroup ℂ := "
        "Complex.instNormedAddCommGroup.toAddCommGroup"
    )
    legacy = "  letI : AddCommGroup Complex := Complex.addCommGroup"
    simpa = (
        "  simpa [actualEdgeAmbientParam, actualEdgeNativeVelocity,\n"
        "    Function.comp_def, modularTileEdgeAmbientVelocity_eq] using hcomp"
    )

    instance_policies: list[tuple[str, list[tuple[str, str]]]] = [
        ("instances-current", []),
        ("instances-reversed", [
            (canonical, "  letI : AddCommGroup ℂ := Complex.addCommGroup"),
            (legacy, "  letI : AddCommGroup Complex := Complex.instNormedAddCommGroup.toAddCommGroup"),
        ]),
        ("instances-canonical-only", [
            (legacy, "  -- keep the canonical normed additive structure"),
        ]),
        ("instances-legacy-only", [
            (canonical, "  -- use the theorem-header additive structure"),
        ]),
        ("instances-both-canonical", [
            (legacy, "  letI : AddCommGroup Complex := Complex.instNormedAddCommGroup.toAddCommGroup"),
        ]),
        ("instances-both-legacy", [
            (canonical, "  letI : AddCommGroup ℂ := Complex.addCommGroup"),
        ]),
        ("instances-none", [
            (canonical, "  -- no local additive override: canonical theorem instances only"),
            (legacy, "  -- no second local additive override"),
        ]),
    ]

    final_policies: list[tuple[str, str]] = [
        ("simpa-current", simpa),
        (
            "convert-simp",
            "  convert hcomp using 1 <;> simp [actualEdgeAmbientParam,\n"
            "    actualEdgeNativeVelocity, Function.comp_def, modularTileEdgeAmbientVelocity_eq]",
        ),
        (
            "convert-rfl",
            "  convert hcomp using 1 <;> rfl\n"
            "  -- same-height padding after dependent conversion",
        ),
        (
            "exact-reducible",
            "  with_reducible_and_instances exact hcomp\n"
            "  -- same-height padding after reducible-instance exact",
        ),
        (
            "simpa-unfold-instances",
            "  simpa [actualEdgeAmbientParam, actualEdgeNativeVelocity,\n"
            "    Function.comp_def, modularTileEdgeAmbientVelocity_eq, Complex.addCommGroup,\n"
            "    Complex.instNormedAddCommGroup] using hcomp",
        ),
        (
            "simpa-comp-apply",
            "  simpa [actualEdgeAmbientParam, actualEdgeNativeVelocity,\n"
            "    Function.comp_apply, modularTileEdgeAmbientVelocity_eq] using hcomp",
        ),
    ]

    result: list[tuple[str, str]] = []
    seen = {sha256(source)}

    def add(item: tuple[str, str] | None) -> None:
        if item is None:
            return
        label, candidate = item
        digest = sha256(candidate)
        if digest in seen:
            return
        if len(candidate.splitlines()) != len(source.splitlines()):
            # Same-declaration comparisons in this phase must preserve file height.
            return
        if any(core.forbidden_hits(candidate).values()):
            return
        seen.add(digest)
        result.append((label, candidate))

    # Prioritize the minimal changes most likely to solve the dependent instance cast.
    priority = [
        ("instances-current", "convert-simp"),
        ("instances-current", "simpa-unfold-instances"),
        ("instances-reversed", "simpa-current"),
        ("instances-canonical-only", "simpa-current"),
        ("instances-legacy-only", "simpa-current"),
        ("instances-none", "simpa-current"),
        ("instances-reversed", "convert-simp"),
        ("instances-canonical-only", "convert-simp"),
        ("instances-legacy-only", "convert-simp"),
        ("instances-current", "convert-rfl"),
        ("instances-current", "exact-reducible"),
        ("instances-current", "simpa-comp-apply"),
    ]
    ip = {name: repls for name, repls in instance_policies}
    fp = {name: body for name, body in final_policies}
    for iname, fname in priority:
        replacements = list(ip[iname])
        if fp[fname] != simpa:
            replacements.append((simpa, fp[fname]))
        add(mutate_block(source, current, f"transport:{iname}:{fname}", replacements))

    for iname, instance_replacements in instance_policies:
        for fname, final_body in final_policies:
            replacements = list(instance_replacements)
            if final_body != simpa:
                replacements.append((simpa, final_body))
            add(mutate_block(source, current, f"transport:{iname}:{fname}", replacements))

    equality_bodies = [
        (
            "group-eq-rfl",
            "  have hgroups : Complex.instNormedAddCommGroup.toAddCommGroup =\n"
            "      Complex.addCommGroup := by rfl\n"
            "  cases hgroups\n"
            + simpa,
        ),
        (
            "group-eq-ext",
            "  have hgroups : Complex.instNormedAddCommGroup.toAddCommGroup =\n"
            "      Complex.addCommGroup := by ext <;> rfl\n"
            "  cases hgroups\n"
            + simpa,
        ),
        (
            "group-eq-structure-ext",
            "  have hgroups : Complex.instNormedAddCommGroup.toAddCommGroup =\n"
            "      Complex.addCommGroup := by apply AddCommGroup.ext <;> rfl\n"
            "  cases hgroups\n"
            + simpa,
        ),
        (
            "group-eq-symm-ext",
            "  have hgroups : Complex.addCommGroup =\n"
            "      Complex.instNormedAddCommGroup.toAddCommGroup := by ext <;> rfl\n"
            "  cases hgroups\n"
            + simpa,
        ),
    ]
    for label, body in equality_bodies:
        item = mutate_block(source, current, f"transport:{label}", [(simpa, body)])
        if item is not None:
            name, candidate = item
            digest = sha256(candidate)
            if digest not in seen and not any(core.forbidden_hits(candidate).values()):
                seen.add(digest)
                result.append((name, candidate))

    return result


def collect_candidates(source: str, current: Any, branches: list[str]):
    limit = engine.MAX_CANDIDATES
    result: list[tuple[str, str]] = []
    seen = {sha256(source)}

    for label, candidate in local_transport_candidates(source, current):
        digest = sha256(candidate)
        if digest in seen:
            continue
        seen.add(digest)
        result.append((label, candidate))
        if len(result) >= limit:
            return result

    for label, candidate in cross_collect(source, current, branches):
        digest = sha256(candidate)
        if digest in seen:
            continue
        seen.add(digest)
        result.append((label, candidate))
        if len(result) >= limit:
            break
    return result


engine.collect_candidates = collect_candidates

if __name__ == "__main__":
    raise SystemExit(engine.main())
