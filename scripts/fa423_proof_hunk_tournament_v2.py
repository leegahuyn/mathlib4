from __future__ import annotations

import fa423_proof_hunk_tournament as mod

engine = mod.engine
core = mod.core
whole_proof_collect = mod._original_collect


def collect_candidates(source, current, branches):
    result = []
    seen = {mod.sha256(source)}
    limit = engine.MAX_CANDIDATES
    hunk_budget = max(1, int(limit * 0.8))

    for label, candidate in mod.local_instance_candidates(source, current):
        digest = mod.sha256(candidate)
        if digest in seen:
            continue
        seen.add(digest)
        result.append((label, candidate))
        if len(result) >= hunk_budget:
            return result

    expected_imports = core.imports(source)
    for donor_label, donor in core.donor_sources(branches):
        if len(result) >= hunk_budget:
            break
        if not core.valid_donor(donor, expected_imports):
            continue
        for donor_decl in engine.same_name_declarations(donor, current):
            for label, candidate in mod.donor_hunk_candidates(
                source, current, donor, donor_decl, donor_label
            ):
                digest = mod.sha256(candidate)
                if digest in seen:
                    continue
                seen.add(digest)
                result.append((label, candidate))
                if len(result) >= hunk_budget:
                    break
            if len(result) >= hunk_budget:
                break

    for label, candidate in whole_proof_collect(source, current, branches):
        if len(result) >= limit:
            break
        digest = mod.sha256(candidate)
        if digest in seen:
            continue
        seen.add(digest)
        result.append((f"whole-proof:{label}", candidate))
    return result


engine.collect_candidates = collect_candidates

if __name__ == "__main__":
    raise SystemExit(engine.main())
