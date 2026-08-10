#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import os
import shutil
from pathlib import Path

EXPECTED = [
    "champion",
    "proof_explicit",
    "proof_explicit_height",
    "namespace_explicit",
    "namespace_explicit_height",
]
CHAMPION_SHA = "c12778aa72fa9541b064e466d59c854283766e73c02fda1a586cf7380e7f7626"
CHAMPION_RANK = (0, 2671, 32592, 5)
EXPECTED_LINES = 60453


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def rank(metric: dict) -> tuple[int, int, int, int]:
    if int(metric["FA_exit"]) == 0:
        return (1, 10**9, 10**9, 10**9)
    return (0, int(metric.get("FA_error_declaration_index", -1)),
            int(metric.get("FA_first_actual_error_line", 0)),
            int(metric.get("FA_first_actual_error_col", 0)))


def incomplete(metric: dict, source: Path) -> list[str]:
    r: list[str] = []
    if metric.get("classification") != "VERIFIED": r.append("metric_not_verified")
    if metric.get("all_required_lean_commands_executed") is not True: r.append("lean_not_executed")
    if sha(source) != metric.get("source_sha256"): r.append("source_sha_mismatch")
    if int(metric.get("line_count", 0)) != EXPECTED_LINES: r.append("line_count")
    if metric.get("same_height") is not True: r.append("not_same_height")
    if metric.get("theorem_header_unchanged") is not True: r.append("header_changed")
    if int(metric.get("Mock2_exit", 999)) != 0 or int(metric.get("Mock2_errors_under_cap", 999)) != 0:
        r.append("Mock2_not_clean")
    if int(metric.get("Mock2_Advanced_exit", 999)) != 0 or int(metric.get("Mock2_Advanced_errors_under_cap", 999)) != 0:
        r.append("Mock2_Advanced_not_clean")
    if metric.get("forbidden_clean") is not True: r.append("forbidden_audit")
    return r


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--collected", required=True)
    ap.add_argument("--output", required=True)
    args = ap.parse_args()
    root, out = Path(args.collected), Path(args.output)
    out.mkdir(parents=True, exist_ok=True)
    loaded: dict[str, tuple[dict, Path]] = {}
    rows: list[dict] = []
    for v in EXPECTED:
        d=root/v; mp=d/'METRIC.json'; sp=d/'Mock2_FunctionalAnalysis-candidate.lean'
        if not mp.exists() or not sp.exists():
            raise RuntimeError(f"INFRA FAILURE: missing metric/source for {v}")
        m=json.loads(mp.read_text())
        if m.get('variant') != v:
            raise RuntimeError(f"INFRA FAILURE: variant mismatch for {v}")
        reasons=incomplete(m,sp)
        if reasons:
            raise RuntimeError(f"INFRA FAILURE: incomplete direct metric {v}: {reasons}")
        loaded[v]=(m,sp)
        rows.append({'variant':v,'source_sha256':m['source_sha256'],'Lean_executed':True,
                     'Mock2_exit':m['Mock2_exit'],'Mock2_Advanced_exit':m['Mock2_Advanced_exit'],
                     'FA_exit':m['FA_exit'],'first_line':m['FA_first_actual_error_line'],
                     'first_col':m['FA_first_actual_error_col'],'declaration':m['FA_first_error_declaration'],
                     'declaration_index':m['FA_error_declaration_index']})
    champion, csrc=loaded['champion']
    if champion['source_sha256'] != CHAMPION_SHA or sha(csrc) != CHAMPION_SHA or rank(champion) != CHAMPION_RANK:
        raise RuntimeError(f"INFRA FAILURE: current-run champion metric mismatch: {rank(champion)}")
    best_variant=max(EXPECTED,key=lambda v:rank(loaded[v][0]))
    best,bsource=loaded[best_variant]
    strict=rank(best)>CHAMPION_RANK
    if int(best['FA_exit'])==0: classification='FA_PASS_CANDIDATE'
    elif strict and int(best['FA_error_declaration_index'])>CHAMPION_RANK[1]: classification='DECLARATION_BREAKTHROUGH'
    elif strict: classification='SMALL_SAME_DECLARATION_ADVANCE'
    else: classification='NO_IMPROVEMENT'
    result={'classification':classification,'strict_promotion':strict,
            'authority':'complete current-run direct Lean CLI matrix',
            'champion':champion,'best':best,'candidate_results':rows}
    (out/'SELECTION.json').write_text(json.dumps(result,indent=2)+'\n')
    (out/'CANDIDATE_RESULTS.json').write_text(json.dumps(rows,indent=2)+'\n')
    shutil.copy2(bsource,out/'Mock2_FunctionalAnalysis-selected.lean')
    shutil.copy2(root/best_variant/'METRIC.json',out/'CHOSEN_METRIC.json')
    print(json.dumps(result,indent=2))
    with open(os.environ['GITHUB_OUTPUT'],'a') as f:
        f.write(f"strict={str(strict).lower()}\nvariant={best_variant}\nsource_sha256={best['source_sha256']}\n")
        f.write(f"fa_exit={best['FA_exit']}\nfirst_line={best['FA_first_actual_error_line']}\n")
        f.write(f"first_col={best['FA_first_actual_error_col']}\ndeclaration={best['FA_first_error_declaration']}\n")
        f.write(f"classification={classification}\n")

if __name__ == '__main__':
    main()
