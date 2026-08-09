#!/usr/bin/env python3
from __future__ import annotations

import argparse
import concurrent.futures
import dataclasses
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import urllib.request

ROOT = Path(__file__).resolve().parents[1]
PVS = ROOT / "PrimalitySheafVerification"
HELPER_PATH = ROOT / "scripts" / "fa394_tournament_solver.py"
spec = importlib.util.spec_from_file_location("fa394_helper_for_fa401", HELPER_PATH)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot import {HELPER_PATH}")
M = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = M
spec.loader.exec_module(M)

EVIDENCE = ROOT / "build-logs" / "fa401-extended-frontier"
STATE = EVIDENCE / "STATE.json"
FINAL = EVIDENCE / "FINAL_STATUS.json"
MARKER = EVIDENCE / "ALL_REQUIRED_TARGETS_2X_PASS"
BRANCH = os.environ.get("FA401_BRANCH", "fix/fa401-extended-frontier-20260809")

PREFERRED_MODELS = [
    "openai/gpt-5", "openai/gpt-5-mini", "openai/o3", "openai/o4-mini",
    "openai/gpt-4.1", "xai/grok-3-mini", "deepseek/DeepSeek-V3-0324",
    "mistral-ai/Mistral-Large-2411", "qwen/Qwen3-235B-A22B",
]
ERROR_POS = re.compile(r"\.lean:(\d+):(\d+):\s+error:")


@dataclasses.dataclass(frozen=True)
class ExtendedMetric:
    lean: object
    declaration_ordinal: int
    declaration_name: str
    errors_in_declaration: int
    normalized_token_offset: int

    @property
    def passed(self) -> bool:
        return bool(self.lean.passed)

    def score(self) -> tuple[int, int, int, int, int]:
        if self.passed:
            return (2, 10**9, 0, 10**9, 0)
        return (
            1,
            self.declaration_ordinal,
            -self.errors_in_declaration,
            self.normalized_token_offset,
            -int(self.lean.errors),
        )

    def better_than(self, other: "ExtendedMetric") -> bool:
        return self.score() > other.score()

    def to_json(self) -> dict[str, object]:
        return {
            "lean": self.lean.to_json(),
            "declaration_ordinal": self.declaration_ordinal,
            "declaration_name": self.declaration_name,
            "errors_in_declaration": self.errors_in_declaration,
            "normalized_token_offset": self.normalized_token_offset,
            "score": self.score(),
        }


def catalog_models(token: str) -> list[str]:
    request = urllib.request.Request(
        "https://models.github.ai/catalog/models",
        headers={"Authorization": f"Bearer {token}", "Accept": "application/vnd.github+json", "X-GitHub-Api-Version": "2022-11-28"},
    )
    available: list[str] = []
    try:
        with urllib.request.urlopen(request, timeout=90) as response:
            payload = json.loads(response.read().decode())
        entries = payload if isinstance(payload, list) else payload.get("models", [])
        for entry in entries:
            if not isinstance(entry, dict):
                continue
            model_id = entry.get("id") or entry.get("name")
            task = str(entry.get("task", "")).lower()
            if model_id and (not task or "chat" in task or "completion" in task):
                available.append(str(model_id))
    except Exception:
        pass
    ordered = [m for m in PREFERRED_MODELS if m in available]
    ordered.extend(m for m in available if m not in ordered)
    return ordered or list(PREFERRED_MODELS)


def choose_models(models: list[str], round_index: int) -> list[str]:
    if len(models) <= 4:
        return models
    start = (round_index * 3) % len(models)
    rotated = models[start:] + models[:start]
    out: list[str] = []
    pubs: set[str] = set()
    for model in rotated:
        pub = model.split("/", 1)[0]
        if pub not in pubs or len(out) >= 2:
            out.append(model); pubs.add(pub)
        if len(out) == 4:
            break
    return out


def declaration_table(source: str) -> list[tuple[int, int, str]]:
    lines = source.splitlines()
    starts = [i for i, line in enumerate(lines) if M.H.DECL_RE.match(line)]
    table: list[tuple[int, int, str]] = []
    for pos, start in enumerate(starts):
        end = starts[pos + 1] if pos + 1 < len(starts) else len(lines)
        m = re.match(
            r"^(?:(?:noncomputable|private|protected|public|opaque)\s+)*"
            r"(?:theorem|lemma|corollary|def|abbrev|instance|structure|class|inductive)"
            r"(?:\s+([A-Za-z0-9_'.]+))?",
            lines[start],
        )
        name = m.group(1) if m and m.group(1) else lines[start][:100]
        table.append((start, end, name))
    return table


def extended_metric(source: str, lean_metric, log_text: str) -> ExtendedMetric:
    if lean_metric.passed:
        return ExtendedMetric(lean_metric, 10**9, "(passed)", 0, 10**9)
    table = declaration_table(source)
    line_idx = max(0, int(lean_metric.first_line) - 1)
    ordinal = -1; start = 0; end = len(source.splitlines()); name = "(preamble)"
    for i, (s, e, n) in enumerate(table):
        if s <= line_idx < e:
            ordinal, start, end, name = i, s, e, n
            break
        if s <= line_idx:
            ordinal, start, end, name = i, s, e, n
    positions = [(int(a) - 1, int(b)) for a, b in ERROR_POS.findall(log_text)]
    in_decl = sum(1 for line, _ in positions if start <= line < end)
    lines = source.splitlines()
    prefix = "\n".join(lines[start : min(line_idx + 1, end)])
    clean = M.H.strip_comments_and_strings(prefix)
    tokens = len(re.findall(r"[A-Za-z_][A-Za-z0-9_'.]*|\S", clean))
    return ExtendedMetric(lean_metric, ordinal, name, max(1, in_decl), tokens)


def compile_source(path: Path, source: str, log_path: Path, max_errors: int = 20) -> ExtendedMetric:
    original = path.read_text(encoding="utf-8")
    path.write_text(source, encoding="utf-8")
    try:
        lean = M.H.compile_file(path, log_path, max_errors=max_errors, timeout=1500)
        log = log_path.read_text(encoding="utf-8", errors="replace")
        return extended_metric(source, lean, log)
    finally:
        path.write_text(original, encoding="utf-8")


def fetch_sources() -> dict[str, str]:
    branches = {
        "pass391":"fix/fa391-final-gate-20260809",
        "pass398":"fix/fa398-single-run-tournament-loop-20260809",
        "pass399":"fix/fa399-single-run-proof-body-loop-20260809",
        "pass400":"fix/fa400-fast-frontier-20260809",
        "pr9":"ci/fa319-isolated-20260807",
    }
    out: dict[str, str] = {}
    for label, branch in branches.items():
        source = M.fetch_branch_source(branch, f"fa401-{label}")
        if source is not None:
            out[label] = source
    return out


def select_baseline(path: Path, candidates: dict[str, str]) -> tuple[str, ExtendedMetric, str]:
    EVIDENCE.mkdir(parents=True, exist_ok=True)
    current = path.read_text(encoding="utf-8")
    headers = M.H.declaration_headers(current)
    all_sources = {"current": current, **candidates}
    best_source = current; best_metric = None; best_label = "current"; records=[]; seen=set()
    for label, source in all_sources.items():
        digest = M.H.sha256_bytes(source.encode())
        if digest in seen: continue
        seen.add(digest)
        if M.H.declaration_headers(source) != headers:
            records.append({"label":label,"rejected":"headers"}); continue
        bad = M.H.forbidden_counts(source)
        if any(bad.values()):
            records.append({"label":label,"rejected":f"forbidden {bad}"}); continue
        metric = compile_source(path, source, EVIDENCE / f"baseline-{label}.log", 20)
        records.append({"label":label,"sha256":digest,"metric":metric.to_json()})
        if best_metric is None or metric.better_than(best_metric):
            best_metric=metric; best_source=source; best_label=label
    if best_metric is None: raise RuntimeError("no admissible baseline")
    path.write_text(best_source, encoding="utf-8")
    (EVIDENCE/"baseline-selection.json").write_text(json.dumps({"selected":best_label,"metric":best_metric.to_json(),"candidates":records},indent=2))
    return best_source,best_metric,best_label


def commit_progress(round_index: int, metric: ExtendedMetric) -> None:
    STATE.write_text(json.dumps({"round":round_index,"metric":metric.to_json(),"source_sha256":M.H.sha256_file(PVS/'Mock2_FunctionalAnalysis.lean')},indent=2))
    subprocess.run(["git","add","PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean",str(STATE.relative_to(ROOT))],cwd=ROOT,check=True)
    if subprocess.run(["git","diff","--cached","--quiet"],cwd=ROOT).returncode != 0:
        subprocess.run(["git","commit","-m",f"fix: advance PASS 401 extended frontier round {round_index}"],cwd=ROOT,check=True)
        subprocess.run(["git","push","origin",f"HEAD:{BRANCH}"],cwd=ROOT,check=True)


def query_candidates(source: str, metric: ExtendedMetric, log_text: str, token: str, models: list[str], round_index: int) -> list[tuple[str,str]]:
    prompt,start,end = M.build_prompt(PVS/'Mock2_FunctionalAnalysis.lean',source,metric,log_text,round_index)
    prompt += "\nThe acceptance metric compares top-level declaration ordinal, remaining errors inside that declaration, and normalized token offset. Fix the complete root issue; adding blank lines or unrelated code cannot count as progress.\n"
    (EVIDENCE/f"round-{round_index:03d}-prompt.txt").write_text(prompt)
    jobs=[(m,s) for m in models for s in range(2)]; responses=[]
    with concurrent.futures.ThreadPoolExecutor(max_workers=min(10,len(jobs))) as pool:
        futs={pool.submit(M.H.model_request,m,prompt,token,s):(m,s) for m,s in jobs}
        for fut in concurrent.futures.as_completed(futs):
            m,s=futs[fut]
            try: _,content=fut.result()
            except Exception as exc: content=f"<ERROR>{exc!r}</ERROR>"
            responses.append((m,s,content))
    out=[]; seen=set()
    for m,s,content in responses:
        safe=re.sub(r"[^A-Za-z0-9_.-]+","_",m)
        (EVIDENCE/f"round-{round_index:03d}-response-{safe}-{s}.txt").write_text(content)
        for cand in M.response_candidates(source,content,start,end):
            digest=M.H.sha256_bytes(cand.encode())
            if digest in seen or cand==source: continue
            seen.add(digest); out.append((f"{safe}-{s}-{digest[:10]}",cand))
    out.sort(key=lambda x:abs(len(x[1])-len(source)))
    return out


def main() -> int:
    parser=argparse.ArgumentParser(); parser.add_argument('--rounds',type=int,default=18); parser.add_argument('--candidates',type=int,default=5); args=parser.parse_args()
    token=os.environ.get('GITHUB_TOKEN','')
    if not token: raise SystemExit('GITHUB_TOKEN required')
    EVIDENCE.mkdir(parents=True,exist_ok=True)
    path=PVS/'Mock2_FunctionalAnalysis.lean'
    source,metric,label=select_baseline(path,fetch_sources())
    commit_progress(0,metric)
    headers=M.H.declaration_headers(source); models_all=catalog_models(token); history=[{'round':0,'metric':metric.to_json(),'selected':label}]
    no_progress=0
    for r in range(1,args.rounds+1):
        source=path.read_text(encoding='utf-8')
        log_path=EVIDENCE/("baseline-"+label+".log" if r==1 else f"round-{r-1:03d}-accepted.log")
        if not log_path.exists(): log_path=next(iter(sorted(EVIDENCE.glob('baseline-*.log'))),EVIDENCE/'missing.log')
        log_text=log_path.read_text(encoding='utf-8',errors='replace') if log_path.exists() else ''
        models=choose_models(models_all,r)
        candidates=query_candidates(source,metric,log_text,token,models,r)[:args.candidates]
        diagnostics=[]; best_metric=None; best_source=None
        for idx,(lab,cand) in enumerate(candidates):
            if M.H.declaration_headers(cand)!=headers:
                diagnostics.append({'label':lab,'rejected':'headers'}); continue
            bad=M.H.forbidden_counts(cand)
            if any(bad.values()): diagnostics.append({'label':lab,'rejected':f'forbidden {bad}'}); continue
            cm=compile_source(path,cand,EVIDENCE/f"round-{r:03d}-candidate-{idx:02d}.log",20)
            diagnostics.append({'label':lab,'metric':cm.to_json()})
            if cm.better_than(metric) and (best_metric is None or cm.better_than(best_metric)):
                best_metric=cm; best_source=cand
        (EVIDENCE/f"round-{r:03d}-candidates.json").write_text(json.dumps(diagnostics,indent=2))
        if best_metric is None or best_source is None:
            no_progress+=1; history.append({'round':r,'accepted':False,'metric':metric.to_json()})
            (EVIDENCE/'history.json').write_text(json.dumps(history,indent=2))
            if no_progress>=4: break
            continue
        no_progress=0; path.write_text(best_source,encoding='utf-8')
        lean=M.H.compile_file(path,EVIDENCE/f"round-{r:03d}-accepted.log",max_errors=20,timeout=1500)
        metric=extended_metric(best_source,lean,(EVIDENCE/f"round-{r:03d}-accepted.log").read_text(errors='replace'))
        history.append({'round':r,'accepted':True,'metric':metric.to_json()}); (EVIDENCE/'history.json').write_text(json.dumps(history,indent=2)); (EVIDENCE/'best-source.lean').write_text(best_source)
        commit_progress(r,metric)
        if metric.passed: break

    full=M.H.compile_file(path,EVIDENCE/'full-frontier.log',max_errors=350,timeout=1800)
    summary={'complete':False,'stage':'Mock2_FunctionalAnalysis','baseline':label,'extended_metric':metric.to_json(),'full_metric':full.to_json()}
    M.EVIDENCE=EVIDENCE/'ordered'
    if full.passed:
        ordered=M.verify_ordered(token,choose_models(models_all,99),fa_rounds=1,downstream_rounds=10,max_candidates=5,max_errors=250); summary.update(ordered)
    else: summary['reason']='full FA compile still fails after extended frontier rounds'
    FINAL.write_text(json.dumps(summary,indent=2))
    targets=[PVS/'Mock2_FunctionalAnalysis.lean',PVS/'Mock2_FunctionalAnalysis_Integrated.lean',*sorted(PVS.glob('Mock3*.lean')),PVS/'QYM.lean']
    subprocess.run(['git','add',*(str(p.relative_to(ROOT)) for p in targets if p.exists()),str(FINAL.relative_to(ROOT))],cwd=ROOT,check=True)
    if summary.get('complete'):
        MARKER.write_text('SUCCESS_ALL_REQUIRED_TARGETS_2X_PASS\n'); subprocess.run(['git','add',str(MARKER.relative_to(ROOT))],cwd=ROOT,check=True)
    if subprocess.run(['git','diff','--cached','--quiet'],cwd=ROOT).returncode!=0:
        subprocess.run(['git','commit','-m','ci: record PASS 401 final status'],cwd=ROOT,check=True); subprocess.run(['git','push','origin',f'HEAD:{BRANCH}'],cwd=ROOT,check=True)
    return 0 if summary.get('complete') else 2

if __name__=='__main__': raise SystemExit(main())
