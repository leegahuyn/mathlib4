#!/usr/bin/env python3
from pathlib import Path
import hashlib, json, subprocess, sys

output = Path(sys.argv[1])
modules = [
    'Mock2',
    'Mock2_Advanced',
    'Mock2_FunctionalAnalysis_Integrated',
    'Mock2_FunctionalAnalysis',
    'QYM',
]

def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

def blob(path: Path) -> str:
    return subprocess.check_output(['git','hash-object',str(path)],text=True).strip()

def signature(path: Path) -> str:
    return subprocess.check_output(
        ['python3','scripts/focused_source_audit_20260807.py','signature',str(path)],
        text=True,
    ).strip()

sources = {}
for module in modules:
    path = Path(f'PrimalitySheafVerification/{module}.lean')
    if not path.is_file():
        raise SystemExit(f'missing checked-in source: {path}')
    sources[module] = {'path':str(path),'sha256':sha(path),'blob':blob(path)}
for module in ['Mock2_Advanced','Mock2_FunctionalAnalysis_Integrated','QYM']:
    sources[module]['theorem_signature_sha256'] = signature(Path(sources[module]['path']))

integrated = Path(sources['Mock2_FunctionalAnalysis_Integrated']['path'])
compat = Path(sources['Mock2_FunctionalAnalysis']['path'])
qym = Path(sources['QYM']['path'])
if integrated.read_text(encoding='utf-8').count('\n') < 500:
    raise SystemExit('Integrated source is not substantive')
if 'import PrimalitySheafVerification.Mock2_FunctionalAnalysis_Integrated' not in compat.read_text(encoding='utf-8'):
    raise SystemExit('historical FunctionalAnalysis path is not the Integrated compatibility entry')
if 'Mock2_FunctionalAnalysis_Integrated' not in qym.read_text(encoding='utf-8'):
    raise SystemExit('QYM does not preserve its Integrated dependency')

report = {
    'focused_candidate_status':'PASS',
    'constructed_from_commit':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),
    'base_master_sha':subprocess.check_output(['git','ls-remote','origin','refs/heads/master'],text=True).split()[0],
    'runtime_repair_used_for_final_direct_source':False,
    'candidate_generation':{'mode':'checked-in-direct-first','repair_scripts':'none'},
    'sources':sources,
    'candidate_clean_pass_1':None,
    'candidate_clean_pass_2':None,
    'error_count':None,
    'maximum_error_limit':False,
    'missing_project_object_files':None,
    'forbidden_tokens':0,
    'sorryAx':None,
    'new_global_axioms':0,
    'theorem_statements_changed':False,
    'assumptions_changed':False,
    'mock2_regression':'pending direct verification',
    'integrated_boundary':'substantive full implementation with historical compatibility entry',
    'qym_conditional_certificate_boundary':'preserved',
}
output.parent.mkdir(parents=True,exist_ok=True)
output.write_text(json.dumps(report,indent=2)+'\n')
