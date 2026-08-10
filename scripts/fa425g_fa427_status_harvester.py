#!/usr/bin/env python3
from pathlib import Path

source = Path('scripts/fa425_426_status_harvester.py').read_text(encoding='utf-8')
source = source.replace(
    'OUT = Path("status-records/fa425-fa426")',
    'OUT = Path("status-records/fa425g-fa427")',
)
needle = '''    ("fix/fa426b-multiround-importsafe-20260810", "FA426b import-safe multiround strict controller"),
]'''
replacement = '''    ("fix/fa426b-multiround-importsafe-20260810", "FA426b import-safe multiround strict controller"),
    ("fix/fa425e-isolated-instance-section-20260810", "FA425e isolated canonical-instance section tournament"),
    ("fix/fa425f-instance-transport-20260810", "FA425f AddCommGroup equality-transport tournament"),
    ("fix/fa425g-instance-sandwich-20260810", "FA425g canonical-instance sandwich tournament"),
    ("fix/fa427-parallel-frontier-loop-20260810", "FA427 parallel direct-Lean frontier loop"),
]'''
if source.count(needle) != 1:
    raise SystemExit(f'expected one CONFIGS suffix, found {source.count(needle)}')
source = source.replace(needle, replacement)
exec(compile(source, 'fa425g_fa427_status_harvester.generated.py', 'exec'), {'__name__': '__main__'})
