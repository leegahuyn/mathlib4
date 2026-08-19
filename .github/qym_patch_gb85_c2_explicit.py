#!/usr/bin/env python3
from __future__ import annotations

from time import sleep
from urllib.request import urlopen

PINNED_SOURCE = (
    "https://raw.githubusercontent.com/leegahuyn/mathlib4/"
    "2d325b7eefb0dd184401fdfb5d2bef1cc07556e9/"
    ".github/qym_patch_gb85_c2_explicit.py"
)

source = None
last_error: Exception | None = None
for attempt in range(1, 6):
    try:
        with urlopen(PINNED_SOURCE, timeout=60) as response:
            source = response.read().decode("utf-8")
        break
    except Exception as exc:  # pragma: no cover - exercised only on transient network failures
        last_error = exc
        sleep(attempt * 2)
if source is None:
    raise SystemExit(f"could not recover pinned C2 patcher: {last_error}")

old = (
    "      horizontalHorocycleAmbientCurve] using\n"
    "      (contDiff_horizontalHorocycleAmbientCurve\n"
)
new = (
    "      QYM.FullCertification.PolygonTraceExtension."
    "horizontalHorocycleAmbientCurve] using\n"
    "      (QYM.FullCertification.PolygonTraceExtension."
    "contDiff_horizontalHorocycleAmbientCurve\n"
)
if source.count(old) != 1:
    raise SystemExit(f"expected one namespace repair site, found {source.count(old)}")
source = source.replace(old, new, 1)

namespace = {"__name__": "qym_patch_gb85_c2_explicit_v2"}
exec(compile(source, PINNED_SOURCE, "exec"), namespace)
namespace["main"]()
