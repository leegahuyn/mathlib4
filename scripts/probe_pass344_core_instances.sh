#!/usr/bin/env bash
set -euo pipefail

FA='PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean'
OUT='/tmp/probe-pass344-core-instances'
OLEAN='.lake/build/lib/lean/PrimalitySheafVerification'
mkdir -p "${OUT}/logs" "${OLEAN}"

# Reconstruct the exact PASS 344 candidate.  Its expected frontier failure is
# ignored; the resulting working-tree source and hash are the probe input.
set +e
bash scripts/diagnose_pass344_frontier_v2.sh \
  > "${OUT}/logs/reconstruct-pass344.log" 2>&1
reconstruct_rc=$?
set -e
sha256sum "${FA}" | tee "${OUT}/candidate-sha256.txt"
test "$(sha256sum "${FA}" | awk '{print $1}')" = \
  '59d4bcc02ff615190da0691c9bef52fe3d8bfcb0b8cdf573c300e258757376b6'
echo "reconstruct_exit=${reconstruct_rc}" > "${OUT}/provenance.txt"

python3 - <<'PY'
from pathlib import Path

source = Path('PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean').read_text(encoding='utf-8')
out = Path('/tmp/probe-pass344-core-instances')

alias_marker = '''noncomputable abbrev InverseEtaFixedPhaseCore (n : ℤ) : Type :=
  ↥(inverseEtaFixedPhaseStableCoreSubmodule n)
'''
local_marker = '''  zero_smul x := by
    apply Subtype.ext
    simp
'''


def write(name: str, marker: str, probe: str) -> None:
    count = source.count(marker)
    print(f'{name}: marker_count={count}')
    if count != 1:
        raise SystemExit(f'{name}: expected unique marker, found {count}')
    text = source.replace(marker, marker + '\n' + probe + '\n', 1)
    (out / f'{name}.lean').write_text(text, encoding='utf-8')

write(
    'canonical-module', alias_marker,
    '''set_option trace.Meta.synthInstance true in
#synth Module ℂ (InverseEtaFixedPhaseCore 0)''',
)
write(
    'canonical-addgroup', alias_marker,
    '''set_option trace.Meta.synthInstance true in
#synth AddCommGroup (InverseEtaFixedPhaseCore 0)''',
)
write(
    'after-local-module', local_marker,
    '''set_option trace.Meta.synthInstance true in
#synth Module ℂ (InverseEtaFixedPhaseCore 0)
#check @fixedPhaseGraphCoreModule''',
)
write(
    'explicit-local-module', local_marker,
    '''example (n : ℤ) : Module ℂ (InverseEtaFixedPhaseCore n) :=
  fixedPhaseGraphCoreModule n''',
)
write(
    'canonical-reexpose', alias_marker,
    '''noncomputable local instance probeCoreAddCommGroup (n : ℤ) :
    AddCommGroup (InverseEtaFixedPhaseCore n) := by
  change AddCommGroup ↥(inverseEtaFixedPhaseStableCoreSubmodule n)
  infer_instance

noncomputable local instance probeCoreModule (n : ℤ) :
    Module ℂ (InverseEtaFixedPhaseCore n) := by
  change Module ℂ ↥(inverseEtaFixedPhaseStableCoreSubmodule n)
  infer_instance

#synth AddCommGroup (InverseEtaFixedPhaseCore 0)
#synth Module ℂ (InverseEtaFixedPhaseCore 0)''',
)
PY

printf 'probe,exit_code,first_error\n' > "${OUT}/summary.csv"
for probe in \
  canonical-module \
  canonical-addgroup \
  after-local-module \
  explicit-local-module \
  canonical-reexpose; do
  log="${OUT}/logs/${probe}.log"
  rm -f "${OLEAN}/Mock2_FunctionalAnalysis.olean" \
    "${OLEAN}/Mock2_FunctionalAnalysis.ilean" \
    "${OLEAN}/Mock2_FunctionalAnalysis.olean.private"
  set +e
  lake env lean -DmaxErrors=1 "${OUT}/${probe}.lean" \
    -o "${OLEAN}/Mock2_FunctionalAnalysis.olean" \
    -i "${OLEAN}/Mock2_FunctionalAnalysis.ilean" \
    > "${log}" 2>&1
  rc=$?
  set -e
  first="$(grep -m1 -E ':[0-9]+:[0-9]+: error' "${log}" | tr ',' ';' || true)"
  printf '%s,%s,%s\n' "${probe}" "${rc}" "${first}" >> "${OUT}/summary.csv"
done

cat "${OUT}/summary.csv"
# Probes are diagnostic; always upload their evidence.
exit 0
