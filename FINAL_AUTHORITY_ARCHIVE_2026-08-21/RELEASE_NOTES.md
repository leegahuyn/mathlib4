# Formalization FINAL AUTHORITY — 2026-08-21

This release permanently records the exact-source Lean FINAL AUTHORITY.

Repository: `leegahuyn/mathlib4`

Canonical tag: `formalization-final-2026-08-21`

Exact tested commit: `61a48f07e42bc5bf1610a8df3e7cf5ec7e1461c3`

Authority branch: `gpt/final-authority-last-mile-20260821`

PR: `#56`

Actual Lean run: `32438949135`

Actual Lean job: `96645636205`

Evidence artifact: `9434085968`

Original evidence ZIP SHA256: `86b2525c7533562b929a573eca0ff006c6b1df1ac054329c906eae009e05954a`

Source snapshot SHA256: `54d6a4fb274ef3bec7853dbbc1f3085d6d8b381a59b8d1102d9b75533ff3c10e`

Toolchain: `leanprover/lean4:v4.33.0-rc1`

Lean commit: `62eed1db4d67327ec8120be05f1a1b0847d74561`

Lake: `5.0.0-src+62eed1d`

`lake-manifest.json` SHA256: `672474eb93bc14c66cd1ff45203c451987fe525f7b5d13ecd83140be46434b26`

## Terminal verification

```text
Final13            13/13 PASS
Bridges              2/2 PASS
BuildAll            PASS
Clean build #1      PASS
Clean build #2      PASS
Checklist           15/15 PASS
Forbidden           0
Panic               0
Axiom audit         PASS
Source identity     PASS
Final Lean error    NONE
Final blocker       NONE

FINAL AUTHORITY     PASS
```

Ordinary Lean warnings are preserved/countable and are not being represented as compiler errors.

No `sorry`/`admit`/project axiom/`native_decide`/forbidden proof escape is accepted under the final policy.

This release is bound to exact source bytes. Future modifications are **not** automatically covered by this certification. The GitHub PR need not be merged for this release to remain valid.

## Third-party verification

```bash
git clone https://github.com/leegahuyn/mathlib4.git
cd mathlib4
git fetch --tags
git checkout formalization-final-2026-08-21
test "$(git rev-parse HEAD)" = "61a48f07e42bc5bf1610a8df3e7cf5ec7e1461c3"
```

Download the release assets into one directory, then run:

```bash
./VERIFY_FINAL_AUTHORITY.sh "$PWD"
```

PowerShell:

```powershell
.\VERIFY_FINAL_AUTHORITY.ps1 -RepoDir $PWD
```

These commands perform cheap cryptographic/source/evidence validation. Optional full Lean reproduction is documented in `FINAL_AUTHORITY_RECORD.md` and can be requested with `FULL_LEAN=1`.
