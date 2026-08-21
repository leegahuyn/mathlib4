        # Lean Formalization FINAL AUTHORITY Record

        This record permanently identifies the exact-source Lean **FINAL AUTHORITY**. It is a preservation and verification record, not a new mathematical source revision.

        ## Canonical authority

        - Repository: `leegahuyn/mathlib4`
        - Canonical annotated tag: `formalization-final-2026-08-21`
        - Exact tested commit: `61a48f07e42bc5bf1610a8df3e7cf5ec7e1461c3`
        - Authority branch: `gpt/final-authority-last-mile-20260821`
        - PR: `#56` — not merged and not required to be merged
        - Actual Lean run: `32438949135`
        - Actual Lean job: `96645636205`
        - Original evidence artifact: `9434085968` / `final-authority-last-mile-32438949135-attempt1`
        - Original evidence ZIP SHA256: `86b2525c7533562b929a573eca0ff006c6b1df1ac054329c906eae009e05954a`
        - Source snapshot: `formalization-final-source-61a48f07.tar.gz`
        - Source snapshot SHA256: `54d6a4fb274ef3bec7853dbbc1f3085d6d8b381a59b8d1102d9b75533ff3c10e`

        ## Toolchain

        - `lean-toolchain`: `leanprover/lean4:v4.33.0-rc1`
        - Lean: `Lean 4.33.0-rc1`
        - Lean commit: `62eed1db4d67327ec8120be05f1a1b0847d74561`
        - Lake: `5.0.0-src+62eed1d`
        - `lake-manifest.json` SHA256: `672474eb93bc14c66cd1ff45203c451987fe525f7b5d13ecd83140be46434b26`

        ## Terminal verification

        | Gate | Result |
        |---|---|
        | QYM golden lock | PASS |
        | QYM independent replay | PASS |
        | Mock3 canonical | PASS |
        | Final13 | 13/13 PASS; FAIL 0; SKIPPED 0; NOT_RUN 0 |
        | Bridges | 2/2 PASS; FAIL 0; SKIPPED 0; NOT_RUN 0 |
        | BuildAll | PASS; exit 0; errors 0; panic 0; sorry warnings 0 |
        | Clean build #1 | PASS |
        | Clean build #2 | PASS |
        | Checklist | 15/15 PASS; FAIL 0; SKIPPED 0; NOT_RUN 0 |
        | Forbidden | 0 |
        | Panic | 0 |
        | Axiom/trust audit | PASS |
        | Source identity audit | PASS |
        | Final Lean error | NONE |
        | Final blocker | NONE |
        | FINAL AUTHORITY | PASS |

        Ordinary Lean warnings are preserved and countable. They are not represented as compiler errors. No `sorry`, `admit`, project axiom, `native_decide`, or forbidden proof escape is accepted under the final policy.

        ## Primary root fingerprints

        | Path | Lines | Bytes | SHA256 | Git blob |
|---|---:|---:|---|---|
| `PrimalitySheafVerification/Spt1.lean` | 8087 | 365921 | `6edd211fba5824a092c22e38ed748a7e59eb313860995f94623df43ce1e06535` | `c69b42e0dc4671ace05fe595d29669558b0d4372` |
| `PrimalitySheafVerification/Spt2.lean` | 8878 | 403732 | `292f8f64858888aa73b24e895b6b0b9af2a0f53a51a9f5d1aded452024d77cb7` | `ee1df370ee56549aebd9db0a0aaa0582ae227a5f` |
| `PrimalitySheafVerification/Spt3.lean` | 7506 | 430152 | `da2c9dfc5787d6121b42df4d1729552c28914f9e54edf30d27d7aba3cd2b347b` | `a73d346d060a9a2b8b3dca636e0e611eb394f69c` |
| `PrimalitySheafVerification/Spt4.lean` | 8714 | 465620 | `be2a7647d95ab6bb32ee2801269d45c9b57a8e2a7e08ad764618651ad09d6dc5` | `dfdbece780686cd0a490ea5ef27a2396728efea2` |
| `PrimalitySheafVerification/Spt5.lean` | 8071 | 473184 | `6279d935410d4dab3b5af8a95ef503ccb5a66da1ecfc668aa03e773a837b9203` | `14ef77d87aaca5db11ca329731e052d000b4bdf5` |
| `PrimalitySheafVerification/Spt6.lean` | 8651 | 435585 | `e8c038b4e1e932914ac4394a036a602c19e1bcb6ac3acedbe518eebf9b95a4fe` | `e4832c95c1dddfc7febec5c6b2891b0149a6c7f9` |
| `PrimalitySheafVerification/Spt7.lean` | 18114 | 865526 | `a05f56f4fbda508f919e9fe8259a91af464afca35758346d2326f75211a366bd` | `1de97d018a37190df3a22824d2ad1d6cf3916955` |
| `PrimalitySheafVerification/Mock1.lean` | 9831 | 425518 | `1bcb9a5c18e0dd5ba115541ba806090daf7800ff0324a3db9e1da4d4eb32c1bd` | `424fa454ee5f73b75a15e49e2eac931f3b4cd269` |
| `PrimalitySheafVerification/Mock1_Advanced.lean` | 90615 | 4428854 | `b14bcea1991b4f9b6fcde207b9d25b31cceb54f7601715fd6b6e2d988ecbfe53` | `3b6596bbc0790c7d6e427c44e2b0b18b8af3efa6` |
| `PrimalitySheafVerification/Mock2.lean` | 26607 | 1119419 | `36a034721c389888b2c235d856753e5f2e38f9f6a258fddabbb70fe751ae3594` | `94f8894b5f866701955a105044b8958a8deb7734` |
| `PrimalitySheafVerification/Mock2_Advanced.lean` | 31919 | 1390059 | `cf44063abca1d5b47331a9001a3cff45a86b5e889865812fe4e7826c6af41526` | `a60fa47ebcd8c1fb6037d705e81b54c80910657a` |
| `PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean` | 63138 | 2821792 | `c680a35b9f12ea3223d8328ed0f5f0674b3439e650bb62cb900b54917f9653bd` | `28f614d48e02a0f28d3f5a758e813350b3ea89cf` |
| `PrimalitySheafVerification/QYM.lean` | 62604 | 2958818 | `ab7c394f68b812046bcfae109b274a2d4fa42479bf8e76461c73a9c190fb3204` | `7afb309d7c4da97da7bc6b922931734d72830d41` |

        ## Mandatory bridge fingerprints

        | Path | Lines | Bytes | SHA256 | Git blob |
|---|---:|---:|---|---|
| `PrimalitySheafVerification/Mock2_FunctionalAnalysis_Integrated.lean` | 13 | 575 | `a77f9e67980ec35b0d7b4d1624c10ec68051f575468d3b74859e6cf30e3e0439` | `464f5dd095876b20165d12690c8127ef9d909e6a` |
| `PrimalitySheafVerification/Mock3.lean` | 12 | 438 | `f828c0c29a3293f40206244e82dde92b5a54d8e9c01a879edd11449cd0eb0a8c` | `bf2a83664292e58f845c457a82de668b0e65be05` |

        ## BuildAll fingerprint

        | Path | Lines | Bytes | SHA256 | Git blob |
|---|---:|---:|---|---|
| `PrimalitySheafVerification/BuildAll.lean` | 16 | 774 | `696f8adf76eb014034d5917d0518856b86b922586d324455023754d75107d38a` | `fc6fb147b8505b434104cf1ef50dd9243baa79f9` |

        ## Independent verification

        1. Clone the repository and fetch tags:

           ```bash
           git clone https://github.com/leegahuyn/mathlib4.git
           cd mathlib4
           git fetch --tags
           git checkout formalization-final-2026-08-21
           git rev-parse HEAD
           ```

           The final command must print:

           ```text
           61a48f07e42bc5bf1610a8df3e7cf5ec7e1461c3
           ```

        2. Download the release assets into one directory. Run the cheap cryptographic/source/evidence verifier:

           ```bash
           chmod +x VERIFY_FINAL_AUTHORITY.sh
           ./VERIFY_FINAL_AUTHORITY.sh "$PWD"
           ```

           PowerShell:

           ```powershell
           .\VERIFY_FINAL_AUTHORITY.ps1 -RepoDir $PWD
           ```

        3. Optional full compiler reproduction under the pinned toolchain:

           ```bash
           FULL_LEAN=1 ./VERIFY_FINAL_AUTHORITY.sh "$PWD"
           ```

           This optional mode runs `python3 scripts/final_authority_gate_v5.py`. It is intentionally not the default because the full Lean chain is expensive. The permanent original actual-Lean evidence is the byte-identical Actions ZIP named above.

        ## Scope

        This certification is bound to exact source bytes at `61a48f07e42bc5bf1610a8df3e7cf5ec7e1461c3`. Future modifications are not automatically covered. No merge commit supersedes the canonical authority. The GitHub PR need not be merged for the tag and release to remain valid.
