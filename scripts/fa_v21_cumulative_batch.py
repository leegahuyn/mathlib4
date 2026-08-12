#!/usr/bin/env python3
from pathlib import Path
import hashlib, json, os, re, subprocess, sys, tempfile

if len(sys.argv) != 3:
    raise SystemExit("usage: fa_v21_cumulative_batch.py <source> <outdir>")
source = Path(sys.argv[1])
out = Path(sys.argv[2])
out.mkdir(parents=True, exist_ok=True)
expected = os.environ.get("BASE_SOURCE_SHA256", "")
before = source.read_bytes()
base_sha = hashlib.sha256(before).hexdigest()
if expected:
    assert base_sha == expected, (base_sha, expected)
before_text = before.decode()

PATCH = r"""diff --git a/PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean b/PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean
--- a/PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean
+++ b/PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean
@@ -46264,6 +46264,7 @@
 open scoped ENNReal NNReal
 open DefinitionOneSobolev.FixedPhasePeterssonCoordinates
 open DefinitionOneSobolev.FixedPhaseGraphCompletion
+open DefinitionOneSobolev.WeightCorePetersson
 open ExplicitDiscriminantPotential
 open ExplicitDiscriminantPotential.FixedPhaseGraphPotential
 open GammaTwoQuotientGeometry
@@ -48586,7 +48587,15 @@
           (Mock2FA.PaperCorrections.AutomorphicSobolev.HalfWeightDifferentialOperators.InverseEtaFixedPhaseCore.toSmoothCompactWeightCore n v)
           (Mock2FA.PaperCorrections.AutomorphicSobolev.HalfWeightDifferentialOperators.InverseEtaFixedPhaseCore.toSmoothCompactWeightCore n u) q := by
   induction q using Quotient.inductionOn'
-  simp only [quotientInnerDensity_mk, potential_mk]
+  change
+    upstairsInnerDensity (OrbitMultiplier n)
+        (Mock2FA.PaperCorrections.AutomorphicSobolev.HalfWeightDifferentialOperators.InverseEtaFixedPhaseCore.toSmoothCompactWeightCore n v)
+        (Mock2FA.PaperCorrections.AutomorphicSobolev.HalfWeightDifferentialOperators.InverseEtaFixedPhaseCore.toSmoothCompactWeightCore n
+          (potentialMultiplicationCore n u)) _ =
+      (upstairsPotential _ : ℂ) *
+        upstairsInnerDensity (OrbitMultiplier n)
+          (Mock2FA.PaperCorrections.AutomorphicSobolev.HalfWeightDifferentialOperators.InverseEtaFixedPhaseCore.toSmoothCompactWeightCore n v)
+          (Mock2FA.PaperCorrections.AutomorphicSobolev.HalfWeightDifferentialOperators.InverseEtaFixedPhaseCore.toSmoothCompactWeightCore n u) _
   unfold upstairsInnerDensity InvariantFiberMetric.pointwiseInnerDensity
   simp only [Mock2FA.PaperCorrections.AutomorphicSobolev.HalfWeightDifferentialOperators.InverseEtaFixedPhaseCore.toSmoothCompactWeightCore_apply,
     potentialMultiplicationCore_apply]
@@ -48616,21 +48625,25 @@
 `<v,u> + <Rv,Ru> + <Lv,Lu>` on the smooth core. -/
 noncomputable def strongPrincipalCore (n : ℤ) :
     Mock2FA.PaperCorrections.AutomorphicSobolev.HalfWeightDifferentialOperators.InverseEtaFixedPhaseCore n →ₗ[ℂ] Mock2FA.PaperCorrections.AutomorphicSobolev.HalfWeightDifferentialOperators.InverseEtaFixedPhaseCore n :=
-  (LinearMap.id : Mock2FA.PaperCorrections.AutomorphicSobolev.HalfWeightDifferentialOperators.InverseEtaFixedPhaseCore n →ₗ[ℂ]
-      Mock2FA.PaperCorrections.AutomorphicSobolev.HalfWeightDifferentialOperators.InverseEtaFixedPhaseCore n) -
-    (Mock2FA.PaperCorrections.AutomorphicSobolev.HalfWeightDifferentialOperators.InverseEtaFixedPhaseCore.lowerFromSucc n).comp
-      (Mock2FA.PaperCorrections.AutomorphicSobolev.HalfWeightDifferentialOperators.InverseEtaFixedPhaseCore.raise n) -
-    (Mock2FA.PaperCorrections.AutomorphicSobolev.HalfWeightDifferentialOperators.InverseEtaFixedPhaseCore.raiseFromPred n).comp
-      (Mock2FA.PaperCorrections.AutomorphicSobolev.HalfWeightDifferentialOperators.InverseEtaFixedPhaseCore.lower n)
+  Sub.sub
+    (Sub.sub
+      (LinearMap.id : Mock2FA.PaperCorrections.AutomorphicSobolev.HalfWeightDifferentialOperators.InverseEtaFixedPhaseCore n →ₗ[ℂ]
+        Mock2FA.PaperCorrections.AutomorphicSobolev.HalfWeightDifferentialOperators.InverseEtaFixedPhaseCore n)
+      ((Mock2FA.PaperCorrections.AutomorphicSobolev.HalfWeightDifferentialOperators.InverseEtaFixedPhaseCore.lowerFromSucc n).comp
+        (Mock2FA.PaperCorrections.AutomorphicSobolev.HalfWeightDifferentialOperators.InverseEtaFixedPhaseCore.raise n)))
+    ((Mock2FA.PaperCorrections.AutomorphicSobolev.HalfWeightDifferentialOperators.InverseEtaFixedPhaseCore.raiseFromPred n).comp
+      (Mock2FA.PaperCorrections.AutomorphicSobolev.HalfWeightDifferentialOperators.InverseEtaFixedPhaseCore.lower n))
 
 @[simp]
 theorem strongPrincipalCore_apply (n : ℤ)
     (u : Mock2FA.PaperCorrections.AutomorphicSobolev.HalfWeightDifferentialOperators.InverseEtaFixedPhaseCore n) :
     strongPrincipalCore n u =
-      u - Mock2FA.PaperCorrections.AutomorphicSobolev.HalfWeightDifferentialOperators.InverseEtaFixedPhaseCore.lowerFromSucc n
-          (Mock2FA.PaperCorrections.AutomorphicSobolev.HalfWeightDifferentialOperators.InverseEtaFixedPhaseCore.raise n u) -
-        Mock2FA.PaperCorrections.AutomorphicSobolev.HalfWeightDifferentialOperators.InverseEtaFixedPhaseCore.raiseFromPred n
-          (Mock2FA.PaperCorrections.AutomorphicSobolev.HalfWeightDifferentialOperators.InverseEtaFixedPhaseCore.lower n u) :=
+      Sub.sub
+        (Sub.sub u
+          (Mock2FA.PaperCorrections.AutomorphicSobolev.HalfWeightDifferentialOperators.InverseEtaFixedPhaseCore.lowerFromSucc n
+            (Mock2FA.PaperCorrections.AutomorphicSobolev.HalfWeightDifferentialOperators.InverseEtaFixedPhaseCore.raise n u)))
+        (Mock2FA.PaperCorrections.AutomorphicSobolev.HalfWeightDifferentialOperators.InverseEtaFixedPhaseCore.raiseFromPred n
+          (Mock2FA.PaperCorrections.AutomorphicSobolev.HalfWeightDifferentialOperators.InverseEtaFixedPhaseCore.lower n u)) :=
   rfl
 
 /-- Both exact factorization identities combine to the full (not averaged)
@@ -48666,15 +48679,15 @@
 /-- The literal strong SchrodingerCore on the actual smooth core. -/
 noncomputable def strongSchrodingerCore (n : ℤ) (t : ℝ) :
     Mock2FA.PaperCorrections.AutomorphicSobolev.HalfWeightDifferentialOperators.InverseEtaFixedPhaseCore n →ₗ[ℂ] Mock2FA.PaperCorrections.AutomorphicSobolev.HalfWeightDifferentialOperators.InverseEtaFixedPhaseCore n :=
-  strongPrincipalCore n -
-    (t : ℂ) • potentialMultiplicationCore n
+  Sub.sub (strongPrincipalCore n)
+    ((t : ℂ) • potentialMultiplicationCore n)
 
 @[sjV���ڱ����pj�Z�ǝ���