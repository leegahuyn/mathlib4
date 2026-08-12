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
 /-- The literal strong Schrodinger expression on the actual smooth core. -/
 noncomputable def strongSchrodingerCore (n : ℤ) (t : ℝ) :
     Mock2FA.PaperCorrections.AutomorphicSobolev.HalfWeightDifferentialOperators.InverseEtaFixedPhaseCore n →ₗ[ℂ] Mock2FA.PaperCorrections.AutomorphicSobolev.HalfWeightDifferentialOperators.InverseEtaFixedPhaseCore n :=
-  strongPrincipalCore n -
-    (t : ℂ) • potentialMultiplicationCore n
+  Sub.sub (strongPrincipalCore n)
+    ((t : ℂ) • potentialMultiplicationCore n)
 
 @[simp]
 theorem strongSchrodingerCore_apply (n : ℤ) (t : ℝ)
     (u : Mock2FA.PaperCorrections.AutomorphicSobolev.HalfWeightDifferentialOperators.InverseEtaFixedPhaseCore n) :
     strongSchrodingerCore n t u =
-      strongPrincipalCore n u -
-        (t : ℂ) • potentialMultiplicationCore n u :=
+      Sub.sub (strongPrincipalCore n u)
+        ((t : ℂ) • potentialMultiplicationCore n u) :=
   rfl
 
 /-- The raw differential expression, displayed independently of the bundled
@@ -48835,7 +48848,7 @@
 theorem corePeterssonForcing_zero (n : ℤ) :
     corePeterssonForcing n 0 = 0 := by
   ext v
-  simp only [corePeterssonForcing_apply, map_zero, inner_zero]
+  simp [corePeterssonForcing_apply]
 
 /-- Petersson pairings against the actual smooth fixed-phase core separate
 smooth sections.  The proof tests with the difference itself and then uses
@@ -48846,7 +48859,7 @@
       inner ℂ (l2Coordinate n v) (l2Coordinate n g) =
         inner ℂ (l2Coordinate n v) (l2Coordinate n f)) :
     g = f := by
-  let w : Mock2FA.PaperCorrections.AutomorphicSobolev.HalfWeightDifferentialOperators.InverseEtaFixedPhaseCore n := g - f
+  let w : Mock2FA.PaperCorrections.AutomorphicSobolev.HalfWeightDifferentialOperators.InverseEtaFixedPhaseCore n := Sub.sub g f
   have hwPair := hPair w
  have hSelf :
      inner ℂ (l2Coordinate n w) (l2Coordinate n w) = 0 := by
@@ -48858,7 +48871,7 @@
   have hw : w = 0 := by
     apply l2Coordinate_injective n
    simpa only [map_zero] using hwCoordinate
-  change g - f = 0 at hw
+  change Sub.sub g f = 0 at hw
   exact sub_eq_zero.mp hw
 
 /-- Every literal smooth strong solution gives an equality in the full
@@ -48977,7 +48990,7 @@
   unfold fullPlaneBilinearPair
   apply integral_congr_ae
   filter_upwards [coeFn_fullPlaneTestToL2 v] with x hx
-  simp only [lsmul_apply, hx]
+  simp only [lsmul_apply, hx, smul_eq_mul]
 
 /-- Translation of an `L²` representative can be used inside a compact-test
 pairing as the literal function `x → u (x - t)`. -/
@@ -49116,7 +49129,6 @@
   apply integral_congr_ae
   filter_upwards [coeFn_fullPlaneTestToL2 v,
     DomAddAct.vadd_Lp_ae_eq (DomAddAct.mk (-t)) u] with x hv hut
-  simp only [lsmul_apply] at *
   rw [hv]
   have hut' : (DomAddAct.mk (-t) +₊ u) x = u (x - t) := by
     change (DomAddAct.mk (-t) +₢ u) x = u (-t + x) at hut
@@ -49195,8 +49207,13 @@
     hcompact : HasCompactSupport g) : FullPlaneTest where
   toFun := fun x ↹ (g x : ℂ)
   contDiff' := Complex.ofRealCLM.contDiff.comp hg
-  hasCompactSupport' := hcompact.comp_left s_4��!j�-���jם