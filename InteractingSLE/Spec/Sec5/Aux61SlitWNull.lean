/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61SlitWCompare
import InteractingSLE.Spec.Sec5.Aux61MarksNull
import InteractingSLE.Spec.Sec5.Aux61MarksAsm

/-! # Comparison unions for null-completed physical marks -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open QuantumZipper (H)
open LQGMetric (DistOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61SlitW
open Aux61ULoc Aux61ChLoc Aux61Marks Aux61Asm LocalSets WholeField
universe u

/-- The comparison union uses the current live event and the null-completed
raised-rule marks. Its retained germ is exactly the physical initial germ. -/
def nullComparisonWiringData {X : Type u} [MeasurableSpace X] {μ : Measure X}
    (D : MarksData μ) (hF : MarksFacts μ D) {Y R : Type*} [MeasurableSpace Y] [MeasurableSpace R]
    (stop : ℝ≥0 → R → R) (rule : D.ι → ℝ≥0 → Y × R → ℝ≥0∞)
    (Y₀ : X → Y) (R₀ : X → R) (q : D.index → ℝ≥0)
    (g : D.index → X → DistOn upperHalfPlaneOpens) : SlitWiringData (D.toAsmData hF) where
  patchMean := fun j _ _ => g j
  union := fun j i t => liveSet (liveEv (D.Z i) (D.B i) (D.code i) t)
    (fun x => D.liveSets i t x ∪ D.patches j i t x)
  unionMarks := fun j i t =>
    nullMarks (ruleMarks stop (fun p => max (rule i t p) (q j : ℝ≥0∞)) Y₀ R₀) μ ⊔ D.germ0 i

section Local
variable {X : Type*} {ℳ : MeasurableSpace X} [mX : MeasurableSpace X]
  {μ : Measure X} [IsProbabilityMeasure μ] {h : X → DistOn upperHalfPlaneOpens}
  {A₀ A L R : X → Set ℂ} {S : Set X}

/-- Enlarge the physical union, pass to its current live version, and retain
the initial germ. The initial set is already a live version. -/
theorem isHistoryAvoidanceLocal_null_comparison
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h μ) (hℳ : ℳ ≤ mX)
    (hS : MeasurableSet[ℳ] S) (hA₀ : Measurable[ℳ, hittingSigma] A₀)
    (hA₀H : ∀ x, A₀ x ⊆ H) (hA : Measurable[ℳ, hittingSigma] A)
    (hL : Measurable[ℳ, hittingSigma] L) (hnest : ∀ x, A₀ x ⊆ A x)
    (hraw : IsHistoryAvoidanceLocal ℳ R h μ)
    (hsub : ∀ᵐ x ∂μ, R x ⊆ A x ∪ L x) :
    IsHistoryAvoidanceLocal (ℳ ⊔ germSigma A₀ h) (liveSet S (fun x => A x ∪ L x)) h μ := by
  have hU := @measurable_union_hitting X ℳ A L hA hL
  have hloc := Sec7.Lemma72C.isHistoryAvoidanceLocal_mono_set hraw hU hsub
  apply Sec7.Lemma725RefMarks.isHistoryAvoidanceLocal_sup_germSigma hh hℳ
    ((Aux61Nest.measurable_liveSet hS hU).mono hℳ le_rfl)
    (isHistoryAvoidanceLocal_liveSet hloc hS) hA₀
  intro x z hz
  by_cases hx : x ∈ S
  · rw [liveSet_of_mem hx]
    exact Or.inl (hnest x hz.1)
  · rw [liveSet_of_notMem hx]
    exact hA₀H x hz.1

end Local
end InteractingSLE.Sec5.Aux61SlitW
