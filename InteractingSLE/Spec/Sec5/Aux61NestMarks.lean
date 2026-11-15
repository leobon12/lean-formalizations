/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61ChLocRestart
import InteractingSLE.Spec.Sec7.Lemma725RefMarksGerm

/-!
# Retaining the initial germ in the later chart marks

Packet PROVE-AUX61-NEST. Germ sigma algebras themselves need not be monotone
under inclusion of local sets. Instead, retain the initial germ as an
additional mark, using `Lemma725RefMarks.isHistoryAvoidanceLocal_sup_germSigma`.
The live versions are essential: outside the later live event the larger set
is all of the upper half-plane.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open QuantumZipper (H)
open LQGMetric (DistOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61Nest

open Aux61ChLoc (liveSet liveSet_of_mem liveSet_of_notMem)
open LocalSets (germSigma)
open WholeField (IsHistoryAvoidanceLocal)

variable {X : Type*}

/-- Taking the live version twice on the same event does not change it. -/
theorem liveSet_idem (S : Set X) (A : X → Set ℂ) :
    liveSet S (liveSet S A) = liveSet S A := by
  funext x
  by_cases hx : x ∈ S
  · rw [liveSet_of_mem hx]
  · simp only [liveSet_of_notMem hx]

/-- Later live sets contain earlier live sets when their events shrink and
their underlying sets grow. -/
theorem liveSet_subset {S₀ S : Set X} (hS : S ⊆ S₀) {A₀ A : X → Set ℂ}
    (hA₀ : ∀ x, A₀ x ⊆ H) (hA : ∀ x, A₀ x ⊆ A x) (x : X) :
    liveSet S₀ A₀ x ⊆ liveSet S A x := by
  by_cases hx : x ∈ S
  · rw [liveSet_of_mem hx, liveSet_of_mem (hS hx)]
    exact hA x
  · rw [liveSet_of_notMem hx]
    by_cases hx₀ : x ∈ S₀
    · rw [liveSet_of_mem hx₀]
      exact hA₀ x
    · rw [liveSet_of_notMem hx₀]

/-- The live version is measurable for any marks recording the event and set. -/
theorem measurable_liveSet {ℋ : MeasurableSpace X} {S : Set X}
    (hS : MeasurableSet[ℋ] S) {A : X → Set ℂ}
    (hA : Measurable[ℋ, hittingSigma] A) :
    Measurable[ℋ, hittingSigma] (liveSet S A) := by
  classical
  exact Measurable.piecewise hS hA measurable_const

/-- Relative closedness is preserved by the live version. -/
theorem liveSet_properties {S : Set X} {A : X → Set ℂ}
    (hA : ∀ x, A x ⊆ H ∧ IsOpen (H \ A x)) (x : X) :
    liveSet S A x ⊆ H ∧ IsOpen (H \ liveSet S A x) := by
  by_cases hx : x ∈ S
  · rw [liveSet_of_mem hx]
    exact hA x
  · rw [liveSet_of_notMem hx, sdiff_self]
    exact ⟨subset_rfl, isOpen_empty⟩

/-- The desired conditioning-algebra nesting is an order consequence of
retaining the initial germ among the later marks. -/
theorem germ_sup_le_sup_germ {ℋ₀ ℋ : MeasurableSpace X} (hℋ : ℋ₀ ≤ ℋ)
    (A₀ A : X → Set ℂ) (h : X → DistOn upperHalfPlaneOpens) :
    germSigma A₀ h ⊔ ℋ₀ ≤ germSigma A h ⊔ (ℋ ⊔ germSigma A₀ h) :=
  sup_le (le_sup_right.trans le_sup_right) (hℋ.trans (le_sup_left.trans le_sup_right))

/-- The later live set stays marked local after the initial live germ is
retained. This uses marked locality, rather than a false germ-monotonicity rule. -/
theorem isHistoryAvoidanceLocal_liveSet_sup_germ
    {ℋ : MeasurableSpace X} [mX : MeasurableSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ] {h : X → DistOn upperHalfPlaneOpens}
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h μ) (hℋ : ℋ ≤ mX)
    {S₀ S : Set X} (hS : MeasurableSet[ℋ] S) (hS₀ : MeasurableSet[ℋ] S₀)
    (hSS : S ⊆ S₀) {A₀ A : X → Set ℂ}
    (hA₀ : Measurable[ℋ, hittingSigma] A₀) (hA₀H : ∀ x, A₀ x ⊆ H)
    (hAm : Measurable[mX, hittingSigma] A)
    (hAA : ∀ x, A₀ x ⊆ A x) (hloc : IsHistoryAvoidanceLocal ℋ A h μ) :
    IsHistoryAvoidanceLocal (ℋ ⊔ germSigma (liveSet S₀ A₀) h) (liveSet S A) h μ := by
  exact Sec7.Lemma725RefMarks.isHistoryAvoidanceLocal_sup_germSigma hh hℋ
    (measurable_liveSet (hℋ _ hS) hAm) (Aux61ChLoc.isHistoryAvoidanceLocal_liveSet hloc hS)
    (measurable_liveSet hS₀ hA₀)
    (fun x => inter_subset_left.trans (liveSet_subset hSS hA₀H hAA x))

end InteractingSLE.Sec5.Aux61Nest
