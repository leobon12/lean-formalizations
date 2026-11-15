/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInRetainRecord
import InteractingSLE.Spec.Sec7.PocketPhaseMeans

/-!
# Original-time references normalized at relative level zero

PROVE-POCKET-SIDEIN. The zero relative prefix is the deterministic seed.
Consequently it adds no information to a record already containing the
candidate event. A retained original-time filled law gives a raw reference
law at this level, without stopping or selecting a later relative visit.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H)
open LQGMetric (DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketStopSide

open PocketCoupling PocketTraversal Lemma71C LocalSets WholeField PocketStop PocketStopField

/-- The zero relative prefix of a driven curve only sees its fixed seed,
so the localized prefix record is exactly the initial record. -/
theorem locPrefixSigma_zero_of_driven {Ω : Type*} {ℋ : MeasurableSpace Ω}
    {A : Set Ω} (hA : MeasurableSet[ℋ] A) {γ : Ω → ℝ → ℂ}
    (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω)) : locPrefixSigma ℋ A γ 0 = ℋ := by
  apply le_antisymm
  · refine sup_le le_rfl (MeasurableSpace.generateFrom_le ?_)
    rintro _ ⟨r, hr, n, k, rfl⟩
    have hr0 : r = 0 := le_antisymm hr zero_le
    subst r
    have hEq : A ∩ PocketAdapt.prefixEvent γ 0 n k =
        {ω | ω ∈ A ∧ (0 : ℂ) ∈ Restart.dyadicSquare n k} := by
      ext ω
      by_cases hω : ω ∈ A
      · simp [PocketAdapt.prefixEvent, hω, (hγ ω hω).capInv_of_nonpos le_rfl,
          (hγ ω hω).zero, PocketPhaseMeans.capLife_pos (hγ ω hω)]
      · simp only [mem_inter_iff, hω, false_and, mem_ofPred_eq]
    rw [hEq]
    by_cases hQ : (0 : ℂ) ∈ Restart.dyadicSquare n k
    · convert hA using 1
      ext ω
      simp only [mem_ofPred_eq, hQ, and_true]
    · simp only [hQ, and_false, ofPred_false]
      exact MeasurableSet.empty
  · exact le_sup_left

/-- At level zero the live normalization is precisely the independently
normalized original-time filling used by the retained comparison laws. -/
theorem liveExt_zero_eq_eventFilled {Ω : Type*} {A : Set Ω} {γ : Ω → ℝ → ℂ}
    (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω)) (C F : Ω → Set ℂ) :
    liveExt A γ C F 0 = eventFilled A C F := by
  funext ω
  by_cases hω : ω ∈ A
  · rw [liveExt_of_live ⟨hω, PocketPhaseMeans.capLife_pos (hγ ω hω)⟩,
      eventFilled, ite_eq_left hω]
  · rw [liveExt_of_not_live (fun h => hω h.1), eventFilled, ite_eq_right hω]

/-- A global retained original-time filled set supplies the precise raw
reference law at zero relative level. Its normalization is on the fixed
candidate event, independently of later collars. -/
theorem raw_reference_law_zero_of_retained {Ω : Type*} {ℋ : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] {P : Measure Ω} (hℋ : ℋ ≤ mΩ)
    {A : Set Ω} (hA : MeasurableSet[ℋ] A) {γ : Ω → ℝ → ℂ}
    (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω)) {C F : Ω → Set ℂ}
    {h : Ω → DistOn upperHalfPlaneOpens}
    (hRecord : Measurable[ℋ, hittingSigma] (eventFilled A C F))
    (hRetained : IsHistoryAvoidanceLocal ℋ (eventFilled A C F) h P) :
    PocketStopUnionLaw ℋ P A γ C F h 0 := by
  refine ⟨eventFilled A C F, hRecord.mono hℋ le_rfl, ?_, ?_⟩
  · rw [locPrefixSigma_zero_of_driven hA hγ]
    exact hRetained
  · intro ω hω _
    simp only [eventFilled, ite_eq_left hω]

end InteractingSLE.Sec7.PocketStopSide
