/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SfMeanVersions
import InteractingSLE.WangWu.ReverseContactMartFilt2Union
import InteractingSLE.Spec.Sec6.CondMeanStop
import InteractingSLE.Spec.Supplement.WalkStageLocalAE

/-! # Comparing a field-determined stopped union with a larger local set -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter MeasureTheory
open QuantumZipper (H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.GW2Sf

open LocalSets WholeField

variable {Ω : Type u} {ℋA ℋC : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]

/-- A field-determined marked local set and a larger marked local set have
 the same mean on any mark of the smaller set where the sets agree. The
 larger set's marks may contain additional randomness. -/
theorem ae_mean_eq_on_nested_determined
    {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hℋA : ℋA ≤ mΩ) (hℋC : ℋC ≤ mΩ) (hNA : Ito.nullSets P ≤ ℋA)
    (hAd : ℋA ≤ aeSigma (MeasurableSpace.comap h inferInstance) P)
    {A C : Ω → Set ℂ} (hA : Measurable[ℋA, hittingSigma] A)
    (hC : Measurable[ℋC, hittingSigma] C)
    (hAc : ∀ᵐ ω ∂P, A ω ⊆ H ∧ IsOpen (H \ A ω))
    (hCc : ∀ᵐ ω ∂P, C ω ⊆ H ∧ IsOpen (H \ C ω))
    (hlA : IsHistoryAvoidanceLocal ℋA A h P) (hlC : IsHistoryAvoidanceLocal ℋC C h P)
    (hAC : ∀ᵐ ω ∂P, A ω ⊆ C ω)
    {E : Set Ω} (hE : MeasurableSet[ℋA] E)
    (hEq : ∀ᵐ ω ∂P, ω ∈ E → A ω = C ω)
    {gA gC : Ω → DistOn upperHalfPlaneOpens}
    (hgA : IsLocalSetMean A h P gA) (hgC : IsLocalSetMean C h P gC) :
    ∀ᵐ ω ∂P, ω ∈ E → gA ω = gC ω := by
  have hAm := hA.mono hℋA le_rfl
  have hCm := hC.mono hℋC le_rfl
  have hci := Sec6.condIndepEv_of_le_aeSigma hh.measurable.comap_le
    (le_rfl : mΩ ≤ mΩ) hAd
  have hlU : IsHistoryAvoidanceLocal (ℋA ⊔ ℋC) (fun ω => A ω ∪ C ω) h P :=
    WangWu.isHistoryAvoidanceLocal_union hℋA le_rfl le_rfl hℋC hA hCm hci hlA hlC
  have heU : (fun ω => A ω ∪ C ω) =ᵐ[P] C :=
    hAC.mono fun _ hω => union_eq_right.2 hω
  have hlC' : IsHistoryAvoidanceLocal ℋA C h P := by
    have hl := Theorem14.WalkLaw.isHistoryAvoidanceLocal_congr_ae heU hlU
    intro U G hUH hG hd F hF
    exact hl U G hUH hG hd F ((le_sup_left : ℋA ≤ ℋA ⊔ ℋC) F hF)
  exact ae_mean_eq_on_marked_event hh hℋA hNA hAm hCm hAc hCc hlA hlC' hE hEq hgA hgC

end InteractingSLE.Theorem14.GW2Sf
