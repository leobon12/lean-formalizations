/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2DrvLateCmp

/-!
# GW2's open lines: means of two marked local sets agreeing on an event, the bigger one `ℍ` off it

Packet PROVE-GW2-STAGEMEAN, R121 round (the transfer of the Claim(k) step). `SB.Lv.Cmp.ae_mean_eq_on_event_of_det`
compares the local-set means of two field-determined marked local sets `U`, `B` on a mark event `E` of `B` on which
they agree, when the marks of `U` lie in those of `B`. Here the marks are unrelated, but `B` is the whole half-plane
off `E` (as the corrected stage unions are off the history's success):

* **`ae_mean_eq_on_event_of_det_H`**: the two local-set means agree almost surely on `E`.

Proof: `U` is marked local for its marks and `E` (`isHistoryAvoidanceLocal_sup_generateFrom`); `B` is then marked
local for the same marks, since off `E` it avoids no nonempty open set and on `E` its avoidance events are those of
`U`; then `GW2Sf.ae_mean_eq_on_marked_event`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set TopologicalSpace
open QuantumZipper (H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.GW2Psm

open LocalSets WalkLaw

variable {Ω : Type u} {ℋ₀ ℋ₁ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens}

/-- **Means of two field-determined marked local sets agree on an event on which they agree, the second set being
the whole half-plane off the event.** -/
theorem ae_mean_eq_on_event_of_det_H (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hℋ₁ : ℋ₁ ≤ mΩ) {U B : Ω → Set ℂ} (hUm : Measurable[mΩ, hittingSigma] U)
    (hBm : Measurable[mΩ, hittingSigma] B) (hUc : ∀ᵐ ω ∂P, U ω ⊆ H ∧ IsOpen (H \ U ω))
    (hBc : ∀ᵐ ω ∂P, B ω ⊆ H ∧ IsOpen (H \ B ω))
    (hU : ∀ V : Opens ℂ, (V : Set ℂ) ⊆ H → MeasurableSet[ℋ₀] {ω | Disjoint (U ω) V})
    (hdet₀ : ℋ₀ ≤ aeSigma (MeasurableSpace.comap h inferInstance) P)
    (hlocU : WholeField.IsHistoryAvoidanceLocal ℋ₀ U h P)
    (hB : ∀ V : Opens ℂ, (V : Set ℂ) ⊆ H → MeasurableSet[ℋ₁] {ω | Disjoint (B ω) V})
    (hdet₁ : ℋ₁ ≤ aeSigma (MeasurableSpace.comap h inferInstance) P)
    (hlocB : WholeField.IsHistoryAvoidanceLocal ℋ₁ B h P) {E : Set Ω} (hE : MeasurableSet[ℋ₁] E)
    (hUB : ∀ᵐ ω ∂P, ω ∈ E → U ω = B ω) (hBH : ∀ ω, ω ∉ E → B ω = H)
    {gU gB : Ω → DistOn upperHalfPlaneOpens} (hgU : IsLocalSetMean U h P gU) (hgB : IsLocalSetMean B h P gB) :
    ∀ᵐ ω ∂P, ω ∈ E → gU ω = gB ω := by
  have hhm := hh.measurable
  have hlocU' := SB.Lv.Cmp.isHistoryAvoidanceLocal_sup_generateFrom hhm hU hdet₀ hlocU hB hdet₁ hlocB hE hUB
  have hEg : MeasurableSet[ℋ₀ ⊔ MeasurableSpace.generateFrom {E}] E :=
    le_sup_right (a := ℋ₀) _ (MeasurableSpace.measurableSet_generateFrom rfl)
  have hdetE : ℋ₀ ⊔ MeasurableSpace.generateFrom {E} ≤ aeSigma (MeasurableSpace.comap h inferInstance) P :=
    sup_le hdet₀ (MeasurableSpace.generateFrom_le (by rintro _ rfl; exact hdet₁ _ hE))
  have hlocB' : WholeField.IsHistoryAvoidanceLocal (ℋ₀ ⊔ MeasurableSpace.generateFrom {E}) B h P := by
    refine isHistoryAvoidanceLocal_of_mem_aeSigma hhm fun V G hVH hG hd F hF => ?_
    have hUV : MeasurableSet[ℋ₀ ⊔ MeasurableSpace.generateFrom {E}] {ω | Disjoint (U ω) V} :=
      le_sup_left (a := ℋ₀) _ (hU V hVH)
    by_cases hV : (V : Set ℂ) = ∅
    · have e : {ω | Disjoint (B ω) V} ∩ F = {ω | Disjoint (U ω) V} ∩ F := by
        ext ω
        simp only [mem_inter_iff, mem_ofPred_eq, hV, disjoint_empty, true_and]
      rw [e]
      exact mem_aeSigma_of_isHistoryAvoidanceLocal hhm hlocU' hVH hG hd hF (hdetE _ (hUV.inter hF))
    · have hsub : {ω | Disjoint (B ω) V} ⊆ E := by
        intro ω hω
        by_contra hωE
        have hω' : Disjoint (B ω) V := hω
        rw [hBH ω hωE] at hω'
        obtain ⟨z, hz⟩ := nonempty_iff_ne_empty.2 hV
        exact disjoint_left.1 hω' (hVH hz) hz
      have hFE : MeasurableSet[ℋ₀ ⊔ MeasurableSpace.generateFrom {E}] (E ∩ F) := hEg.inter hF
      obtain ⟨K, hK, hKe⟩ := mem_aeSigma_of_isHistoryAvoidanceLocal hhm hlocU' hVH hG hd hFE
        (hdetE _ (hUV.inter hFE))
      refine ⟨K, hK, EventuallyEq.trans ?_ hKe⟩
      filter_upwards [hUB] with ω hω
      show (ω ∈ {ω | Disjoint (B ω) V} ∩ F) = (ω ∈ {ω | Disjoint (U ω) V} ∩ (E ∩ F))
      apply propext
      simp only [mem_inter_iff, mem_ofPred_eq]
      constructor
      · rintro ⟨h1, h2⟩
        have hωE : ω ∈ E := hsub h1
        exact ⟨by rw [hω hωE]; exact h1, hωE, h2⟩
      · rintro ⟨h1, hωE, h2⟩
        exact ⟨by rw [← hω hωE]; exact h1, h2⟩
  have hE' : MeasurableSet[mΩ ⊓ aeSigma (ℋ₀ ⊔ MeasurableSpace.generateFrom {E}) P] E :=
    ⟨hℋ₁ _ hE, E, hEg, EventuallyEq.rfl⟩
  exact GW2Sf.ae_mean_eq_on_marked_event hh inf_le_left (SB.Lv.Cmp.nullSets_le_inf_aeSigma _) hUm hBm hUc hBc
    (Restart.FCPlumb.isHistoryAvoidanceLocal_aeSigma hlocU') (Restart.FCPlumb.isHistoryAvoidanceLocal_aeSigma hlocB')
    hE' hUB hgU hgB

end InteractingSLE.Theorem14.GW2Psm
