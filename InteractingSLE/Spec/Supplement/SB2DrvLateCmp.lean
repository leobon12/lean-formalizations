/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkUnionLaw
import InteractingSLE.Spec.Supplement.GW2SfMeanVersions
import InteractingSLE.Spec.Restart.FCLocality

/-!
# Comparing local-set means on an event, for field-determined marked local sets

Packet PROVE-T14-SB2DRV (round 7), the comparison step of the late regime of SB2(1)'s (S) line mean. FIN's union
(the retained set with the coupling hull at `min(t, σ_k)`) and the (S) line set agree only on an event `E` that the
line marks see, but the union's own marks do not. With field determination this is no obstruction:

* **`isHistoryAvoidanceLocal_sup_generateFrom`** (pull-out): if `U` is marked local for `ℋ₀` and `B` for `ℋ₁`, both
  with mark-measurable avoidance events and marks determined by the field, and `U = B` almost surely on `E ∈ ℋ₁`, then
  `U` is marked local for `ℋ₀ ⊔ σ(E)` (the events `F` with `{U ∩ V = ∅} ∩ F` in the complementary σ-algebra form the
  trace σ-algebra `WalkLaw.traceSigma`, which contains `ℋ₀` and, through `B`, the event `E`);
* **`ae_mean_eq_on_event_of_det`**: then the local-set means of `U` and `B` agree almost surely on `E`
  (`GW2Sf.ae_mean_eq_on_marked_event` for the completed marks `ℋ₀ ⊔ σ(E)`, for which `B` is marked local as
  `ℋ₀ ⊔ σ(E) ≤ ℋ₁`).

Generic; no source theorem is replaced.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set TopologicalSpace
open QuantumZipper (H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lv.Cmp

open LocalSets WalkLaw

variable {Ω : Type u} {ℋ₀ ℋ₁ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens}

/-- **Marks extended by an event on which the set agrees with a better-marked one** (pull-out). -/
theorem isHistoryAvoidanceLocal_sup_generateFrom (hhm : Measurable h) {U B : Ω → Set ℂ}
    (hU : ∀ V : Opens ℂ, (V : Set ℂ) ⊆ H → MeasurableSet[ℋ₀] {ω | Disjoint (U ω) V})
    (hdet₀ : ℋ₀ ≤ aeSigma (MeasurableSpace.comap h inferInstance) P)
    (hlocU : WholeField.IsHistoryAvoidanceLocal ℋ₀ U h P)
    (hB : ∀ V : Opens ℂ, (V : Set ℂ) ⊆ H → MeasurableSet[ℋ₁] {ω | Disjoint (B ω) V})
    (hdet₁ : ℋ₁ ≤ aeSigma (MeasurableSpace.comap h inferInstance) P)
    (hlocB : WholeField.IsHistoryAvoidanceLocal ℋ₁ B h P) {E : Set Ω} (hE : MeasurableSet[ℋ₁] E)
    (hUB : ∀ᵐ ω ∂P, ω ∈ E → U ω = B ω) :
    WholeField.IsHistoryAvoidanceLocal (ℋ₀ ⊔ MeasurableSpace.generateFrom {E}) U h P := by
  refine isHistoryAvoidanceLocal_of_mem_aeSigma hhm fun V G hVH hG hd F hF => ?_
  have hA₀ : MeasurableSet[complSigma P G h] {ω | Disjoint (U ω) V} := by
    have := mem_aeSigma_of_isHistoryAvoidanceLocal hhm hlocU hVH hG hd (@MeasurableSet.univ _ ℋ₀)
      (by simpa only [inter_univ] using hdet₀ _ (hU V hVH))
    simpa only [inter_univ] using this
  have hle : ℋ₀ ⊔ MeasurableSpace.generateFrom {E} ≤ WalkLaw.traceSigma (complSigma P G h) _ hA₀ := by
    refine sup_le (fun F' hF' => ?_) (MeasurableSpace.generateFrom_le ?_)
    · exact mem_aeSigma_of_isHistoryAvoidanceLocal hhm hlocU hVH hG hd hF'
        (hdet₀ _ ((hU V hVH).inter hF'))
    · intro s hs
      rw [show s = E from hs]
      obtain ⟨K, hK, hKe⟩ := mem_aeSigma_of_isHistoryAvoidanceLocal hhm hlocB hVH hG hd hE
        (hdet₁ _ ((hB V hVH).inter hE))
      refine ⟨K, hK, EventuallyEq.trans ?_ hKe⟩
      filter_upwards [hUB] with ω hω
      show (ω ∈ {ω | Disjoint (U ω) V} ∩ E) = (ω ∈ {ω | Disjoint (B ω) V} ∩ E)
      apply propext
      simp only [mem_inter_iff, mem_ofPred_eq]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨by rw [← hω h2]; exact h1, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨by rw [hω h2]; exact h1, h2⟩
  exact hle F hF

omit [IsProbabilityMeasure P] in
theorem nullSets_le_inf_aeSigma (ℋ : MeasurableSpace Ω) : Ito.nullSets P ≤ mΩ ⊓ aeSigma ℋ P := by
  refine MeasurableSpace.generateFrom_le fun N hN => ⟨hN.1, ∅, @MeasurableSet.empty _ ℋ, ?_⟩
  exact ae_eq_empty.2 hN.2

/-- **Means of two field-determined marked local sets agree on an event on which the sets agree**, the event being a
mark of the better-marked set. -/
theorem ae_mean_eq_on_event_of_det (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P) (hℋ₁ : ℋ₁ ≤ mΩ)
    (hle₀₁ : ℋ₀ ≤ ℋ₁) {U B : Ω → Set ℂ} (hUm : Measurable[mΩ, hittingSigma] U)
    (hBm : Measurable[mΩ, hittingSigma] B) (hUc : ∀ᵐ ω ∂P, U ω ⊆ H ∧ IsOpen (H \ U ω))
    (hBc : ∀ᵐ ω ∂P, B ω ⊆ H ∧ IsOpen (H \ B ω))
    (hU : ∀ V : Opens ℂ, (V : Set ℂ) ⊆ H → MeasurableSet[ℋ₀] {ω | Disjoint (U ω) V})
    (hdet₀ : ℋ₀ ≤ aeSigma (MeasurableSpace.comap h inferInstance) P)
    (hlocU : WholeField.IsHistoryAvoidanceLocal ℋ₀ U h P)
    (hB : ∀ V : Opens ℂ, (V : Set ℂ) ⊆ H → MeasurableSet[ℋ₁] {ω | Disjoint (B ω) V})
    (hdet₁ : ℋ₁ ≤ aeSigma (MeasurableSpace.comap h inferInstance) P)
    (hlocB : WholeField.IsHistoryAvoidanceLocal ℋ₁ B h P) {E : Set Ω} (hE : MeasurableSet[ℋ₁] E)
    (hUB : ∀ᵐ ω ∂P, ω ∈ E → U ω = B ω) {gU gB : Ω → DistOn upperHalfPlaneOpens}
    (hgU : IsLocalSetMean U h P gU) (hgB : IsLocalSetMean B h P gB) :
    ∀ᵐ ω ∂P, ω ∈ E → gU ω = gB ω := by
  have hℋ1 : ℋ₀ ⊔ MeasurableSpace.generateFrom {E} ≤ ℋ₁ :=
    sup_le hle₀₁ (MeasurableSpace.generateFrom_le (by rintro _ rfl; exact hE))
  have hlocU' := isHistoryAvoidanceLocal_sup_generateFrom hh.measurable hU hdet₀ hlocU hB hdet₁ hlocB hE hUB
  have hlocB' : WholeField.IsHistoryAvoidanceLocal (ℋ₀ ⊔ MeasurableSpace.generateFrom {E}) B h P :=
    fun V G hV hG hd F hF => hlocB V G hV hG hd F (hℋ1 _ hF)
  have hE' : MeasurableSet[mΩ ⊓ aeSigma (ℋ₀ ⊔ MeasurableSpace.generateFrom {E}) P] E :=
    ⟨hℋ₁ _ hE, E, le_sup_right (a := ℋ₀) _ (MeasurableSpace.measurableSet_generateFrom rfl), EventuallyEq.rfl⟩
  exact GW2Sf.ae_mean_eq_on_marked_event hh inf_le_left (nullSets_le_inf_aeSigma _) hUm hBm hUc hBc
    (Restart.FCPlumb.isHistoryAvoidanceLocal_aeSigma hlocU') (Restart.FCPlumb.isHistoryAvoidanceLocal_aeSigma hlocB')
    hE' hUB hgU hgB

end InteractingSLE.Theorem14.SB.Lv.Cmp
