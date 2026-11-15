/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.RetPlumbProofInputsCond
import InteractingSLE.Spec.Restart.RetPlumbProofInputsWord
import InteractingSLE.Spec.Restart.RetPlumbProofSplit
import InteractingSLE.Spec.Sec5.GlueCond

/-!
# Generic glue for the retained stopped models

Packet PROVE-T15-RET3. Three small facts used to apply PROVE-RETPLUMB's driver construction and
PROVE-T15-RET's model constructor to an arbitrary mean-identifying retained word:

* `flowField_chartTransport`: shifting a chart transport by a constant is the chart transport with that
  constant (the shifted chart field is the chart transport used by the safe laws);
* `hasSafeLaw_congr_field`, `hasSafeMembers_congr_field`: K2's two safe inputs only see the field through
  integrals over events contained in the live event, so they pass to an almost surely equal field there;
* `typeSet_congr`, `typeXL_congr`, `typeXR_congr`, `isFlowType_of_forces_eq`: the flow-line type of a word
  and its fixed-type positions depend only on its force data (number of marks and padded flow word), which
  `RetAux79.word_forces_eq_of_mean_integrals` identifies for words with the same mean pairings.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.Restart.RetFin

open LQGMetric (DistOn TestOn)
open DomainMarkov DomainMarkov.K2 RetAux79

/-! ### The shifted chart field -/

/-- **A constant shift of a chart transport** is the chart transport with that constant. -/
theorem flowField_chartTransport {c : Chart} (hc : c.IsConformal) (σ s k : ℝ)
    (f : DistOn upperHalfPlaneOpens) :
    Exist.flowField 0 s (Chart.chartTransport hc σ 0 k f) = Chart.chartTransport hc σ s k f := by
  ext φ
  rw [Exist.flowField_apply, Sec5.GlueCond.pushTest_shiftChart_zero, Chart.chartTransport_apply',
    Chart.chartTransport_apply', Chart.oneDist_apply]
  ring

/-! ### The safe inputs see the field only on the live event -/

section Safe

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓗 : Filtration ℝ≥0 mΩ} {F : Set Ω}
  {V : Ω → ℝ≥0∞} {nL nR : ℕ} {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {X X' : Ω → DistOn upperHalfPlaneOpens}

/-- **K2's (S) for an almost surely equal field on the live event.** -/
theorem hasSafeLaw_congr_field (he : ∀ᵐ ω ∂P, ω ∈ F → X' ω = X ω)
    (h : HasSafeLaw κ ρL ρR P 𝓗 F V W VL VR X) : HasSafeLaw κ ρL ρR P 𝓗 F V W VL VR X' := by
  intro ψ q D hD hsafe
  rw [← h ψ q D hD hsafe]
  refine setIntegral_congr_ae (𝓗.le q _ hD) ?_
  filter_upwards [he, hsafe] with ω e hs hωD
  rw [e (hs hωD).1]

/-- **K2's (L) for an almost surely equal field on the live event.** -/
theorem hasSafeMembers_congr_field (he : ∀ᵐ ω ∂P, ω ∈ F → X' ω = X ω)
    (h : HasSafeMembers P 𝓗 F V W X) : HasSafeMembers P 𝓗 F V W X' := by
  intro s Fb hFb D hD hsafe f Ξ
  have e : ∀ Φ : TestOn upperHalfPlaneOpens, ∫ ω in D, Complex.exp (Complex.I * (X' ω Φ : ℂ)) ∂P =
      ∫ ω in D, Complex.exp (Complex.I * (X ω Φ : ℂ)) ∂P := fun Φ => by
    refine setIntegral_congr_ae (𝓗.le s _ hD) ?_
    filter_upwards [he, hsafe] with ω e hs hωD
    rw [e (hs hωD).1]
  rw [e, e]
  exact h s Fb hFb D hD hsafe f Ξ

end Safe

/-! ### Types depend only on the force data -/

section Types

variable {κ θ : ℝ} {c c' : BoundaryWord}

/-- **Membership in a type set depends only on the force data.** -/
theorem typeSet_congr {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hNL : flowLineNL c.fn c.jumps 0 = flowLineNL c'.fn c'.jumps 0)
    (hNR : flowLineNR c.fn c.jumps 0 = flowLineNR c'.fn c'.jumps 0)
    (hP : flowPad κ θ (c, 0) = flowPad κ θ (c', 0)) :
    c ∈ FCDet.typeSet κ θ nL nR ρL ρR ↔ c' ∈ FCDet.typeSet κ θ nL nR ρL ρR := by
  simp only [FCDet.typeSet, mem_inter_iff, mem_preimage, mem_singleton_iff, mem_ofPred_eq, hNL, hNR, hP]

/-- **The fixed-type left positions depend only on the force data.** -/
theorem typeXL_congr {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hNL : flowLineNL c.fn c.jumps 0 = flowLineNL c'.fn c'.jumps 0)
    (hNR : flowLineNR c.fn c.jumps 0 = flowLineNR c'.fn c'.jumps 0)
    (hP : flowPad κ θ (c, 0) = flowPad κ θ (c', 0)) :
    FCDet.typeXL κ θ nL nR ρL ρR c = FCDet.typeXL κ θ nL nR ρL ρR c' := by
  classical
  by_cases hc : c ∈ FCDet.typeSet κ θ nL nR ρL ρR
  · have hc' := (typeSet_congr hNL hNR hP).1 hc
    simp only [FCDet.typeXL, hc, hc', ↓reduceIte, hP]
  · have hc' : c' ∉ FCDet.typeSet κ θ nL nR ρL ρR := fun h => hc ((typeSet_congr hNL hNR hP).2 h)
    simp only [FCDet.typeXL, hc, hc', ↓reduceIte]

/-- **The fixed-type right positions depend only on the force data.** -/
theorem typeXR_congr {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hNL : flowLineNL c.fn c.jumps 0 = flowLineNL c'.fn c'.jumps 0)
    (hNR : flowLineNR c.fn c.jumps 0 = flowLineNR c'.fn c'.jumps 0)
    (hP : flowPad κ θ (c, 0) = flowPad κ θ (c', 0)) :
    FCDet.typeXR κ θ nL nR ρL ρR c = FCDet.typeXR κ θ nL nR ρL ρR c' := by
  classical
  by_cases hc : c ∈ FCDet.typeSet κ θ nL nR ρL ρR
  · have hc' := (typeSet_congr hNL hNR hP).1 hc
    simp only [FCDet.typeXR, hc, hc', ↓reduceIte, hP]
  · have hc' : c' ∉ FCDet.typeSet κ θ nL nR ρL ρR := fun h => hc ((typeSet_congr hNL hNR hP).2 h)
    simp only [FCDet.typeXR, hc, hc', ↓reduceIte]

/-- **A word with the force data of a typed word has that word's type, at that word's positions.** -/
theorem isFlowType_of_forces_eq (a : ForceWordType)
    (hNL : flowLineNL c.fn c.jumps 0 = flowLineNL c'.fn c'.jumps 0)
    (hNR : flowLineNR c.fn c.jumps 0 = flowLineNR c'.fn c'.jumps 0)
    (hP : flowPad κ θ (c, 0) = flowPad κ θ (c', 0)) (hc : c ∈ forceTypeSet κ θ a) :
    FCDet.IsFlowType κ θ c' (FCDet.typeXL κ θ a.nL a.nR a.rhoL a.rhoR c)
      (FCDet.typeXR κ θ a.nL a.nR a.rhoL a.rhoR c) a.rhoL a.rhoR := by
  rw [typeXL_congr hNL hNR hP, typeXR_congr hNL hNR hP]
  exact FCDet.isFlowType_of_mem_typeSet ((typeSet_congr hNL hNR hP).1 hc)

/-- **Sorted words with the same mean pairings lie in the same type sets.** -/
theorem mem_forceTypeSet_iff_of_mean_integrals (a : ForceWordType) (hc : c.IsSorted) (hc' : c'.IsSorted)
    (he : ∀ φ : TestOn upperHalfPlaneOpens, ∫ z, c.mean z * φ z = ∫ z, c'.mean z * φ z) :
    c ∈ forceTypeSet κ θ a ↔ c' ∈ forceTypeSet κ θ a := by
  obtain ⟨hNL, hNR, hP⟩ := word_forces_eq_of_mean_integrals κ θ hc hc' he
  exact typeSet_congr hNL hNR hP

/-- **A sorted word with the mean pairings of a typed sorted word has its type and positions.** -/
theorem isFlowType_of_mean_integrals (a : ForceWordType) (hc : c.IsSorted) (hc' : c'.IsSorted)
    (he : ∀ φ : TestOn upperHalfPlaneOpens, ∫ z, c.mean z * φ z = ∫ z, c'.mean z * φ z)
    (hct : c ∈ forceTypeSet κ θ a) :
    FCDet.IsFlowType κ θ c' (FCDet.typeXL κ θ a.nL a.nR a.rhoL a.rhoR c)
      (FCDet.typeXR κ θ a.nL a.nR a.rhoL a.rhoR c) a.rhoL a.rhoR := by
  obtain ⟨hNL, hNR, hP⟩ := word_forces_eq_of_mean_integrals κ θ hc hc' he
  exact isFlowType_of_forces_eq a hNL hNR hP hct

end Types

end InteractingSLE.Restart.RetFin
