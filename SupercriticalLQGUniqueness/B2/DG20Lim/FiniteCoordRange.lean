import SupercriticalLQGUniqueness.B2.DG20Lim.FiniteChainSource
import SupercriticalLQGUniqueness.B2.DG20Lim.FiniteJointCoords
import SupercriticalLQGUniqueness.B2.DG20Lim.FiniteCoordEmbedding

 


set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem ae_circleCoords_range_of_coord_law
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} [IsFiniteMeasure P] {P' : Measure Ω'}
    (D : Ω → LQGMetric.ContMetric) (hD : AEMeasurable D P)
    (Y : Ω' → (RatCircle × RatCircle → ℝ≥0∞)) (hY : Measurable Y)
    (hLaw : P'.map Y = P.map (fun ω =>
      (measurableRatCoordsVersion D hD ω).1)) :
    ∀ᵐ ω ∂P', finiteCircleCoords (circleCoordsInv (Y ω)) = Y ω := by
  have hRange : MeasurableSet (Set.range finiteCircleCoords) :=
    measurableEmbedding_finiteCircleCoords.measurableSet_range
  have hSourceM : Measurable (fun ω =>
      (measurableRatCoordsVersion D hD ω).1) :=
    measurable_fst.comp (measurable_measurableRatCoordsVersion D hD)
  have hSource : ∀ᵐ ω ∂P,
      (measurableRatCoordsVersion D hD ω).1 ∈ Set.range finiteCircleCoords := by
    filter_upwards [ae_eq_measurableRatCoordsVersion D hD] with ω hω
    exact ⟨D ω, by simpa only [finiteRatCoords] using congrArg Prod.fst hω⟩
  have hSourceMap : ∀ᵐ q ∂P.map (fun ω =>
      (measurableRatCoordsVersion D hD ω).1),
      q ∈ Set.range finiteCircleCoords :=
    (ae_map_iff hSourceM.aemeasurable hRange).2 hSource
  have hTarget : ∀ᵐ ω ∂P', Y ω ∈ Set.range finiteCircleCoords :=
    (ae_map_iff hY.aemeasurable hRange).1 (hLaw ▸ hSourceMap)
  filter_upwards [hTarget] with ω ⟨d, hd⟩
  rw [← hd, circleCoordsInv_finiteCircleCoords]

 

theorem ae_finiteCircleCoords_chain
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Y : Ω → (RatCircle × RatCircle → ℝ≥0∞))
    (hRange : ∀ᵐ ω ∂P,
      finiteCircleCoords (circleCoordsInv (Y ω)) = Y ω)
    (hLen : ∀ᵐ ω ∂P, (circleCoordsInv (Y ω)).IsLength) :
    ∀ᵐ ω ∂P, ∀ (k : ℕ) (O : Fin (k + 1) → RatCircle),
      (∀ i j : Fin (k + 1), i ≠ j →
        Disjoint (O i).toSet (O j).toSet) →
      (∀ j : ℕ, (hj : 0 < j) → (hjk : j < k) →
        Disconnects (O ⟨j, by omega⟩).toSet
          (O ⟨j - 1, by omega⟩).toSet
          (O ⟨j + 1, by omega⟩).toSet) →
      (∑ j : Fin k,
        Y ω (O ⟨j.val, by omega⟩, O ⟨j.val + 1, by omega⟩)) ≤
        Y ω (O ⟨0, by omega⟩, O ⟨k, by omega⟩) := by
  filter_upwards [hRange, hLen] with ω hω hωLen
  intro k O hdisj hsep
  rw [← hω]
  exact finiteCircleDist_chain (circleCoordsInv (Y ω)) hωLen k O hdisj hsep

end SupercriticalLQGUniqueness.B2.DG20Lim
