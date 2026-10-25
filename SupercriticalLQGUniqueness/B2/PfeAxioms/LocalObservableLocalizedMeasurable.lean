import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableNeighborhoodMeasurable
import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableLocalizedCompare

 

set_option autoImplicit false
noncomputable section

open Set Topology MeasureTheory
open scoped ENNReal
open LQGMetric LQGMetric.DFGPS.L217

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem measurable_normalizedLocalizedLFPP_neighborhood
    (ξ : ℝ) (a : Set.Ioi (0 : ℝ))
    (ε : ℝ) (hε : 0 < ε)
    {V : Set ℂ} (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    (x y : V) (ρ : ℝ) :
    Measurable fun g : DistC => neighborhoodInternal
      (PfeWeyl.normalizedLFPPMetric ξ a (locMollifyC ε hε g)) V x y ρ := by
  apply measurable_normalizedLFPP_neighborhood ξ a
    (X := locMollifyC ε hε) (fun z =>
      (continuous_eval_const z).measurable.comp
        (measurable_locMollifyC ε hε)) hV hVb

theorem normalizedLocalizedLFPP_neighborhood_congr
    (ξ ε : Set.Ioi (0 : ℝ)) (a : Set.Ioi (0 : ℝ))
    {V : Set ℂ} (hV : IsOpen V)
    (O : TopologicalSpace.Opens ℂ)
    (hVO : ∀ z ∈ V, Metric.closedBall z (Real.sqrt (ε : ℝ)) ⊆ O)
    {g g' : DistC} (he : restrictTo O g = restrictTo O g')
    (x y : V) (ρ : ℝ) :
    neighborhoodInternal (PfeWeyl.normalizedLFPPMetric (ξ : ℝ) a
      (locMollifyC (ε : ℝ) ε.property g)) V x y ρ =
    neighborhoodInternal (PfeWeyl.normalizedLFPPMetric (ξ : ℝ) a
      (locMollifyC (ε : ℝ) ε.property g')) V x y ρ := by
  unfold neighborhoodInternal
  apply iInf_congr
  intro u
  apply iInf_congr
  intro hu
  apply iInf_congr
  intro v
  apply iInf_congr
  intro hv
  rw [normalizedLocalizedLFPPMetric_internal_eq_localizedLFPP ξ a ε g hV u v,
    normalizedLocalizedLFPPMetric_internal_eq_localizedLFPP ξ a ε g' hV u v]
  exact congrArg (ENNReal.ofReal ((a : ℝ)⁻¹) * ·)
    (localizedLFPP_congr ξ ε V O hVO he u v)

theorem comap_normalizedLocalizedLFPP_neighborhood_le_fieldSigma
    {Ω : Type} [MeasurableSpace Ω]
    (ξ ε : Set.Ioi (0 : ℝ)) (a : Set.Ioi (0 : ℝ))
    {V : Set ℂ} (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    (O : TopologicalSpace.Opens ℂ)
    (hVO : ∀ z ∈ V, Metric.closedBall z (Real.sqrt (ε : ℝ)) ⊆ O)
    (x y : V) (ρ : ℝ) (Y : Ω → DistC) :
    MeasurableSpace.comap
      (fun ω => neighborhoodInternal
        (PfeWeyl.normalizedLFPPMetric (ξ : ℝ) a
          (locMollifyC (ε : ℝ) ε.property (Y ω))) V x y ρ)
      inferInstance ≤ LQGMetric.Blueprint.fieldSigma Y O := by
  exact comap_le_fieldSigma_of_local
    (measurable_normalizedLocalizedLFPP_neighborhood (ξ : ℝ) a
      (ε : ℝ) ε.property hV hVb x y ρ) O
    (fun g g' he => normalizedLocalizedLFPP_neighborhood_congr
      ξ ε a hV O hVO he x y ρ) Y

end SupercriticalLQGUniqueness.B2.PfeAxioms
