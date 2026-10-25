import SupercriticalLQGUniqueness.B2.DG20Pt.HeatVersionPoint
import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableLiminfLocalized

 

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open LQGMetric

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

 

theorem ae_heat_smoothing_sequence_eq
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (ε : ℕ → Ioi (0 : ℝ))
    (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ δ, IsHeatSmoothing P h δ (X δ)) :
    ∀ᵐ ω ∂P, ∀ n z, X (ε n) ω z = heatMollify (ε n : ℝ) (h ω) z := by
  exact ae_all_iff.mpr fun n =>
    DG20Pt.dg20_heat_smoothing_ae_heatMollify P h hh (ε n) (X (ε n)) (hX (ε n))

 

theorem ae_lowerNeighborhoodObservable_localized_eq_heat_of_normalized
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (ξ : Ioi (0 : ℝ))
    {V : Set ℂ} (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    (ε : ℕ → Ioi (0 : ℝ))
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (a : ℕ → Ioi (0 : ℝ))
    (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ δ, IsHeatSmoothing P h δ (X δ)) :
    ∀ᵐ ω ∂P, ∀ x y : V,
      lowerNeighborhoodObservable
        (fun n => PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (a n)
          (LQGMetric.DFGPS.L217.locMollifyC (ε n : ℝ)
            (ε n).property (h ω))) V x y =
      lowerNeighborhoodObservable
        (fun n => PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (a n)
          (X (ε n) ω)) V x y := by
  exact ae_lowerNeighborhoodObservable_localized_eq_heat
    (LQGMetric.DFGPS.isGFFPlusBddCont_of_wp hh.1) ξ hV hVb
    ε hε a (fun n ω => X (ε n) ω)
    (ae_heat_smoothing_sequence_eq P h hh ε X hX)

end SupercriticalLQGUniqueness.B2.PfeAxioms
