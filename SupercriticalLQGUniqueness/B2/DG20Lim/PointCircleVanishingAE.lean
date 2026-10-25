import SupercriticalLQGUniqueness.B2.DG20Lim.SmallEndpointProbability
import SupercriticalLQGUniqueness.B2.DG20Lim.RDataFromCoords

 

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem ae_point_circle_vanishing_of_near_point_probability
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Ylim : Ω → (LQGMetric.CoordJ → ℝ) × RatCoords)
    (Z : RatCircle) (hZ : Z.radius = 0)
    (hRData : ∀ᵐ ω ∂P, ∃ R : RData,
      R.across = (fun O Q => (Ylim ω).2.1 (O, Q)) ∧
      R.around = (Ylim ω).2.2)
    (hnear : ∀ δ : ℝ≥0∞, 0 < δ → ∀ η : ℝ, 0 < η →
      ∃ Q : RatCircle, Q.radius = 0 ∧ Q.center ≠ Z.center ∧
        P {ω | δ ≤ (Ylim ω).2.1 (Z, Q)} ≤ ENNReal.ofReal η) :
    ∀ᵐ ω ∂P, ∃ R : RData,
      R.across = (fun O Q => (Ylim ω).2.1 (O, Q)) ∧
      R.around = (Ylim ω).2.2 ∧
      ∀ O : ℕ → RatCircle,
        (∀ᶠ n in atTop, (O n).Surrounds Z.center) →
        Tendsto (fun n => ((O n).radius : ℝ)) atTop (𝓝 0) →
        Tendsto (fun n => R.across Z (O n)) atTop (𝓝 0) := by
  have hsmall := ae_arbitrarily_small_endpoints_of_prob P
    (fun ω Q => (Ylim ω).2.1 (Z, Q))
    (fun Q => Q.radius = 0 ∧ Q.center ≠ Z.center)
    (fun δ hδ η hη => by
      obtain ⟨Q, hQ, hQne, hp⟩ := hnear δ hδ η hη
      exact ⟨Q, ⟨hQ, hQne⟩, hp⟩)
  filter_upwards [hRData, hsmall] with ω hR hω
  obtain ⟨R, hAcross, hAround⟩ := hR
  refine ⟨R, hAcross, hAround, ?_⟩
  intro O hO hr
  apply R.across_point_circle_tendsto_zero_of_small_points Z hZ ?_ O hO hr
  intro δ hδ
  obtain ⟨Q, ⟨hQ, hQne⟩, hcost⟩ := hω δ hδ
  exact ⟨Q, hQ, hQne, by simpa only [hAcross] using hcost⟩

end SupercriticalLQGUniqueness.B2.DG20Lim
