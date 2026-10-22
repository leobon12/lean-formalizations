import HigherDimLQGMetric.Amplify.TrialTransfer

/-! The witness probability pays only the coarse oscillation error. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory Set
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]

theorem amplify_wit_probability_le_trial_add_osc
    (hd : 2 ≤ d) {ξ Q : ℝ} (hξ : 0 < ξ)
    {D Dt : DistRd d → ContMetric d}
    (hD : IsSharpWeakExpMetric d ξ Q D)
    (hDt : IsSharpWeakExpMetric d ξ Q Dt)
    (F : Ω → DistRd d) (g : Ω → C(Rd d, ℝ))
    (hF : Measurable F) (hg : Measurable g)
    (hH : IsWholeSpaceLGF (fun ω => F ω + ofCont (g ω)) P)
    (cs a A₀ ℓ β₀ c1 δ : ℝ) (hc1 : 0 < c1) (hℓ : 0 < ℓ)
    {s : ℝ} (hs : 0 < s) (w : Rd d) :
    P ((fun ω => F ω + ofCont (g ω)) ⁻¹'
      WitEvent Dt D ξ Q cs⁻¹ a A₀ ℓ β₀ c1⁻¹ s w) ≤
      P (F ⁻¹' TrialEvent D Dt ξ Q cs c1 ℓ δ s w) +
      P {ω | ∃ x ∈ Metric.ball w (5 * s), ∃ y ∈ Metric.ball w (5 * s),
        δ < |g ω x - g ω y|} := by
  let W := (fun ω => F ω + ofCont (g ω)) ⁻¹'
    WitEvent Dt D ξ Q cs⁻¹ a A₀ ℓ β₀ c1⁻¹ s w
  let T := F ⁻¹' TrialEvent D Dt ξ Q cs c1 ℓ δ s w
  let B := {ω | ∃ x ∈ Metric.ball w (5 * s), ∃ y ∈ Metric.ball w (5 * s),
    δ < |g ω x - g ω y|}
  have hae := amplify_ae_trial_of_wit hd hξ hD hDt F g hF hg hH
    cs a A₀ ℓ β₀ c1 δ hc1 hℓ
  have hmono : P W ≤ P (T ∪ B) := by
    apply measure_mono_ae
    filter_upwards [hae] with ω hω hW
    by_cases hb : ω ∈ B
    · exact Or.inr hb
    · left
      apply hω s hs w
      · intro x hx y hy
        exact le_of_not_gt (fun hgt => hb ⟨x, hx, y, hy, hgt⟩)
      · exact hW
  exact hmono.trans (measure_union_le T B)

end HigherDimLQGMetric
