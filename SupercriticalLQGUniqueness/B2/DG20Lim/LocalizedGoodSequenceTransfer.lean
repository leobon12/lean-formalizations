import SupercriticalLQGUniqueness.B2.DG20Lim.EventualNullEventProbability
import SupercriticalLQGUniqueness.B2.DG20Lim.RationalGoodSequence

 


set_option autoImplicit false
noncomputable section

open Set Filter MeasureTheory Topology
open scoped ENNReal
open LQGMetric LQGMetric.Blueprint LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem ae_eventually_localized_good_of_full_good
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P)
    (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ e, IsHeatSmoothing P h e (X e))
    (ξ : ℝ) (ε : ℕ → Ioi (0 : ℝ))
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 (0 : ℝ)))
    (x y r : ℚ) (hr : 0 < r) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ C : ℝ≥0∞,
      (lfppContMetric ξ (X (ε n) ω) (X (ε n) ω).continuous).aroundDist
          (centeredRatAnnulus x y r hr).toSet
          (centeredInnerCircle x y r hr).toSet
          (centeredOuterCircle x y r hr).toSet ≤
        C * setDist (lfppContMetric ξ (X (ε n) ω) (X (ε n) ω).continuous)
          (centeredInnerCircle x y r hr).toSet
          (centeredOuterCircle x y r hr).toSet →
      (lfppContMetric ξ
          (LQGMetric.DFGPS.L217.locMollifyC (ε n : ℝ) (ε n).property (h ω))
          (LQGMetric.DFGPS.L217.locMollifyC (ε n : ℝ) (ε n).property (h ω)).continuous).aroundDist
          (centeredRatAnnulus x y r hr).toSet
          (centeredInnerCircle x y r hr).toSet
          (centeredOuterCircle x y r hr).toSet ≤
        (ENNReal.ofReal 2 * C * ENNReal.ofReal 2) *
          setDist (lfppContMetric ξ
            (LQGMetric.DFGPS.L217.locMollifyC (ε n : ℝ) (ε n).property (h ω))
            (LQGMetric.DFGPS.L217.locMollifyC (ε n : ℝ) (ε n).property (h ω)).continuous)
            (centeredInnerCircle x y r hr).toSet
            (centeredOuterCircle x y r hr).toSet := by
  have hField : ∀ᵐ ω ∂P, ∀ n, ∀ z,
      X (ε n) ω z = heatMollify (ε n : ℝ) (h ω) z := by
    rw [ae_all_iff]
    intro n
    exact B2.DG20Pt.dg20_heat_smoothing_ae_heatMollify
      P h hh (ε n) (X (ε n)) (hX (ε n))
  filter_upwards [hField,
    ae_eventually_localized_lfpp_compare_on_buffer_sequence hh ξ x y r ε hε]
    with ω hφ hcmp
  filter_upwards [hcmp] with n hn
  intro C hgood
  exact centeredRatAnnulus_good_local_of_heat_compare ξ (ε n) (h ω)
    (X (ε n) ω) (hφ n) x y r hr C hn hgood

end SupercriticalLQGUniqueness.B2.DG20Lim
