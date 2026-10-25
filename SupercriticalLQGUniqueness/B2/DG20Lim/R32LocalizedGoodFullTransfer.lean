import SupercriticalLQGUniqueness.B2.DG20Lim.R32LocalizedGoodSequenceTransfer

 



set_option autoImplicit false
noncomputable section

open Set Filter MeasureTheory Topology
open scoped ENNReal
open LQGMetric LQGMetric.Blueprint LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem centeredRatAnnulus_good_heat_of_local_compareR32
    (ξ : ℝ) (ε : Ioi (0 : ℝ)) (g : DistC) (φ : C(ℂ, ℝ))
    (hφ : ∀ z, φ z = heatMollify (ε : ℝ) g z)
    (x y r : ℚ) (hr : 0 < r) (C : ℝ≥0∞)
    (hcmp : ∀ z w : ℂ,
      lfppLocOn ξ (ε : ℝ) ε.property g (bufferedCenteredAnnulusR32 x y r) z w ≤
        ENNReal.ofReal 2 *
          lfppDOn ξ (heatMollify (ε : ℝ) g) (bufferedCenteredAnnulusR32 x y r) z w ∧
      lfppDOn ξ (heatMollify (ε : ℝ) g) (bufferedCenteredAnnulusR32 x y r) z w ≤
        ENNReal.ofReal 2 *
          lfppLocOn ξ (ε : ℝ) ε.property g (bufferedCenteredAnnulusR32 x y r) z w)
    (hgood : (lfppContMetric ξ
        (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property g)
        (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property g).continuous).aroundDist
        (centeredRatAnnulusR32 x y r hr).toSet
        (centeredInnerCircleR32 x y r hr).toSet
        (centeredOuterCircleR32 x y r hr).toSet ≤
      C * setDist (lfppContMetric ξ
        (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property g)
        (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property g).continuous)
        (centeredInnerCircleR32 x y r hr).toSet
        (centeredOuterCircleR32 x y r hr).toSet) :
    (lfppContMetric ξ φ φ.continuous).aroundDist
        (centeredRatAnnulusR32 x y r hr).toSet
        (centeredInnerCircleR32 x y r hr).toSet
        (centeredOuterCircleR32 x y r hr).toSet ≤
      (ENNReal.ofReal 2 * C * ENNReal.ofReal 2) *
        setDist (lfppContMetric ξ φ φ.continuous)
          (centeredInnerCircleR32 x y r hr).toSet
          (centeredOuterCircleR32 x y r hr).toSet := by
  have hφeq : (φ : ℂ → ℝ) = heatMollify (ε : ℝ) g := funext hφ
  apply centeredRatAnnulus_good_of_local_lfpp_compareR32 ξ
    (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property g)
    φ x y r hr (ENNReal.ofReal 2) C (by norm_num) ENNReal.ofReal_ne_top
  · intro u v
    change lfppDOn ξ φ (bufferedCenteredAnnulusR32 x y r) u v ≤
      ENNReal.ofReal 2 * lfppLocOn ξ (ε : ℝ) ε.property g
        (bufferedCenteredAnnulusR32 x y r) u v
    rw [hφeq]
    exact (hcmp u v).2
  · intro u v
    change lfppLocOn ξ (ε : ℝ) ε.property g
      (bufferedCenteredAnnulusR32 x y r) u v ≤
        ENNReal.ofReal 2 * lfppDOn ξ φ (bufferedCenteredAnnulusR32 x y r) u v
    rw [hφeq]
    exact (hcmp u v).1
  · exact hgood

theorem ae_eventually_full_good_of_local_goodR32
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P)
    (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ e, IsHeatSmoothing P h e (X e))
    (ξ : ℝ) (ε : ℕ → Ioi (0 : ℝ))
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 (0 : ℝ)))
    (x y r : ℚ) (hr : 0 < r) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ C : ℝ≥0∞,
      (lfppContMetric ξ
          (LQGMetric.DFGPS.L217.locMollifyC (ε n : ℝ) (ε n).property (h ω))
          (LQGMetric.DFGPS.L217.locMollifyC (ε n : ℝ) (ε n).property (h ω)).continuous).aroundDist
          (centeredRatAnnulusR32 x y r hr).toSet
          (centeredInnerCircleR32 x y r hr).toSet
          (centeredOuterCircleR32 x y r hr).toSet ≤
        C * setDist (lfppContMetric ξ
          (LQGMetric.DFGPS.L217.locMollifyC (ε n : ℝ) (ε n).property (h ω))
          (LQGMetric.DFGPS.L217.locMollifyC (ε n : ℝ) (ε n).property (h ω)).continuous)
          (centeredInnerCircleR32 x y r hr).toSet
          (centeredOuterCircleR32 x y r hr).toSet →
      (lfppContMetric ξ (X (ε n) ω) (X (ε n) ω).continuous).aroundDist
          (centeredRatAnnulusR32 x y r hr).toSet
          (centeredInnerCircleR32 x y r hr).toSet
          (centeredOuterCircleR32 x y r hr).toSet ≤
        (ENNReal.ofReal 2 * C * ENNReal.ofReal 2) *
          setDist (lfppContMetric ξ (X (ε n) ω) (X (ε n) ω).continuous)
            (centeredInnerCircleR32 x y r hr).toSet
            (centeredOuterCircleR32 x y r hr).toSet := by
  have hField : ∀ᵐ ω ∂P, ∀ n, ∀ z,
      X (ε n) ω z = heatMollify (ε n : ℝ) (h ω) z := by
    rw [ae_all_iff]
    intro n
    exact B2.DG20Pt.dg20_heat_smoothing_ae_heatMollify
      P h hh (ε n) (X (ε n)) (hX (ε n))
  filter_upwards [hField,
    ae_eventually_localized_lfpp_compare_on_buffer_sequenceR32 hh ξ x y r ε hε]
    with ω hφ hcmp
  filter_upwards [hcmp] with n hn
  intro C hgood
  exact centeredRatAnnulus_good_heat_of_local_compareR32 ξ (ε n) (h ω)
    (X (ε n) ω) (hφ n) x y r hr C hn hgood

end SupercriticalLQGUniqueness.B2.DG20Lim
