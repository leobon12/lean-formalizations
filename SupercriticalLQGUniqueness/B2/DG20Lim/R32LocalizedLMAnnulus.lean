import SupercriticalLQGUniqueness.B2.DG20Lim.R32LocalizedGoodRepresentative

 



set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal
open LQGMetric LQGMetric.LFPP LQGMetric.Blueprint

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem widerCenteredAnnulus_zero_eq_annulusR32 (r : ℚ) :
    widerCenteredAnnulusR32 0 0 r =
      annulus 0 ((r : ℝ) / 4) (8 * (r : ℝ)) := by
  ext w
  have hc : Complex.mk (0 : ℝ) (0 : ℝ) = (0 : ℂ) := rfl
  simp [widerCenteredAnnulusR32, annulus, hc]

theorem widerCenteredAnnulus_eq_annulusR32 (x y r : ℚ) :
    widerCenteredAnnulusR32 x y r =
      annulus (Complex.mk (x : ℝ) (y : ℝ)) ((r : ℝ) / 4)
        (8 * (r : ℝ)) := by
  ext w
  simp only [widerCenteredAnnulusR32, annulus]

theorem widerCenteredAnnulus_zero_eq_lm_annulusR32 (r : ℚ) :
    widerCenteredAnnulusR32 0 0 r =
      annulus 0 ((1 / 64 : ℝ) * (16 * (r : ℝ)))
        ((1 / 2 : ℝ) * (16 * (r : ℝ))) := by
  rw [widerCenteredAnnulus_zero_eq_annulusR32]
  congr 1 <;> ring

theorem widerCenteredAnnulus_eq_lm_annulusR32 (x y r : ℚ) :
    widerCenteredAnnulusR32 x y r =
      annulus (Complex.mk (x : ℝ) (y : ℝ))
        ((1 / 64 : ℝ) * (16 * (r : ℝ)))
        ((1 / 2 : ℝ) * (16 * (r : ℝ))) := by
  rw [widerCenteredAnnulus_eq_annulusR32]
  congr 1 <;> ring

theorem exists_localized_good_lm_representativeR32
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (ξ : ℝ) (ε : Set.Ioi (0 : ℝ))
    (r : ℚ) (hr : 0 < r)
    (hεr : Real.sqrt (ε : ℝ) < (r : ℝ) / 4)
    (C : ℝ≥0∞) :
    ∃ E : Set Ω,
      MeasurableSet[fieldSigma
        (fun ω => addConst (h ω)
          (-circleAvg (h ω) (16 * (r : ℝ)) 0))
        (annulus 0 ((1 / 64 : ℝ) * (16 * (r : ℝ)))
          ((1 / 2 : ℝ) * (16 * (r : ℝ))))] E ∧
      E =ᵐ[P] {ω | finiteAroundCoords
        (lfppContMetric ξ
          (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property (h ω))
          (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property (h ω)).continuous)
        (centeredRatAnnulusR32 0 0 r hr) ≤
        C * finiteCircleCoords
        (lfppContMetric ξ
          (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property (h ω))
          (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property (h ω)).continuous)
        (centeredInnerCircleR32 0 0 r hr, centeredOuterCircleR32 0 0 r hr)} := by
  rw [← widerCenteredAnnulus_zero_eq_lm_annulusR32 r]
  exact exists_measurable_localized_good_ratio_centeredR32
    P h hh ξ ε 0 0 r hr hεr C (16 * (r : ℝ)) 0

end SupercriticalLQGUniqueness.B2.DG20Lim
