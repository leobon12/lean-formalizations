import SupercriticalLQGUniqueness.B2.DG20Lim.LocalizedGoodRepresentative

 

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal
open LQGMetric LQGMetric.LFPP LQGMetric.Blueprint

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem widerCenteredAnnulus_zero_eq_annulus (r : ℚ) :
    widerCenteredAnnulus 0 0 r =
      annulus 0 ((r : ℝ) / 4) (8 * (r : ℝ)) := by
  ext w
  have hc : Complex.mk (0 : ℝ) (0 : ℝ) = (0 : ℂ) := rfl
  simp [widerCenteredAnnulus, annulus, hc]

theorem widerCenteredAnnulus_eq_annulus (x y r : ℚ) :
    widerCenteredAnnulus x y r =
      annulus (Complex.mk (x : ℝ) (y : ℝ)) ((r : ℝ) / 4)
        (8 * (r : ℝ)) := by
  ext w
  simp only [widerCenteredAnnulus, annulus]

theorem widerCenteredAnnulus_zero_eq_lm_annulus (r : ℚ) :
    widerCenteredAnnulus 0 0 r =
      annulus 0 ((1 / 64 : ℝ) * (16 * (r : ℝ)))
        ((1 / 2 : ℝ) * (16 * (r : ℝ))) := by
  rw [widerCenteredAnnulus_zero_eq_annulus]
  congr 1 <;> ring

theorem widerCenteredAnnulus_eq_lm_annulus (x y r : ℚ) :
    widerCenteredAnnulus x y r =
      annulus (Complex.mk (x : ℝ) (y : ℝ))
        ((1 / 64 : ℝ) * (16 * (r : ℝ)))
        ((1 / 2 : ℝ) * (16 * (r : ℝ))) := by
  rw [widerCenteredAnnulus_eq_annulus]
  congr 1 <;> ring

theorem exists_localized_good_lm_representative
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
        (centeredRatAnnulus 0 0 r hr) ≤
        C * finiteCircleCoords
        (lfppContMetric ξ
          (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property (h ω))
          (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property (h ω)).continuous)
        (centeredInnerCircle 0 0 r hr, centeredOuterCircle 0 0 r hr)} := by
  rw [← widerCenteredAnnulus_zero_eq_lm_annulus r]
  exact exists_measurable_localized_good_ratio_centered
    P h hh ξ ε 0 0 r hr hεr C (16 * (r : ℝ)) 0

end SupercriticalLQGUniqueness.B2.DG20Lim
