import SupercriticalLQGUniqueness.B2.DG20Lim.LocalizedGoodEventLocal

 

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal
open LQGMetric LQGMetric.LFPP LQGMetric.Blueprint

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem aeEventIn_localized_bad_ratio_centered
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (ξ : ℝ) (ε : Ioi (0 : ℝ))
    (x y r : ℚ) (hr : 0 < r)
    (hεr : Real.sqrt (ε : ℝ) < (r : ℝ) / 4)
    (C : ℝ≥0∞) (R : ℝ) (z : ℂ) :
    AEEventIn P
      (fieldSigma (fun ω => addConst (h ω) (-circleAvg (h ω) R z))
        (widerCenteredAnnulus x y r))
      {ω | C * finiteCircleCoords
        (lfppContMetric ξ
          (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property (h ω))
          (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property (h ω)).continuous)
        (centeredInnerCircle x y r hr, centeredOuterCircle x y r hr) <
        finiteAroundCoords
        (lfppContMetric ξ
          (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property (h ω))
          (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property (h ω)).continuous)
        (centeredRatAnnulus x y r hr)} := by
  let Y : Ω → DistC := fun ω => addConst (h ω) (-circleAvg (h ω) R z)
  have hm : Measurable (fun ω => -circleAvg (h ω) R z) :=
    ((measurable_circleAvg_left R z).comp hh.1.measurable).neg
  have hY : Measurable Y := (hh.1.addConst hm).measurable
  have hloc := aeEventIn_localized_bad_ratio P Y hY ξ ε x y r hr hεr C
  have heq :
      {ω | C * finiteCircleCoords
        (lfppContMetric ξ
          (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property (Y ω))
          (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property (Y ω)).continuous)
        (centeredInnerCircle x y r hr, centeredOuterCircle x y r hr) <
        finiteAroundCoords
        (lfppContMetric ξ
          (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property (Y ω))
          (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property (Y ω)).continuous)
        (centeredRatAnnulus x y r hr)} =
      {ω | C * finiteCircleCoords
        (lfppContMetric ξ
          (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property (h ω))
          (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property (h ω)).continuous)
        (centeredInnerCircle x y r hr, centeredOuterCircle x y r hr) <
        finiteAroundCoords
        (lfppContMetric ξ
          (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property (h ω))
          (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property (h ω)).continuous)
        (centeredRatAnnulus x y r hr)} := by
    ext ω
    exact localized_bad_ratio_iff_addConst ξ (ε : ℝ) ε.property
      (h ω) (-circleAvg (h ω) R z)
      (centeredRatAnnulus x y r hr).toSet
      (centeredInnerCircle x y r hr).toSet
      (centeredOuterCircle x y r hr).toSet C
  simpa only [Y, heq] using hloc

end SupercriticalLQGUniqueness.B2.DG20Lim
