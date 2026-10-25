import SupercriticalLQGUniqueness.B2.DG20Lim.R32LocalizedGoodFullTransfer
import SupercriticalLQGUniqueness.B2.DG20Lim.FiniteGoodEventualProbability
import SupercriticalLQGUniqueness.B2.DG20Lim.R32LocalizedGoodMarginal

 



set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal
open LQGMetric LQGMetric.LFPP LQGMetric.Blueprint

namespace SupercriticalLQGUniqueness.B2.DG20Lim

def fullHeatGoodEventR32 {Ω : Type} (X : Ω → C(ℂ, ℝ)) (ξ : ℝ)
    (x y r : ℚ) (hr : 0 < r) (C : ℝ≥0∞) : Set Ω :=
  {ω | finiteAroundCoords (lfppContMetric ξ (X ω) (X ω).continuous)
    (centeredRatAnnulusR32 x y r hr) ≤
    C * finiteCircleCoords (lfppContMetric ξ (X ω) (X ω).continuous)
      (centeredInnerCircleR32 x y r hr, centeredOuterCircleR32 x y r hr)}

theorem nullMeasurableSet_localizedGoodEventR32
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P)
    (ξ : ℝ) (ε : Ioi (0 : ℝ)) (x y r : ℚ) (hr : 0 < r)
    (C : ℝ≥0∞) :
    NullMeasurableSet (localizedGoodEventR32 h ξ ε x y r hr C) P := by
  have hbad := nullMeasurableSet_finite_bad_ratio (P := P)
    (fun ω => lfppContMetric ξ
      (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property (h ω))
      (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property (h ω)).continuous)
    (measurable_local_lfpp_metricR32 hh ξ ε).aemeasurable
    (centeredRatAnnulusR32 x y r hr) C
  convert hbad.compl using 1
  ext ω
  simp only [localizedGoodEventR32, mem_setOf_eq, mem_compl_iff, not_lt,
    finiteAroundCoords, finiteCircleCoords, centeredRatAnnulusR32]

theorem nullMeasurableSet_fullHeatGoodEventR32
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ e, IsHeatSmoothing P h e (X e))
    (ξ : ℝ) (ε : Ioi (0 : ℝ)) (x y r : ℚ) (hr : 0 < r)
    (C : ℝ≥0∞) :
    NullMeasurableSet (fullHeatGoodEventR32 (X ε) ξ x y r hr C) P := by
  have hbad := nullMeasurableSet_finite_bad_ratio
    (fun ω => lfppContMetric ξ (X ε ω) (X ε ω).continuous)
    (aemeasurable_full_heat_lfpp_metric P h hh ξ ε (X ε) (hX ε))
    (centeredRatAnnulusR32 x y r hr) C
  convert hbad.compl using 1
  ext ω
  simp only [fullHeatGoodEventR32, mem_setOf_eq, mem_compl_iff, not_lt,
    finiteAroundCoords, finiteCircleCoords, centeredRatAnnulusR32]

end SupercriticalLQGUniqueness.B2.DG20Lim
