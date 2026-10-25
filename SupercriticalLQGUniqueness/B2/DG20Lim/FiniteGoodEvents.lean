import SupercriticalLQGUniqueness.B2.DG20Lim.FiniteGoodEventualProbability
import SupercriticalLQGUniqueness.B2.DG20Lim.LocalizedGoodMarginal

 

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal
open LQGMetric LQGMetric.LFPP LQGMetric.Blueprint

namespace SupercriticalLQGUniqueness.B2.DG20Lim

def fullHeatGoodEvent {Ω : Type} (X : Ω → C(ℂ, ℝ)) (ξ : ℝ)
    (x y r : ℚ) (hr : 0 < r) (C : ℝ≥0∞) : Set Ω :=
  {ω | finiteAroundCoords (lfppContMetric ξ (X ω) (X ω).continuous)
    (centeredRatAnnulus x y r hr) ≤
    C * finiteCircleCoords (lfppContMetric ξ (X ω) (X ω).continuous)
      (centeredInnerCircle x y r hr, centeredOuterCircle x y r hr)}

theorem nullMeasurableSet_localizedGoodEvent
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P)
    (ξ : ℝ) (ε : Ioi (0 : ℝ)) (x y r : ℚ) (hr : 0 < r)
    (C : ℝ≥0∞) :
    NullMeasurableSet (localizedGoodEvent h ξ ε x y r hr C) P := by
  have hbad := nullMeasurableSet_finite_bad_ratio (P := P)
    (fun ω => lfppContMetric ξ
      (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property (h ω))
      (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property (h ω)).continuous)
    (measurable_local_lfpp_metric hh ξ ε).aemeasurable
    (centeredRatAnnulus x y r hr) C
  convert hbad.compl using 1
  ext ω
  simp only [localizedGoodEvent, mem_setOf_eq, mem_compl_iff, not_lt,
    finiteAroundCoords, finiteCircleCoords, centeredRatAnnulus]

theorem nullMeasurableSet_fullHeatGoodEvent
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ e, IsHeatSmoothing P h e (X e))
    (ξ : ℝ) (ε : Ioi (0 : ℝ)) (x y r : ℚ) (hr : 0 < r)
    (C : ℝ≥0∞) :
    NullMeasurableSet (fullHeatGoodEvent (X ε) ξ x y r hr C) P := by
  have hbad := nullMeasurableSet_finite_bad_ratio
    (fun ω => lfppContMetric ξ (X ε ω) (X ε ω).continuous)
    (aemeasurable_full_heat_lfpp_metric P h hh ξ ε (X ε) (hX ε))
    (centeredRatAnnulus x y r hr) C
  convert hbad.compl using 1
  ext ω
  simp only [fullHeatGoodEvent, mem_setOf_eq, mem_compl_iff, not_lt,
    finiteAroundCoords, finiteCircleCoords, centeredRatAnnulus]

end SupercriticalLQGUniqueness.B2.DG20Lim
