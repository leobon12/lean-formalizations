import SupercriticalLQGUniqueness.B2.DG20Lim.FullGoodIterationEventual
import SupercriticalLQGUniqueness.B2.DG20Lim.GoodAnnulusNormalize

 

set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal
open LQGMetric LQGMetric.LFPP LQGMetric.Blueprint

namespace SupercriticalLQGUniqueness.B2.DG20Lim

def normalizedGoodEvent {Ω : Type} (X : Ω → C(ℂ, ℝ))
    (ξ : ℝ) (a : Ioi (0 : ℝ))
    (x y r : ℚ) (hr : 0 < r) (C : ℝ≥0∞) : Set Ω :=
  {ω | finiteAroundCoords (normalizedContLFPP ξ a (X ω))
      (centeredRatAnnulus x y r hr) ≤
    C * finiteCircleCoords (normalizedContLFPP ξ a (X ω))
      (centeredInnerCircle x y r hr, centeredOuterCircle x y r hr)}

theorem fullHeatGoodEvent_eq_normalizedGoodEvent
    {Ω : Type} (X : Ω → C(ℂ, ℝ))
    (ξ : ℝ) (a : Ioi (0 : ℝ))
    (x y r : ℚ) (hr : 0 < r) (C : ℝ≥0∞) :
    fullHeatGoodEvent X ξ x y r hr C =
      normalizedGoodEvent X ξ a x y r hr C := by
  ext ω
  have hbad := lfpp_bad_ratio_iff_normalized ξ a (X ω)
    (centeredRatAnnulus x y r hr).toSet
    (centeredInnerCircle x y r hr).toSet
    (centeredOuterCircle x y r hr).toSet C
  have hgood := not_congr hbad
  simpa only [fullHeatGoodEvent, normalizedGoodEvent, mem_setOf_eq,
    finiteAroundCoords, finiteCircleCoords, centeredRatAnnulus, not_lt] using hgood.symm

end SupercriticalLQGUniqueness.B2.DG20Lim
