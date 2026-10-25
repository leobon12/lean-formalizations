import SupercriticalLQGUniqueness.B2.DG20Lim.R32FullGoodIterationEventual
import SupercriticalLQGUniqueness.B2.DG20Lim.GoodAnnulusNormalize

 



set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal
open LQGMetric LQGMetric.LFPP LQGMetric.Blueprint

namespace SupercriticalLQGUniqueness.B2.DG20Lim

def normalizedGoodEventR32 {Ω : Type} (X : Ω → C(ℂ, ℝ))
    (ξ : ℝ) (a : Ioi (0 : ℝ))
    (x y r : ℚ) (hr : 0 < r) (C : ℝ≥0∞) : Set Ω :=
  {ω | finiteAroundCoords (normalizedContLFPP ξ a (X ω))
      (centeredRatAnnulusR32 x y r hr) ≤
    C * finiteCircleCoords (normalizedContLFPP ξ a (X ω))
      (centeredInnerCircleR32 x y r hr, centeredOuterCircleR32 x y r hr)}

theorem fullHeatGoodEvent_eq_normalizedGoodEventR32
    {Ω : Type} (X : Ω → C(ℂ, ℝ))
    (ξ : ℝ) (a : Ioi (0 : ℝ))
    (x y r : ℚ) (hr : 0 < r) (C : ℝ≥0∞) :
    fullHeatGoodEventR32 X ξ x y r hr C =
      normalizedGoodEventR32 X ξ a x y r hr C := by
  ext ω
  have hbad := lfpp_bad_ratio_iff_normalized ξ a (X ω)
    (centeredRatAnnulusR32 x y r hr).toSet
    (centeredInnerCircleR32 x y r hr).toSet
    (centeredOuterCircleR32 x y r hr).toSet C
  have hgood := not_congr hbad
  simpa only [fullHeatGoodEventR32, normalizedGoodEventR32, mem_setOf_eq,
    finiteAroundCoords, finiteCircleCoords, centeredRatAnnulusR32, not_lt] using hgood.symm

end SupercriticalLQGUniqueness.B2.DG20Lim
