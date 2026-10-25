import SupercriticalLQGUniqueness.B2.DG20Lim.R32UnitAnnulusCoords
import SupercriticalLQGUniqueness.B2.DG20Lim.R32UnitGoodAnnulusRatio
import SupercriticalLQGUniqueness.B2.DG20Lim.R32ScaledGoodAnnulusRatio
import SupercriticalLQGUniqueness.B2.DG20Lim.R32TranslatedGoodAnnulusRatio
import SupercriticalLQGUniqueness.B2.DG20Lim.R32UniformGoodAnnulusRatio
import SupercriticalLQGUniqueness.B2.DG20Lim.R32RationalAnnulusAffine
import SupercriticalLQGUniqueness.B2.DG20Lim.R32RationalGoodAnnulusRatio
import SupercriticalLQGUniqueness.B2.DG20Lim.R32LocalizedRatAnnulusLocality
import SupercriticalLQGUniqueness.B2.DG20Lim.R32RationalGoodSequence
import SupercriticalLQGUniqueness.B2.DG20Lim.R32GoodAnnulusCoupledLimit
import SupercriticalLQGUniqueness.B2.DG20Lim.R32LocalizedMollifierSigma
import SupercriticalLQGUniqueness.B2.DG20Lim.FiniteAnnulusInternalCompare

 




set_option autoImplicit false
noncomputable section

open Set Metric

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem centered_shell_subset_bufferedR32
    (x y r : ℚ) (hr : 0 < r) (w : ℂ)
    (hinner : (r : ℝ) ≤ ‖w - Complex.mk (x : ℝ) (y : ℝ)‖)
    (houter : ‖w - Complex.mk (x : ℝ) (y : ℝ)‖ ≤ 3 / 2 * (r : ℝ)) :
    w ∈ bufferedCenteredAnnulusR32 x y r := by
  change (r : ℝ) / 2 < ‖w - Complex.mk (x : ℝ) (y : ℝ)‖ ∧
    ‖w - Complex.mk (x : ℝ) (y : ℝ)‖ < 4 * (r : ℝ)
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  constructor <;> linarith

theorem centeredRatAnnulus_subset_bufferedR32
    (x y r : ℚ) (hr : 0 < r) :
    (centeredRatAnnulusR32 x y r hr).toSet ⊆ bufferedCenteredAnnulusR32 x y r := by
  intro w hw
  rw [centeredRatAnnulus_eq_closedAnnR32] at hw
  exact centered_shell_subset_bufferedR32 x y r hr w hw.1 hw.2

end SupercriticalLQGUniqueness.B2.DG20Lim
