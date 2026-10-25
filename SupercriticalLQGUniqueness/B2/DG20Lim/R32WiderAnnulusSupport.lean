import SupercriticalLQGUniqueness.B2.DG20Lim.R32LocalizedGoodCostCompare
import SupercriticalLQGUniqueness.B2.DG20Lim.R32LocalizedGoodHeatCompare
import SupercriticalLQGUniqueness.B2.DG20Lim.R32LocalizedGoodEventualCompare
import SupercriticalLQGUniqueness.B2.DG20Lim.R32LocalizedGoodSequenceTransfer
import SupercriticalLQGUniqueness.B2.DG20Lim.R32FullHeatGoodSequence
import SupercriticalLQGUniqueness.B2.DG20Lim.R32LocalizedGoodProbability
import SupercriticalLQGUniqueness.B2.DG20Lim.LocalizedGoodShift
import SupercriticalLQGUniqueness.B2.DG20Lim.R32RationalAnnulusBuffer

 




set_option autoImplicit false
noncomputable section

open Set Metric
open LQGMetric LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.DG20Lim

def widerCenteredAnnulusR32 (x y r : ℚ) : TopologicalSpace.Opens ℂ :=
  ⟨{w | (r : ℝ) / 4 < ‖w - Complex.mk (x : ℝ) (y : ℝ)‖ ∧
      ‖w - Complex.mk (x : ℝ) (y : ℝ)‖ < 8 * (r : ℝ)}, by
    exact (isOpen_lt continuous_const (continuous_id.sub continuous_const).norm).inter
      (isOpen_lt (continuous_id.sub continuous_const).norm continuous_const)⟩

theorem bufferedCenteredAnnulus_locSupport_widerR32
    (x y r : ℚ) (hr : 0 < r) (ε : Ioi (0 : ℝ))
    (hεr : Real.sqrt (ε : ℝ) < (r : ℝ) / 4) :
    ∀ z ∈ bufferedCenteredAnnulusR32 x y r,
      closedBall z (Real.sqrt (ε : ℝ)) ⊆ widerCenteredAnnulusR32 x y r := by
  intro z hz w hw
  let c : ℂ := Complex.mk (x : ℝ) (y : ℝ)
  have hzw : ‖w - z‖ ≤ Real.sqrt (ε : ℝ) := by
    simpa only [mem_closedBall, dist_eq_norm] using hw
  have h1 : ‖z - c‖ ≤ ‖z - w‖ + ‖w - c‖ := by
    calc ‖z - c‖ = ‖(z - w) + (w - c)‖ := by ring
      _ ≤ _ := norm_add_le _ _
  have h2 : ‖w - c‖ ≤ ‖w - z‖ + ‖z - c‖ := by
    calc ‖w - c‖ = ‖(w - z) + (z - c)‖ := by ring
      _ ≤ _ := norm_add_le _ _
  have hzw' : ‖z - w‖ ≤ Real.sqrt (ε : ℝ) := by
    simpa only [norm_sub_rev] using hzw
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  exact ⟨by change (r : ℝ) / 4 < ‖w - c‖; linarith [hz.1],
    by change ‖w - c‖ < 8 * (r : ℝ); linarith [hz.2]⟩

theorem localizedLFPP_buffered_congrR32
    (ξ : ℝ) (ε : Ioi (0 : ℝ))
    (x y r : ℚ) (hr : 0 < r)
    (hεr : Real.sqrt (ε : ℝ) < (r : ℝ) / 4)
    {g g' : DistC}
    (he : restrictTo (widerCenteredAnnulusR32 x y r) g =
      restrictTo (widerCenteredAnnulusR32 x y r) g')
    (z w : ℂ) :
    lfppLocOn ξ (ε : ℝ) ε.property g (bufferedCenteredAnnulusR32 x y r) z w =
      lfppLocOn ξ (ε : ℝ) ε.property g' (bufferedCenteredAnnulusR32 x y r) z w := by
  unfold lfppLocOn
  apply lfppDOn_congr
  intro v hv
  unfold locMollify
  exact LQGMetric.DFGPS.L217.apply_eq_of_restrictTo_eq he _
    ((tsupport_locTest_subset (ε : ℝ) ε.property v).trans
      (bufferedCenteredAnnulus_locSupport_widerR32 x y r hr ε hεr v hv))

end SupercriticalLQGUniqueness.B2.DG20Lim
