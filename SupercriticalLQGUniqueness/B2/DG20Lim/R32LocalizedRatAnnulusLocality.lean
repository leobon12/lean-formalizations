import SupercriticalLQGUniqueness.B2.DG20Lim.R32RationalGoodAnnulusRatio
import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalizedLFPP

 



set_option autoImplicit false
noncomputable section

open Set Metric
open LQGMetric LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.DG20Lim

 

def bufferedCenteredAnnulusR32 (x y r : ℚ) : TopologicalSpace.Opens ℂ :=
  ⟨{w | (r : ℝ) / 2 < ‖w - Complex.mk (x : ℝ) (y : ℝ)‖ ∧
      ‖w - Complex.mk (x : ℝ) (y : ℝ)‖ < 4 * (r : ℝ)}, by
    exact (isOpen_lt continuous_const (continuous_id.sub continuous_const).norm).inter
      (isOpen_lt (continuous_id.sub continuous_const).norm continuous_const)⟩

theorem centeredRatAnnulus_locSupportR32
    (x y r : ℚ) (hr : 0 < r) (ε : Ioi (0 : ℝ))
    (hεr : Real.sqrt (ε : ℝ) < (r : ℝ) / 2) :
    ∀ z ∈ (centeredRatAnnulusR32 x y r hr).toSet,
      closedBall z (Real.sqrt (ε : ℝ)) ⊆ bufferedCenteredAnnulusR32 x y r := by
  intro z hz w hw
  rw [centeredRatAnnulus_eq_closedAnnR32] at hz
  let c : ℂ := Complex.mk (x : ℝ) (y : ℝ)
  have hzw : ‖w - z‖ ≤ Real.sqrt (ε : ℝ) := by
    simpa only [mem_closedBall, dist_eq_norm] using hw
  have h1 : ‖z - c‖ ≤ ‖z - w‖ + ‖w - c‖ := by
    calc ‖z - c‖ = ‖(z - w) + (w - c)‖ := by ring
      _ ≤ _ := norm_add_le _ _
  have h2 : ‖w - c‖ ≤ ‖w - z‖ + ‖z - c‖ := by
    calc ‖w - c‖ = ‖(w - z) + (z - c)‖ := by ring
      _ ≤ _ := norm_add_le _ _
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hzw' : ‖z - w‖ ≤ Real.sqrt (ε : ℝ) := by
    simpa only [norm_sub_rev] using hzw
  exact ⟨by change (r : ℝ) / 2 < ‖w - c‖; linarith [hz.1],
    by change ‖w - c‖ < 4 * (r : ℝ); linarith [hz.2]⟩

 

theorem localizedLFPP_centeredRatAnnulus_congrR32
    (ξ ε : Ioi (0 : ℝ)) (x y r : ℚ) (hr : 0 < r)
    (hεr : Real.sqrt (ε : ℝ) < (r : ℝ) / 2)
    {g g' : DistC}
    (he : restrictTo (bufferedCenteredAnnulusR32 x y r) g =
      restrictTo (bufferedCenteredAnnulusR32 x y r) g')
    (z w : ℂ) :
    lfppLocOn (ξ : ℝ) (ε : ℝ) ε.property g
        (centeredRatAnnulusR32 x y r hr).toSet z w =
      lfppLocOn (ξ : ℝ) (ε : ℝ) ε.property g'
        (centeredRatAnnulusR32 x y r hr).toSet z w := by
  exact B2.PfeAxioms.localizedLFPP_congr ξ ε
    (centeredRatAnnulusR32 x y r hr).toSet (bufferedCenteredAnnulusR32 x y r)
    (centeredRatAnnulus_locSupportR32 x y r hr ε hεr) he z w

end SupercriticalLQGUniqueness.B2.DG20Lim
