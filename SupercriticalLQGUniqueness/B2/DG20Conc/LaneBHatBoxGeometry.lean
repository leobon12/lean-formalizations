import SupercriticalLQGUniqueness.B2.DG20Conc.J1OscExtended
import SupercriticalLQGUniqueness.B2.DG20Conc.LaneBSourceIdxVisited

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Metric

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise

theorem laneB_hatBox_subset_center_ball (K : ℕ) (b : ℤ × ℤ) :
    T20D.hatBox K b ⊆ closedBall (T20.dyCenter K b)
      (3 * (2 : ℝ)⁻¹ ^ K) := by
  intro x hx
  have hr : 0 ≤ (2 : ℝ)⁻¹ ^ K := by positivity
  simp only [T20D.hatBox, Complex.mem_reProdIm, mem_Icc] at hx
  rw [mem_closedBall, dist_eq_norm]
  have hre : |(x - T20.dyCenter K b).re| ≤ (3 / 2 : ℝ) * (2 : ℝ)⁻¹ ^ K := by
    rw [Complex.sub_re, abs_le]
    dsimp [T20.dyCenter]
    constructor <;> nlinarith [hx.1.1, hx.1.2]
  have him : |(x - T20.dyCenter K b).im| ≤ (3 / 2 : ℝ) * (2 : ℝ)⁻¹ ^ K := by
    rw [Complex.sub_im, abs_le]
    dsimp [T20.dyCenter]
    constructor <;> nlinarith [hx.2.1, hx.2.2]
  exact (Complex.norm_le_abs_re_add_abs_im _).trans (by linarith)

 
theorem laneB_source_hatBox_subset_bigBox
    (Q : PsiParams) {K : ℕ} (hK : 6 ≤ K)
    {b : ℤ × ℤ} (hb : b ∈ j1SourceIdx K (j1SourceRadius Q K)) :
    T20D.hatBox K b ⊆ T20D.bigBox := by
  have hcenter : T20.dyCenter K b ∈ j1NearbyBox :=
    j1_nearbyIdx_center (j1_sourceIdx_subset_nearbyIdx K (j1SourceRadius Q K) hb)
  have hr : 3 * (2 : ℝ)⁻¹ ^ K ≤ 1 := by
    have hp : (2 : ℝ)⁻¹ ^ K ≤ (2 : ℝ)⁻¹ ^ 2 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    norm_num at hp
    linarith
  exact (laneB_hatBox_subset_center_ball K b).trans
    (j1_closedBall_nearby_subset_bigBox hcenter hr)

end SupercriticalLQGUniqueness.B2.DG20Conc
