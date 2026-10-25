import SupercriticalLQGUniqueness.B2.DG20Conc.J1OscExtended
import SupercriticalLQGUniqueness.B2.DG20Conc.LaneBInSquareWeightedCost

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Metric

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF

theorem laneB_blkIdx_center_nearby {K : ℕ} (hK : 2 ≤ K)
    {b : ℤ × ℤ} (hb : b ∈ T20.blkIdx K) :
    T20.dyCenter K b ∈ j1NearbyBox := by
  simp only [T20.blkIdx, Finset.mem_product, Finset.mem_Icc] at hb
  simp only [T20.dyCenter, j1NearbyBox, Complex.mem_reProdIm, mem_Icc]
  have hp : (0 : ℝ) < (2 : ℝ)⁻¹ ^ K := by positivity
  have he : (2 : ℝ) ^ K * (2 : ℝ)⁻¹ ^ K = 1 := by
    rw [← mul_pow]
    norm_num
  have hr : (2 : ℝ)⁻¹ ^ K ≤ 1 := by
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have hb1 : (-1 : ℝ) ≤ b.1 ∧ (b.1 : ℝ) ≤ (2 : ℝ)^K := by
    exact_mod_cast hb.1
  have hb2 : (-1 : ℝ) ≤ b.2 ∧ (b.2 : ℝ) ≤ (2 : ℝ)^K := by
    exact_mod_cast hb.2
  constructor <;> constructor <;> nlinarith

theorem laneB_glueBox_subset_center_ball {K : ℕ} (hK : 2 ≤ K)
    {b : ℤ × ℤ} (hb : b ∈ T20.blkIdx K) :
    S6U.glueBox K b ⊆
      closedBall (T20.dyCenter K b) (7 * (2 : ℝ)⁻¹ ^ K) := by
  intro x hx
  have h := (S6U.glueBox_near hK hb hx).2
  simpa only [mem_closedBall, dist_eq_norm] using h

end SupercriticalLQGUniqueness.B2.DG20Conc
