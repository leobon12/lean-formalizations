import HigherDimLQGMetric.Growth.DyadicBlock

/-!
# Dyadic cells for the sphere-average growth argument

The existing `HigherDimLFPP.Osc.grid` supplies a finite grid of controlled cardinality.
This file records the geometry of the small-radius cells and the large-radius blocks.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ}

def l2a_smallScale (k : ℕ) : ℝ := ((2 : ℝ) ^ k)⁻¹

theorem l2a_smallScale_pos (k : ℕ) : 0 < l2a_smallScale k := by
  unfold l2a_smallScale
  positivity

theorem l2a_smallScale_eq_zpow (k : ℕ) :
    l2a_smallScale k = (2 : ℝ) ^ (-(k : ℤ)) := by
  simp only [l2a_smallScale, zpow_neg, zpow_natCast]

theorem l2a_smallScale_eq_half_pow (k : ℕ) :
    l2a_smallScale k = (1 / 2 : ℝ) ^ k := by
  rw [l2a_smallScale, ← inv_pow]
  norm_num

theorem l2a_closedBall_subset_box {R : ℝ} {z : Rd d}
    (hz : z ∈ closedBall (0 : Rd d) R) : z ∈ HigherDimLFPP.Osc.box 0 R := by
  intro i
  have hi := PiLp.norm_apply_le z i
  have hR : ‖z‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hz
  simpa only [PiLp.zero_apply, sub_zero, Real.norm_eq_abs] using hi.trans hR

theorem l2a_gridOf_mem {R a : ℝ} (ha : 0 < a) {z : Rd d}
    (hz : z ∈ closedBall (0 : Rd d) R) :
    HigherDimLFPP.Osc.gridOf 0 R a z ∈ HigherDimLFPP.Osc.grid 0 R a :=
  HigherDimLFPP.Osc.gridOf_mem_grid 0 ha (l2a_closedBall_subset_box hz)

theorem l2a_gridOf_dist_le {R a : ℝ} (ha : 0 < a) {z : Rd d}
    (hz : z ∈ closedBall (0 : Rd d) R) :
    ‖z - HigherDimLFPP.Osc.gridOf 0 R a z‖ ≤ Real.sqrt (d : ℝ) * a :=
  HigherDimLFPP.Osc.norm_sub_gridOf_le 0 ha (l2a_closedBall_subset_box hz)

theorem l2a_small_cell {R a r : ℝ} (ha : 0 < a) (hrlo : a / 2 ≤ r) (hrhi : r ≤ a)
    {z : Rd d} (hz : z ∈ closedBall (0 : Rd d) R) :
    let g := HigherDimLFPP.Osc.gridOf 0 R a z
    let p : ℝ × Rd d := (r / a, a⁻¹ • (z - g))
    p ∈ Icc (1 / 2 : ℝ) 1 ×ˢ closedBall (0 : Rd d) (Real.sqrt (d : ℝ)) ∧
      a * p.1 = r ∧ a • p.2 + g = z := by
  dsimp
  have hslo : (1 / 2 : ℝ) ≤ r / a := by
    rw [le_div_iff₀ ha]
    linarith
  have hshi : r / a ≤ 1 := (div_le_one ha).2 hrhi
  have hnorm := l2a_gridOf_dist_le ha hz
  have hscaled : ‖a⁻¹ • (z - HigherDimLFPP.Osc.gridOf 0 R a z)‖ ≤ Real.sqrt (d : ℝ) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 ha)]
    rw [inv_mul_le_iff₀ ha]
    simpa only [mul_comm] using hnorm
  refine ⟨⟨⟨hslo, hshi⟩, ?_⟩, ?_, ?_⟩
  · simpa only [mem_closedBall, dist_zero_right] using hscaled
  · exact mul_div_cancel₀ r ha.ne'
  · rw [smul_smul, mul_inv_cancel₀ ha.ne', one_smul, sub_add_cancel]

theorem l2a_large_cell {R a r : ℝ} (ha : 0 < a) (ha1 : 1 ≤ a)
    (hrlo : a / 2 ≤ r) (hrhi : r ≤ a) {z : Rd d}
    (hz : z ∈ closedBall (0 : Rd d) R) :
    let p : ℝ × Rd d := (r / a, a⁻¹ • z)
    p ∈ Icc (1 / 2 : ℝ) 1 ×ˢ closedBall (0 : Rd d) R ∧
      a * p.1 = r ∧ a • p.2 = z := by
  dsimp
  have hslo : (1 / 2 : ℝ) ≤ r / a := by
    rw [le_div_iff₀ ha]
    linarith
  have hshi : r / a ≤ 1 := (div_le_one ha).2 hrhi
  have hnorm : ‖z‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hz
  have hscaled : ‖a⁻¹ • z‖ ≤ R := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 ha)]
    calc a⁻¹ * ‖z‖ ≤ a⁻¹ * R := mul_le_mul_of_nonneg_left hnorm (inv_nonneg.2 ha.le)
      _ ≤ R := by
        have hR : 0 ≤ R := (norm_nonneg z).trans hnorm
        have hinv : a⁻¹ ≤ 1 := (inv_le_one₀ ha).2 ha1
        nlinarith
  refine ⟨⟨⟨hslo, hshi⟩, ?_⟩, ?_, ?_⟩
  · simpa only [mem_closedBall, dist_zero_right] using hscaled
  · exact mul_div_cancel₀ r ha.ne'
  · rw [smul_smul, mul_inv_cancel₀ ha.ne', one_smul]

end HigherDimLQGMetric
