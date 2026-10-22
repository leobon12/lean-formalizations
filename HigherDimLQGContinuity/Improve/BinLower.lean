import HigherDimLQGContinuity.Improve.Class

/-!
# Lower edge of the finite dyadic bin family
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HigherDimLQGContinuity

open HigherDimLQGMetric

/-- The extra lower endpoint bin in the finite bin family can be a factor
four below its nominal lower unit. -/
theorem q11_bin_lower_all {lo hi : ℝ} (hlo : 0 < lo)
    {i : ℤ} (hi : i ∈ s7b_binIndices lo hi) :
    lo / 4 ≤ (2 : ℝ) ^ i := by
  have hindex : Int.floor (Real.logb 2 lo) - 1 ≤ i :=
    (Finset.mem_Icc.mp hi).1
  let q : ℤ := Int.floor (Real.logb 2 lo)
  have hlog : Real.logb 2 lo ≤ (q : ℝ) + 1 :=
    (Int.lt_floor_add_one _).le
  have hloPow : lo ≤ (2 : ℝ) ^ ((q : ℝ) + 1) :=
    (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) hlo).mp hlog
  have hpowEq : (2 : ℝ) ^ ((q : ℝ) + 1) = 4 * (2 : ℝ) ^ (q - 1) := by
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_intCast,
      Real.rpow_one]
    have hq : (2 : ℝ) ^ q = 2 * (2 : ℝ) ^ (q - 1) := by
      calc
        (2 : ℝ) ^ q = (2 : ℝ) ^ ((q - 1) + 1) := by congr 1; omega
        _ = 2 * (2 : ℝ) ^ (q - 1) := by
          rw [zpow_add_one₀ (by norm_num : (2 : ℝ) ≠ 0)]
          ring
    rw [hq]
    ring
  have hmon : (2 : ℝ) ^ (q - 1) ≤ (2 : ℝ) ^ i :=
    zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hindex
  rw [hpowEq] at hloPow
  nlinarith only [hloPow, hmon]

end HigherDimLQGContinuity
