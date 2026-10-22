import HigherDimLQGMetric.ScaleBin.Ratio

/-!
# Summing over the 64-adic lattice

The lattice scales below `εR` are indexed by `J-n`, with `n : ℕ` and
`J = floor(log(εR)/log 64)`. The fourth powers of their ratios form a
geometric series bounded by `2ε⁴`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric.ScaleBin

def topIndex (x : ℝ) : ℤ := ⌊Real.log x / Real.log 64⌋

private theorem log64_pos : 0 < Real.log 64 := Real.log_pos (by norm_num)

/-- Every lattice exponent below `x` lies below the top index. -/
theorem index_le_topIndex {x : ℝ} {j : ℤ}
    (hj : (64 : ℝ) ^ j ≤ x) : j ≤ topIndex x := by
  apply Int.le_floor.mpr
  apply (le_div_iff₀ log64_pos).2
  rw [← Real.log_zpow]
  exact Real.log_le_log (zpow_pos (by norm_num : (0 : ℝ) < 64) j) hj

/-- The top lattice radius does not exceed `x`. -/
theorem zpow_topIndex_le {x : ℝ} (hx : 0 < x) :
    (64 : ℝ) ^ topIndex x ≤ x := by
  apply (Real.log_le_log_iff (zpow_pos (by norm_num : (0 : ℝ) < 64) _) hx).1
  rw [Real.log_zpow]
  have h := Int.floor_le (Real.log x / Real.log 64)
  have h' := (le_div_iff₀ log64_pos).1 h
  exact h'

/-- Reindex all exponents `j ≤ J` by `n = J-j`. -/
theorem exists_nat_index {j J : ℤ} (hj : j ≤ J) :
    ∃ n : ℕ, j = J - n := by
  refine ⟨(J - j).toNat, ?_⟩
  rw [Int.toNat_of_nonneg (sub_nonneg.mpr hj)]
  omega

private theorem scale_pow_sub (J : ℤ) (n : ℕ) :
    (64 : ℝ) ^ (J - n) = (64 : ℝ) ^ J * (1 / 64 : ℝ) ^ n := by
  rw [zpow_sub₀ (by norm_num : (64 : ℝ) ≠ 0), zpow_natCast,
    div_eq_mul_inv, one_div, inv_pow]

theorem scale_four_eq_geom (J : ℤ) (n : ℕ) (R : ℝ) :
    ((64 : ℝ) ^ (J - n) / R) ^ 4 =
      ((64 : ℝ) ^ J / R) ^ 4 * ((1 / 64 : ℝ) ^ 4) ^ n := by
  rw [scale_pow_sub]
  have h : (64 : ℝ) ^ J * (1 / 64 : ℝ) ^ n / R =
      ((64 : ℝ) ^ J / R) * (1 / 64 : ℝ) ^ n := by ring
  rw [h, mul_pow, ← pow_mul, mul_comm n 4, pow_mul]

theorem summable_scale_four (J : ℤ) (R : ℝ) :
    Summable fun n : ℕ => ((64 : ℝ) ^ (J - n) / R) ^ 4 := by
  have hq : Summable fun n : ℕ => ((1 / 64 : ℝ) ^ 4) ^ n :=
    summable_geometric_of_lt_one (by positivity) (by norm_num)
  refine (hq.mul_left (((64 : ℝ) ^ J / R) ^ 4)).congr ?_
  intro n
  exact (scale_four_eq_geom J n R).symm

/-- The sum of fourth powers over the lower lattice scales is at most `2ε⁴`. -/
theorem sum_scale_four_le {ε R : ℝ} (hε : 0 < ε) (hR : 0 < R) :
    (∑' n : ℕ, ((64 : ℝ) ^ (topIndex (ε * R) - n) / R) ^ 4) ≤ 2 * ε ^ 4 := by
  let J := topIndex (ε * R)
  let q : ℝ := (1 / 64 : ℝ) ^ 4
  let A : ℝ := ((64 : ℝ) ^ J / R) ^ 4
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by norm_num [q]
  have hqhalf : (1 - q)⁻¹ ≤ 2 := by norm_num [q]
  have hqInv0 : 0 ≤ (1 - q)⁻¹ := inv_nonneg.mpr (by linarith)
  have htop : (64 : ℝ) ^ J / R ≤ ε := by
    apply (div_le_iff₀ hR).2
    exact zpow_topIndex_le (mul_pos hε hR)
  have hA : A ≤ ε ^ 4 := pow_le_pow_left₀ (by positivity) htop 4
  have hA0 : 0 ≤ A := by positivity
  calc
    (∑' n : ℕ, ((64 : ℝ) ^ (topIndex (ε * R) - n) / R) ^ 4) =
        ∑' n : ℕ, A * q ^ n := by
          congr 1
          funext n
          exact scale_four_eq_geom J n R
    _ = A * (1 - q)⁻¹ := by rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
    _ ≤ ε ^ 4 * (1 - q)⁻¹ := mul_le_mul_of_nonneg_right hA hqInv0
    _ ≤ ε ^ 4 * 2 := mul_le_mul_of_nonneg_left hqhalf (by positivity)
    _ = 2 * ε ^ 4 := by ring

end HigherDimLQGMetric.ScaleBin
