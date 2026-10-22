import HigherDimLQGMetric.ConvField.ParamTest
import HigherDimLQGMetric.Growth.Main

/-! The logarithmic sphere-average growth remains bounded after polar weighting on bounded radii. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace HigherDimLQGMetric

variable {d : ℕ}

theorem l2b_polar_log_weight_bounded (hd : 2 ≤ d)
    {R r : ℝ} (hR : 1 ≤ R) (hr : 0 < r) (hrR : r ≤ R) :
    r ^ (d - 1) *
      max (Real.log r⁻¹)
        (max ((max (Real.log r) 0) ^ (1 / 2 + 1 / 2 : ℝ)) 1) ≤
      R ^ (d - 1) * max (Real.log R) 1 + 1 := by
  have hp : 1 ≤ d - 1 := by omega
  have hR0 : 0 ≤ R := by linarith
  have hpow0 : 0 ≤ r ^ (d - 1) := pow_nonneg hr.le _
  have hpowR0 : 0 ≤ R ^ (d - 1) := pow_nonneg hR0 _
  by_cases hr1 : r ≤ 1
  · have hlog : Real.log r ≤ 0 := Real.log_nonpos hr.le hr1
    have hloginv : 0 ≤ Real.log r⁻¹ := by rw [Real.log_inv]; linarith
    have hsmall : r * Real.log r⁻¹ ≤ 1 := by
      have hle := Real.log_le_sub_one_of_pos (inv_pos.2 hr)
      have hle' : Real.log r⁻¹ ≤ r⁻¹ := by linarith
      have hm := mul_le_mul_of_nonneg_left hle' hr.le
      simpa [mul_comm, mul_inv_cancel₀ hr.ne'] using hm
    have hpowr : r ^ (d - 1) ≤ r := by
      simpa only [pow_one] using
        (pow_le_pow_of_le_one hr.le hr1 hp : r ^ (d - 1) ≤ r ^ 1)
    have hterm : r ^ (d - 1) * Real.log r⁻¹ ≤ 1 :=
      (mul_le_mul_of_nonneg_right hpowr hloginv).trans hsmall
    have hpow1 : r ^ (d - 1) ≤ 1 := hpowr.trans hr1
    rw [max_eq_right hlog, Real.zero_rpow (by norm_num : (1 / 2 + 1 / 2 : ℝ) ≠ 0),
      max_eq_right zero_le_one]
    have hmax : r ^ (d - 1) * max (Real.log r⁻¹) 1 ≤ 1 := by
      rw [mul_max_of_nonneg (Real.log r⁻¹) 1 hpow0]
      exact max_le hterm (by simpa using hpow1)
    have hRprod : 0 ≤ R ^ (d - 1) * max (Real.log R) 1 := by positivity
    linarith
  · have hr1' : 1 ≤ r := le_of_not_ge hr1
    have hlog : 0 ≤ Real.log r := Real.log_nonneg hr1'
    have hloginv : Real.log r⁻¹ ≤ 0 := by rw [Real.log_inv]; linarith
    have hlogR : Real.log r ≤ Real.log R := Real.log_le_log hr hrR
    have hpowR : r ^ (d - 1) ≤ R ^ (d - 1) := pow_le_pow_left₀ hr.le hrR _
    rw [max_eq_left hlog, show (1 / 2 + 1 / 2 : ℝ) = 1 by ring, Real.rpow_one,
      max_eq_right (by
        have := le_max_right (Real.log r) 1
        linarith : Real.log r⁻¹ ≤ max (Real.log r) 1)]
    have hmax : max (Real.log r) 1 ≤ max (Real.log R) 1 :=
      max_le_max hlogR le_rfl
    have hmain : r ^ (d - 1) * max (Real.log r) 1 ≤
        R ^ (d - 1) * max (Real.log R) 1 :=
      mul_le_mul hpowR hmax (by positivity) hpowR0
    linarith

end HigherDimLQGMetric
