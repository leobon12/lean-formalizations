import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCFinalAlgebra

 
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped ENNReal
namespace SupercriticalLQGUniqueness.B2.DG20Conc

 

theorem laneC_exp_factor_rate
    {ν r : ℝ} (hν : 0 ≤ ν) (hr : 0 ≤ r)
    (K : ℕ) (hK : 1 ≤ K) :
    (ENNReal.ofReal (Real.exp (ν * K) + 1)) ^ r ≤
      ENNReal.ofReal ((2 : ℝ) ^
        ((r * (ν / Real.log 2 + 1)) * (K : ℝ))) := by
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hνK : 0 ≤ ν * (K : ℝ) := mul_nonneg hν (by positivity)
  have hreal : Real.exp (ν * K) + 1 ≤
      (2 : ℝ) ^ ((ν / Real.log 2 + 1) * (K : ℝ)) := by
    calc
      _ ≤ 2 * Real.exp (ν * K) := by
        have h : 1 ≤ Real.exp (ν * K) := by
          simpa using (Real.exp_le_exp.mpr hνK)
        linarith
      _ = Real.exp (Real.log 2 + ν * K) := by
        rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      _ ≤ Real.exp ((Real.log 2 + ν) * K) :=
        Real.exp_le_exp.mpr (by
          have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
          nlinarith)
      _ = _ := by
        rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
        congr 1
        field_simp
        ring
  have hbase := ENNReal.ofReal_le_ofReal hreal
  have hpow := ENNReal.rpow_le_rpow hbase hr
  have htwo : 0 ≤ (2 : ℝ) ^ ((ν / Real.log 2 + 1) * (K : ℝ)) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  rw [ENNReal.ofReal_rpow_of_nonneg htwo hr] at hpow
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)] at hpow
  convert hpow using 1 <;> congr 2 <;> ring

end SupercriticalLQGUniqueness.B2.DG20Conc
