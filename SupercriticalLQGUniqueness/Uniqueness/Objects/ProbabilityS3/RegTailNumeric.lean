import SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS3.RegGridTail
import SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS1S2.Numeric




 
set_option autoImplicit false
noncomputable section
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS3

theorem s3_tail_numeric (c : ℝ) (hc : 0 ≤ c) (k : ℕ) (hk : 48 ≤ k) :
    (1089 : ℝ≥0∞) * (4 : ℝ≥0∞)^k *
      ENNReal.ofReal (c * Real.exp (-(72 * Real.log 2) * Objects.CorrectedEvent.regK k)) ≤
        (1089 : ℝ≥0∞) * (2 : ℝ≥0∞)^144 * ENNReal.ofReal c *
          ((1/16 : ℝ≥0∞)^k) := by
  have he := Objects.ProbabilityS1S2.regK_exp_tail k hk
  have hreal : (4 : ℝ)^k * Real.exp (-(72 * Real.log 2) * Objects.CorrectedEvent.regK k) ≤
      (2 : ℝ)^144 * (1/16 : ℝ)^k := by
    have hpow : (4 : ℝ)^k * (2 : ℝ)^(-(6:ℝ)*k) = (1/16 : ℝ)^k := by
      have heq : (2 : ℝ)^(-(6:ℝ)*k) = (1/64:ℝ)^k := by
        rw [show (1/64:ℝ) = (2:ℝ)^(-6:ℝ) by norm_num]
        rw [← Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 2) (-6) k]
      rw [heq, mul_comm, ← mul_pow]
      norm_num
    calc
      (4 : ℝ)^k * Real.exp _ ≤ (4 : ℝ)^k * ((2:ℝ)^144 * (2:ℝ)^(-(6:ℝ)*k)) :=
        mul_le_mul_of_nonneg_left he (by positivity)
      _ = (2:ℝ)^144 * ((1/16:ℝ)^k) := by rw [← hpow]; ring
  have hnon : 0 ≤ (4:ℝ)^k := by positivity
  have hexp : 0 ≤ Real.exp (-(72 * Real.log 2) * Objects.CorrectedEvent.regK k) := (Real.exp_pos _).le
  have hr := ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_left hreal hc)
  have hleft : (1089 : ℝ≥0∞) * (4 : ℝ≥0∞)^k *
      ENNReal.ofReal (c * Real.exp (-(72 * Real.log 2) * Objects.CorrectedEvent.regK k)) =
      1089 * ENNReal.ofReal
        (c * ((4:ℝ)^k * Real.exp (-(72 * Real.log 2) * Objects.CorrectedEvent.regK k))) := by
    rw [ENNReal.ofReal_mul hc, ENNReal.ofReal_mul hc,
      ENNReal.ofReal_mul hnon]
    norm_num
    ring_nf
  have hright : ENNReal.ofReal (c * ((2:ℝ)^144 * (1/16:ℝ)^k)) =
      ENNReal.ofReal c * (2:ℝ≥0∞)^144 * (1/16:ℝ≥0∞)^k := by
    rw [ENNReal.ofReal_mul hc, ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (2:ℝ)^144)]
    rw [ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 1/16)]
    rw [show ENNReal.ofReal (1/16:ℝ) = (1/16:ℝ≥0∞) by
      rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ) < 16)]
      norm_num]
    norm_num
    ring
  calc
    _ = 1089 * ENNReal.ofReal
        (c * ((4:ℝ)^k * Real.exp (-(72 * Real.log 2) * Objects.CorrectedEvent.regK k))) := hleft
    _ ≤ 1089 * ENNReal.ofReal (c * ((2:ℝ)^144 * (1/16:ℝ)^k)) :=
      by gcongr
    _ = _ := by rw [hright]; ring

end SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS3
