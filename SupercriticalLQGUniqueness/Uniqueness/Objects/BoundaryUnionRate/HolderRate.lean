import SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionRate.AnnulusHolder




 


set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionRate

theorem rpow_mul_exp_log_inv (b A B C : ℝ) (hb : 0 < b) :
    b ^ A * Real.exp (B * (Real.log b⁻¹ + C)) =
      b ^ (A - B) * Real.exp (B * C) := by
  rw [Real.rpow_def_of_pos hb, Real.rpow_def_of_pos hb, Real.log_inv]
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

theorem ennreal_scale_gauss_rate (b A B C q : ℝ)
    (hb : 0 < b) (hq : 0 < q) :
    ENNReal.ofReal (b ^ A) *
        ENNReal.ofReal (Real.exp (q * B * (Real.log b⁻¹ + C))) ^ (1 / q) =
      ENNReal.ofReal (b ^ (A - B)) *
        ENNReal.ofReal (Real.exp (B * C)) := by
  rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (by positivity : 0 ≤ 1 / q)]
  rw [← Real.exp_mul]
  have he : (q * B * (Real.log b⁻¹ + C)) * (1 / q) =
      B * (Real.log b⁻¹ + C) := by
    field_simp
  rw [he, ← ENNReal.ofReal_mul (Real.rpow_nonneg hb.le _)]
  rw [rpow_mul_exp_log_inv b A B C hb]
  rw [ENNReal.ofReal_mul (Real.rpow_nonneg hb.le _)]

theorem annulus_rate_identity
    (a s ξ Q p q : ℝ) (ha : 0 < a) (hs : 0 < s)
    (hp : 0 < p) (hq : 0 < q) :
    ENNReal.ofReal ((a / s) ^ (ξ * Q)) ^ p *
        ENNReal.ofReal
          (Real.exp ((p * q * ξ) ^ 2 *
            (Real.log (s / a) + 2 * Real.log (1 + 1)) / 2)) ^ (1 / q) =
      ENNReal.ofReal ((a / s) ^ (ξ * Q * p - q * p ^ 2 * ξ ^ 2 / 2)) *
        ENNReal.ofReal (Real.exp (q * p ^ 2 * ξ ^ 2 * Real.log (1 + 1))) := by
  have hb : 0 < a / s := div_pos ha hs
  have hInv : (a / s)⁻¹ = s / a := by
    field_simp
  have hScale : ENNReal.ofReal ((a / s) ^ (ξ * Q)) ^ p =
      ENNReal.ofReal ((a / s) ^ (ξ * Q * p)) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hb.le _) hp.le,
      ← Real.rpow_mul hb.le]
  have hExp : (p * q * ξ) ^ 2 *
      (Real.log (s / a) + 2 * Real.log (1 + 1)) / 2 =
      (q * (q * p ^ 2 * ξ ^ 2 / 2)) *
      (Real.log (a / s)⁻¹ + 2 * Real.log (1 + 1)) := by
    rw [hInv]
    ring_nf
  rw [hScale, hExp]
  have h := ennreal_scale_gauss_rate (a / s) (ξ * Q * p)
    (q * p ^ 2 * ξ ^ 2 / 2) (2 * Real.log (1 + 1)) q hb hq
  convert h using 1
  all_goals (congr 1; ring_nf)


end SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionRate
