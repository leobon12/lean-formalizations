import SupercriticalLQGUniqueness.Uniqueness.EndSaving.C45.GridAsymptotic




set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.C45

theorem grid_budget_le_power
    {ε μ c₁ B : ℝ} {k J : ℕ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hB : 0 ≤ B)
    (hexp : μ + 1 / 2 ≤ c₁ * k)
    (hgrid : (J : ℝ) ≤ (ε⁻¹) ^ (1 / 2 : ℝ)) :
    (J : ℝ≥0∞) *
        (ENNReal.ofReal B / ENNReal.ofReal (ε ^ (-(c₁ * k)))) ≤
      ENNReal.ofReal (B * ε ^ μ) := by
  have hJpow : (J : ℝ) ≤ ε ^ (-(1 / 2 : ℝ)) := by
    simpa only [Real.rpow_neg hε.le, ← Real.inv_rpow hε.le] using hgrid
  have hpow : ε ^ (-(1 / 2 : ℝ)) ≤ ε ^ (μ - c₁ * k) :=
    Real.rpow_le_rpow_of_exponent_ge hε hε1 (by linarith)
  have hprod : ε ^ μ * ε ^ (-(c₁ * k)) = ε ^ (μ - c₁ * k) := by
    rw [← Real.rpow_add hε]
    congr 1
  have hJN : (J : ℝ) ≤ ε ^ μ * ε ^ (-(c₁ * k)) := by
    rw [hprod]
    exact hJpow.trans hpow
  have hNpos : 0 < ε ^ (-(c₁ * k)) := Real.rpow_pos_of_pos hε _
  have hreal : (J : ℝ) * (B / ε ^ (-(c₁ * k))) ≤ B * ε ^ μ := by
    rw [← mul_div_assoc, div_le_iff₀ hNpos]
    have hm := mul_le_mul_of_nonneg_right hJN hB
    nlinarith [hm]
  have hrealNN :
      ENNReal.ofReal ((J : ℝ) * (B / ε ^ (-(c₁ * k)))) ≤
        ENNReal.ofReal (B * ε ^ μ) := ENNReal.ofReal_le_ofReal hreal
  convert hrealNN using 1
  rw [ENNReal.ofReal_mul (Nat.cast_nonneg J),
    ENNReal.ofReal_natCast, ENNReal.ofReal_div_of_pos hNpos]

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.C45
