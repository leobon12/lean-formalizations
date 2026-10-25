import SupercriticalLQGUniqueness.Uniqueness.Objects.Shield.ShieldBump




 



set_option autoImplicit false

noncomputable section

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Shield

def shieldK0 (ξ C₁ lam : ℝ) : ℝ :=
  max 0 (Real.log (C₁ ^ 2 / lam)) / ξ

theorem shieldK0_nonneg {ξ C₁ lam : ℝ} (hξ : 0 < ξ) :
    0 ≤ shieldK0 ξ C₁ lam := by
  unfold shieldK0
  exact div_nonneg (le_max_left _ _) hξ.le

theorem shieldK0_budget {ξ C₁ lam : ℝ}
    (hξ : 0 < ξ) (hC : 0 < C₁) (hlam : 0 < lam) :
    Real.exp (ξ * -(shieldK0 ξ C₁ lam)) * C₁ ^ 2 ≤ lam := by
  have hC2 : 0 < C₁ ^ 2 := sq_pos_of_pos hC
  have hx : 0 < C₁ ^ 2 / lam := div_pos hC2 hlam
  have heq : ξ * shieldK0 ξ C₁ lam = max 0 (Real.log (C₁ ^ 2 / lam)) := by
    unfold shieldK0
    field_simp
  have hexp : Real.exp (ξ * -(shieldK0 ξ C₁ lam)) ≤ lam / C₁ ^ 2 := by
    have hmon := Real.exp_le_exp.mpr
      (neg_le_neg (le_max_right 0 (Real.log (C₁ ^ 2 / lam))))
    have hident : Real.exp (-Real.log (C₁ ^ 2 / lam)) = (C₁ ^ 2 / lam)⁻¹ := by
      rw [Real.exp_neg, Real.exp_log hx]
    rw [hident] at hmon
    have hinv : (C₁ ^ 2 / lam)⁻¹ = lam / C₁ ^ 2 := by field_simp
    rw [mul_neg, heq]
    rwa [hinv] at hmon
  have hmul := mul_le_mul_of_nonneg_right hexp hC2.le
  have hid : lam / C₁ ^ 2 * C₁ ^ 2 = lam := by field_simp
  rw [hid] at hmul
  exact hmul

end SupercriticalLQGUniqueness.Uniqueness.Objects.Shield
