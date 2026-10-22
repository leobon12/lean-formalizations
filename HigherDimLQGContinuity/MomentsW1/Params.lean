import HigherDimLQGContinuity.MomentsW1.Pointwise

/-! A quantile level above the uniform Peierls threshold. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGContinuity

open HigherDimLFPP HigherDimLQGMetric.DGZ
open scoped ENNReal

theorem wnQuantile_choice {d : ℕ} {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) :
    ∃ ρ : ℝ, 0 < ρ ∧ (∀ y, ρ ≤ ‖y‖ → κ y = 0) ∧
      ∃ q q' : ℝ≥0∞, 0 < q ∧ q < q' ∧ q' < 1 ∧
        (1 + 3 ^ d) * (2 * (d : ℝ≥0∞) * (1 - q)) ≤
          ENNReal.ofReal (2 * 3 ^ d : ℝ)⁻¹ ^
            ((⌈2 * (2 + ρ)⌉₊ + 1) ^ d) := by
  obtain ⟨ρ, hρ0, hρ⟩ := hκ.exists_radius
  let r : ℕ := ⌈2*(2+ρ)⌉₊
  obtain ⟨ht0,ht1⟩ := theta_pow_pos_le_one d r
  obtain ⟨c₄,hc₄1,hc₄⟩ := exists_c4 ht0 ht1 ((1+3^d)*(2*d))
  obtain ⟨q,hc₄q,hq1⟩ := exists_between hc₄1
  obtain ⟨q',hqq',hq'1⟩ := exists_between hq1
  have hq0 : (0:ℝ≥0∞) < q := lt_of_le_of_lt zero_le hc₄q
  refine ⟨ρ,hρ0,hρ,q,q',hq0,hqq',hq'1,?_⟩
  have h := hc₄ q hc₄q
  simpa only [r, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat,
    Nat.cast_pow, mul_assoc] using h

end HigherDimLQGContinuity
