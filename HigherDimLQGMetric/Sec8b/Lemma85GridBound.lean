import HigherDimLQGMetric.Sharp.GridCount

/-! Polynomial count for lattice centres at mesoscopic scales. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- The same grid cardinal bound as the source's `C_d ε^{-2d}` estimate,
with the geometric constant displayed explicitly. -/
theorem s7b_scale_grid_bound (d : ℕ) (hd : 1 ≤ d)
    {ε R r : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hR : 0 < R) (hrlo : ε ^ 2 * R ≤ r) :
    ((shellGridBox d (⌈5 * R / (r / (100 * d))⌉₊ + 1)
      (r / (100 * d))).card : ℝ) ≤
        ((1000 * d + 5 : ℝ) * (ε⁻¹) ^ (2 : ℕ)) ^ d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hr : 0 < r := lt_of_lt_of_le (mul_pos (pow_pos hε _) hR) hrlo
  let s : ℝ := r / (100 * d)
  have hs : 0 < s := by dsimp [s]; positivity
  let N : ℕ := ⌈5 * R / s⌉₊ + 1
  have hceil : (⌈5 * R / s⌉₊ : ℝ) < 5 * R / s + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hratio : 5 * R / s ≤ 500 * (d : ℝ) * (ε⁻¹) ^ (2 : ℕ) := by
    have hε2 : 0 < ε ^ 2 := pow_pos hε _
    have heq : (ε⁻¹) ^ (2 : ℕ) = (ε ^ 2)⁻¹ := by ring
    rw [heq]
    have hbound : 5 * R / s ≤ 500 * (d : ℝ) / ε ^ 2 := by
      apply (div_le_div_iff₀ hs hε2).mpr
      have hcore : 5 * R * ε ^ 2 ≤ 5 * r := by nlinarith only [hrlo]
      have hsEq : 500 * (d : ℝ) * s = 5 * r := by
        dsimp [s]
        field_simp
        ring
      nlinarith only [hcore, hsEq]
    simpa only [div_eq_mul_inv] using hbound
  have hinv : 1 ≤ (ε⁻¹) ^ (2 : ℕ) := by
    have h : 1 ≤ ε⁻¹ := one_le_inv_iff₀.mpr ⟨hε, hε1⟩
    exact one_le_pow₀ h
  have hbase : (2 * (N : ℝ) + 1) ≤
      (1000 * (d : ℝ) + 5) * (ε⁻¹) ^ (2 : ℕ) := by
    have hN : (N : ℝ) < 5 * R / s + 2 := by
      dsimp [N]
      push_cast
      linarith only [hceil]
    nlinarith only [hN, hratio, hinv]
  have hcard : ((shellGridBox d N s).card : ℝ) ≤ (2 * (N : ℝ) + 1) ^ d := by
    exact_mod_cast card_shellGridBox_le d N s
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ 2 * (N : ℝ) + 1)
    hbase d
  exact hcard.trans hpow

end HigherDimLQGMetric
