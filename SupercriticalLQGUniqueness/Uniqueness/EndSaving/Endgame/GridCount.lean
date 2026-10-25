import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Endgame.GridFinite




 
set_option autoImplicit false
noncomputable section
open Set
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.Endgame

 
theorem endpointSites_card_scale_bound
    (b x : ℝ) (hb : 0 < b) (hx : 0 < x) (hx1 : x ≤ 1) :
    ((endpointSites (x * b / 100) b).card : ℝ) * x ^ 2 ≤ (203 : ℝ) ^ 2 := by
  have hratio : b / (x * b / 100) = 100 / x := by
    field_simp
  have hcard : ((endpointSites (x * b / 100) b).card : ℝ) ≤
      ((2 * ⌈b / (x * b / 100)⌉₊ + 1 : ℕ) : ℝ) ^ 2 := by
    exact_mod_cast endpointSites_card_le (x * b / 100) b
  rw [hratio] at hcard
  have hceil : (⌈100 / x⌉₊ : ℝ) < 100 / x + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hbase : (2 * (⌈100 / x⌉₊ : ℝ) + 1) * x ≤ 203 := by
    have hmul := mul_le_mul_of_nonneg_right hceil.le hx.le
    have hcancel : (100 / x + 1) * x = 100 + x := by field_simp
    nlinarith only [hmul, hcancel, hx1, hx]
  have hbase0 : 0 ≤ (2 * (⌈100 / x⌉₊ : ℝ) + 1) * x := by positivity
  have hsq := pow_le_pow_left₀ hbase0 hbase 2
  have hcard' : ((endpointSites (x * b / 100) b).card : ℝ) ≤
      (2 * (⌈100 / x⌉₊ : ℝ) + 1) ^ 2 := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hcard
  have hmul := mul_le_mul_of_nonneg_right hcard' (sq_nonneg x)
  nlinarith only [hmul, hsq]

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.Endgame
