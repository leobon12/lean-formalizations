import HigherDimLQGMetric.Bilip.Event
import HigherDimLQGMetric.Sharp.GridCount

/-! The grid count from `Sharp.GridCount` with the dimension threshold needed
by Proposition 3.13.  Its proof only uses `0 < d`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HigherDimLQGMetric
open HigherDimLFPP (Rd)

theorem bilip_card_shellGridBox_scaled {d : ℕ} (hd : 2 ≤ d)
    {𝕣 ε : ℝ} (h𝕣 : 0 < 𝕣) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ((shellGridBox d (⌈(𝕣 / ε) / (ε ^ 2 * 𝕣 / (10 * d))⌉₊ + 1)
      (ε ^ 2 * 𝕣 / (10 * d))).card : ℝ) * ε ^ (3 * d) ≤ (25 * d : ℝ) ^ d := by
  let s : ℝ := ε ^ 2 * 𝕣 / (10 * d)
  let B : ℝ := 𝕣 / ε
  let N : ℕ := ⌈B / s⌉₊ + 1
  have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hs : 0 < s := by dsimp [s]; positivity
  have hε3 : 0 < ε ^ 3 := pow_pos hε0 _
  have hε3le : ε ^ 3 ≤ 1 := pow_le_one₀ hε0.le hε1.le
  have hquot : B / s = 10 * (d : ℝ) / ε ^ 3 := by
    dsimp [B, s]
    field_simp
  have hN : (N : ℝ) < B / s + 2 := by
    dsimp [N]
    push_cast
    linarith [Nat.ceil_lt_add_one (le_of_lt (div_pos (div_pos h𝕣 hε0) hs))]
  have hNε : (N : ℝ) * ε ^ 3 < 10 * d + 2 := by
    rw [hquot] at hN
    have hm := mul_lt_mul_of_pos_right hN hε3
    have hcancel : (10 * (d : ℝ) / ε ^ 3 + 2) * ε ^ 3 = 10 * d + 2 * ε ^ 3 := by
      field_simp
    rw [hcancel] at hm
    linarith
  have hN₁ : (2 * (N : ℝ) + 1) * ε ^ 3 ≤ 25 * d := by
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
    nlinarith
  have hcard := card_shellGridBox_le d N s
  have hcardR : ((shellGridBox d N s).card : ℝ) ≤ (2 * (N : ℝ) + 1) ^ d := by
    exact_mod_cast hcard
  have hpow : ((2 * (N : ℝ) + 1) * ε ^ 3) ^ d ≤ (25 * d : ℝ) ^ d :=
    pow_le_pow_left₀ (by positivity) hN₁ d
  have heq : (2 * (N : ℝ) + 1) ^ d * ε ^ (3 * d) =
      ((2 * (N : ℝ) + 1) * ε ^ 3) ^ d := by rw [pow_mul, mul_pow]
  change ((shellGridBox d N s).card : ℝ) * ε ^ (3 * d) ≤ (25 * d : ℝ) ^ d
  calc
    ((shellGridBox d N s).card : ℝ) * ε ^ (3 * d) ≤
        (2 * (N : ℝ) + 1) ^ d * ε ^ (3 * d) :=
      mul_le_mul_of_nonneg_right hcardR (by positivity)
    _ = ((2 * (N : ℝ) + 1) * ε ^ 3) ^ d := heq
    _ ≤ (25 * d : ℝ) ^ d := hpow

end HigherDimLQGMetric
