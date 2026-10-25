import SupercriticalLQGUniqueness.B2.DG20Lim.SparseDyadicRadius
import Mathlib.Data.Int.Interval

 

set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Lim

def dyadicLatticeBox (R K : ℕ) : Finset (ℤ × ℤ) :=
  let M : ℕ := R * 2 ^ (K + 4)
  (Finset.Icc (-(M : ℤ)) (M : ℤ)).product
    (Finset.Icc (-(M : ℤ)) (M : ℤ))

theorem dyadicLatticeBox_card (R K : ℕ) :
    (dyadicLatticeBox R K).card = (2 * (R * 2 ^ (K + 4)) + 1) ^ 2 := by
  have hM (M : ℕ) : (Finset.Icc (-(M : ℤ)) (M : ℤ)).card = 2 * M + 1 := by
    rw [Int.card_Icc]
    have h : (M : ℤ) + 1 - -(M : ℤ) = ((2 * M + 1 : ℕ) : ℤ) := by
      push_cast
      ring
    rw [h, Int.toNat_natCast]
  let M : ℕ := R * 2 ^ (K + 4)
  change ((Finset.Icc (-(M : ℤ)) (M : ℤ)).product
    (Finset.Icc (-(M : ℤ)) (M : ℤ))).card = (2 * M + 1) ^ 2
  rw [Finset.product_eq_sprod, Finset.card_product, hM]
  ring

theorem dyadicLatticeBox_card_le (R K : ℕ) :
    (dyadicLatticeBox R K).card ≤ (32 * R + 1) ^ 2 * 4 ^ K := by
  rw [dyadicLatticeBox_card]
  have hpow : 1 ≤ 2 ^ K := one_le_pow₀ (by norm_num : 1 ≤ (2 : ℕ))
  have hsmall : 2 * (R * 2 ^ (K + 4)) + 1 ≤
      (32 * R + 1) * 2 ^ K := by
    calc
      2 * (R * 2 ^ (K + 4)) + 1 = 32 * R * 2 ^ K + 1 := by
        rw [pow_add]
        norm_num
        ring
      _ ≤ 32 * R * 2 ^ K + 2 ^ K := by omega
      _ = (32 * R + 1) * 2 ^ K := by ring
  have h4 : (4 : ℕ) ^ K = (2 ^ K) ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, mul_pow]
    ring
  calc
    (2 * (R * 2 ^ (K + 4)) + 1) ^ 2 ≤
        ((32 * R + 1) * 2 ^ K) ^ 2 := by gcongr
    _ = (32 * R + 1) ^ 2 * 4 ^ K := by rw [h4]; ring

end SupercriticalLQGUniqueness.B2.DG20Lim
