import SupercriticalLQGUniqueness.B2.DG20Lim.DyadicLatticeEventual

 

set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Lim

def dyadicRoundCoord (K : ℕ) (t : ℝ) : ℤ :=
  ⌊t * (2 : ℝ) ^ (K + 4)⌋

theorem dyadicRoundCoord_close (K : ℕ) (t : ℝ) :
    0 ≤ t - (dyadicRoundCoord K t : ℝ) / (2 : ℝ) ^ (K + 4) ∧
      t - (dyadicRoundCoord K t : ℝ) / (2 : ℝ) ^ (K + 4) <
        1 / (2 : ℝ) ^ (K + 4) := by
  have hp : 0 < (2 : ℝ) ^ (K + 4) := by positivity
  have hlo := Int.floor_le (t * (2 : ℝ) ^ (K + 4))
  have hhi := Int.lt_floor_add_one (t * (2 : ℝ) ^ (K + 4))
  constructor
  · apply sub_nonneg.mpr
    rw [div_le_iff₀ hp]
    exact hlo
  · rw [sub_lt_iff_lt_add, ← add_div, lt_div_iff₀ hp]
    simpa [dyadicRoundCoord, add_comm] using hhi

theorem dyadicRoundCoord_mem_box (R K : ℕ) (t : ℝ)
    (ht : |t| < (R : ℝ)) :
    -((R + 1) * 2 ^ (K + 4) : ℕ) ≤ dyadicRoundCoord K t ∧
      dyadicRoundCoord K t ≤ ((R + 1) * 2 ^ (K + 4) : ℕ) := by
  have hp : 0 < (2 : ℝ) ^ (K + 4) := by positivity
  have htlo : -(R : ℝ) < t := (abs_lt.mp ht).1
  have hthi : t < (R : ℝ) := (abs_lt.mp ht).2
  have hlo := Int.lt_floor_add_one (t * (2 : ℝ) ^ (K + 4))
  have hhi := Int.floor_le (t * (2 : ℝ) ^ (K + 4))
  have hpow1 : (1 : ℝ) ≤ (2 : ℝ) ^ (K + 4) := one_le_pow₀ (by norm_num)
  have hprodlo := mul_lt_mul_of_pos_right htlo hp
  have hprodhi := mul_lt_mul_of_pos_right hthi hp
  have hcast : (((R + 1) * 2 ^ (K + 4) : ℕ) : ℝ) =
      ((R : ℝ) + 1) * (2 : ℝ) ^ (K + 4) := by push_cast; ring
  constructor
  · have hh : -(((R + 1) * 2 ^ (K + 4) : ℕ) : ℝ) ≤
        (⌊t * (2 : ℝ) ^ (K + 4)⌋ : ℝ) := by rw [hcast]; nlinarith
    simpa only [dyadicRoundCoord] using (by exact_mod_cast hh :
      -((R + 1) * 2 ^ (K + 4) : ℕ) ≤
        ⌊t * (2 : ℝ) ^ (K + 4)⌋)
  · have hh : (⌊t * (2 : ℝ) ^ (K + 4)⌋ : ℝ) ≤
        (((R + 1) * 2 ^ (K + 4) : ℕ) : ℝ) := by rw [hcast]; nlinarith
    simpa only [dyadicRoundCoord] using (by exact_mod_cast hh :
      ⌊t * (2 : ℝ) ^ (K + 4)⌋ ≤
        ((R + 1) * 2 ^ (K + 4) : ℕ))

end SupercriticalLQGUniqueness.B2.DG20Lim
