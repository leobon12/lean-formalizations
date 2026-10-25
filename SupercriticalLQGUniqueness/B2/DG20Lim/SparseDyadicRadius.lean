import SupercriticalLQGUniqueness.B2.DG20Lim.SparseDyadicIndices

 

set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem ratRad64_one_eq_dyadic (i : ℕ) :
    ratRad64 1 i = 1 / (2 : ℚ) ^ (6 * i) := by
  have h64 : (64 : ℚ) = (2 : ℚ) ^ 6 := by norm_num
  simp only [ratRad64, h64, ← pow_mul]

end SupercriticalLQGUniqueness.B2.DG20Lim
