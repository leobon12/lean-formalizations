import SupercriticalLQGUniqueness.B2.DG20Lim.AnnulusIteration64

 

set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Lim

def ratRad64 (r₀ : ℚ) (i : ℕ) : ℚ := r₀ / (64 : ℚ) ^ i

theorem ratRad64_pos {r₀ : ℚ} (hr₀ : 0 < r₀) (i : ℕ) : 0 < ratRad64 r₀ i :=
  div_pos hr₀ (pow_pos (by norm_num) _)

theorem geoRad64_eq_ratRad64 (r₀ : ℚ) (i : ℕ) :
    geoRad64 (16 * (r₀ : ℝ)) i = 16 * (ratRad64 r₀ i : ℝ) := by
  unfold geoRad64 ratRad64
  rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]
  push_cast
  ring

end SupercriticalLQGUniqueness.B2.DG20Lim
