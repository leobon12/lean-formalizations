import HigherDimLQGContinuity.Core.Interfaces

/-!
# Numerical margin for rounding a separated bad pair
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HigherDimLQGContinuity

/-- The radius and comparison error chosen in Step 1 satisfy the smallness
condition of `net_rounding`. The upper Hölder constant is `2H`. -/
theorem q11_rounding_small {Cb H σ g dsep ε t : ℝ}
    (hCb : 0 < Cb) (hH : 0 < H) (hσ : 0 < σ)
    (hg : 0 < g) (hdsep : 0 < dsep) (ht : 0 ≤ t)
    (htbound : t ≤ (7 * g * dsep / (128 * Cb * H)) ^ (1 / σ))
    (hε : 2 * ε ≤ 7 / 16 * g * dsep) :
    4 * Cb * (2 * H) * t ^ σ + 2 * ε ≤ 7 / 8 * g * dsep := by
  let A : ℝ := 7 * g * dsep / (128 * Cb * H)
  have hA : 0 < A := by dsimp [A]; positivity
  have hpow : t ^ σ ≤ A := by
    change t ≤ A ^ (1 / σ) at htbound
    have hh := Real.rpow_le_rpow ht htbound hσ.le
    have hright : (A ^ (1 / σ)) ^ σ = A := by
      rw [← Real.rpow_mul hA.le]
      rw [div_mul_cancel₀ _ hσ.ne', Real.rpow_one]
    rw [hright] at hh
    exact hh
  have hmul := mul_le_mul_of_nonneg_left hpow
    (by positivity : 0 ≤ 4 * Cb * (2 * H))
  have heq : 4 * Cb * (2 * H) * A = 7 / 16 * g * dsep := by
    dsimp [A]
    field_simp
    ring
  rw [heq] at hmul
  linarith only [hmul, hε]

/-- The concrete radius used for rounding. -/
def q11RoundingRadius (w Cb H σ g dsep : ℝ) : ℝ :=
  min (w / 8) ((7 * g * dsep / (128 * Cb * H)) ^ (1 / σ))

theorem q11_rounding_radius_spec {w Cb H σ g dsep ε : ℝ}
    (hw : 0 < w) (hCb : 0 < Cb) (hH : 0 < H) (hσ : 0 < σ)
    (hg : 0 < g) (hdsep : 0 < dsep)
    (hε : 2 * ε ≤ 7 / 16 * g * dsep) :
    0 < q11RoundingRadius w Cb H σ g dsep ∧
    q11RoundingRadius w Cb H σ g dsep ≤ w / 8 ∧
    4 * Cb * (2 * H) * (q11RoundingRadius w Cb H σ g dsep) ^ σ +
      2 * ε ≤ 7 / 8 * g * dsep := by
  have hA : 0 < 7 * g * dsep / (128 * Cb * H) := by positivity
  have ht : 0 < q11RoundingRadius w Cb H σ g dsep := by
    dsimp [q11RoundingRadius]
    exact lt_min (by positivity) (Real.rpow_pos_of_pos hA _)
  refine ⟨ht, min_le_left _ _, ?_⟩
  exact q11_rounding_small hCb hH hσ hg hdsep ht.le
    (min_le_right _ _) hε

end HigherDimLQGContinuity
