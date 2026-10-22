import HigherDimLQGContinuity.Core.Interfaces

/-!
# Numerical probability budget for the pair and catalogue union
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HigherDimLQGContinuity

/-- The exponent chosen in Step 0 leaves four spare powers of the mesh after
summing over all pairs and catalogues. -/
theorem q11_probability_count {Δ D P B : ℝ}
    (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) (hB : 0 ≤ B)
    (hPc : P ≤ Δ ^ (-D)) (hBc : B ≤ Δ ^ (-(1 : ℝ))) :
    P * B * Δ ^ (2 * (D + 3) + 2) ≤ Δ ^ (D + 3) := by
  calc
    P * B * Δ ^ (2 * (D + 3) + 2)
        ≤ Δ ^ (-D) * Δ ^ (-(1 : ℝ)) * Δ ^ (2 * (D + 3) + 2) := by
          gcongr
    _ = Δ ^ ((D + 3) + 4) := by
          rw [← Real.rpow_add hΔ, ← Real.rpow_add hΔ]
          congr 1
          ring
    _ ≤ Δ ^ (D + 3) :=
          Real.rpow_le_rpow_of_exponent_ge hΔ hΔ1 (by linarith)

end HigherDimLQGContinuity
