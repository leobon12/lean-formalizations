import HigherDimLQGContinuity.Caps.FullScales

/-!
# Full-scale radii in the exponential mesh notation
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HigherDimLQGContinuity

/-- The exact radius window used by the catalogue proof, expressed through
`Δ=exp(-V)`. -/
theorem q11_full_scale_mesh {V : ℝ} (hV : 0 ≤ V) :
    let Δ := Real.exp (-V)
    ∀ k ∈ p4_fullScales V,
      Δ ^ (2 : ℕ) ≤ p4_radius k ∧ p4_radius k ≤ Δ := by
  change ∀ k ∈ p4_fullScales V,
    (Real.exp (-V)) ^ (2 : ℕ) ≤ p4_radius k ∧
      p4_radius k ≤ Real.exp (-V)
  intro k hk
  have hrad := (p4_mem_fullScales_iff hV k).mp hk
  have heq : (Real.exp (-V)) ^ (2 : ℕ) = Real.exp (-2 * V) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  simpa only [heq] using hrad

end HigherDimLQGContinuity
