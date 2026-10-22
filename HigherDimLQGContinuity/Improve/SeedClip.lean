import HigherDimLQGContinuity.Improve.SeedDepth

/-!
# Clipping the certificate seed gain at one
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HigherDimLQGContinuity

/-- The `SiteCertOfLabel` interface only asserts `d₀>0`; clipping the seed
gain preserves a fixed positive fraction of `θ` and makes it at most one. -/
theorem q11_seed_clip {θ d0 : ℝ}
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hd0 : 0 < d0) :
    let seed := min 1 (θ * d0 / 2)
    let dclip := min 1 (d0 / 2)
    0 < dclip ∧ 0 < seed ∧ seed ≤ 1 ∧
      θ * dclip ≤ seed ∧ seed ≤ θ * d0 / 2 := by
  have hdhalf : 0 < d0 / 2 := by positivity
  have hseed : 0 < θ * d0 / 2 := by positivity
  have hclip : 0 < min 1 (d0 / 2) := lt_min one_pos hdhalf
  have hseed0 : 0 < min 1 (θ * d0 / 2) := lt_min one_pos hseed
  have hleft : θ * min 1 (d0 / 2) ≤ 1 :=
    (mul_le_mul_of_nonneg_left (min_le_left _ _) hθ.le).trans (by simpa using hθ1)
  have hright : θ * min 1 (d0 / 2) ≤ θ * d0 / 2 := by
    have hh := mul_le_mul_of_nonneg_left (min_le_right (1 : ℝ) (d0 / 2)) hθ.le
    nlinarith only [hh]
  exact ⟨hclip, hseed0, min_le_left _ _, le_min hleft hright,
    min_le_right _ _⟩

end HigherDimLQGContinuity
