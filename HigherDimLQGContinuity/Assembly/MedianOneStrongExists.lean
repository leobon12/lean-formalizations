import HigherDimLQGContinuity.Median.MedianOneStrong

/-!
# Provider of the frozen theorem `HigherDimLQGContinuity.medianOneStrong_exists`

`medianOneStrong_exists_impl` states the frozen anchor `HigherDimLQGContinuity/Frozen/MedianOneStrongExists.lean`
verbatim (non-vacuity: a median-one strong assignment exists at every subcritical ξ). Proof: packet PAR's
`medianOneStrong_holds` (`Median/MedianOneStrong.lean`: the strong assignment of the sealed `theorem12` already has unit
median, by `l10a_subseq_limit_median_one`). This module imports no frozen theorem anchor.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGContinuity

open HigherDimLQGMetric

/-- The frozen statement of `medianOneStrong_exists`, proved. -/
theorem medianOneStrong_exists_impl :
    ∀ d : ℕ, 3 ≤ d → ∀ ξ : ℝ, 0 < ξ → Real.sqrt (2 * d) < distExp d ξ →
      ∃ E : DistRd d → ContMetric d, IsStrongExpMetric d ξ (distExp d ξ) E ∧ IsMedianOne d E := by
  exact medianOneStrong_holds

end HigherDimLQGContinuity
