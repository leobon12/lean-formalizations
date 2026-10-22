-- FROZEN_ANCHOR_PREFIX_BEGIN
import HigherDimLQGContinuity.Frozen.IsMedianOne
import HigherDimLQGMetric.Frozen.IsStrongExpMetric
import HigherDimLQGMetric.Frozen.DistExp
import Mathlib.Analysis.SpecialFunctions.Sqrt
import HigherDimLQGContinuity.Assembly.MedianOneStrongExists

/-!
# Frozen theorem: `medianOneStrong_exists`

Anchor of the statement surface of the HigherDimLQGContinuity formalization (manifest
`HigherDimLQGContinuity/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, N1, N4).
Source: `source/higher-dimensional-lqg-continuity.pdf` ([C], sha256 `05368f93…2f9c2e5934`, cited by line of the
text extraction `source/higher-dimensional-lqg-continuity.txt`): l. 25–30 (the γ-LQG metric of [8] exists),
(1.2), l. 32–34 (median-one normalization), l. 1297–1309 ("the metric `m_ξ⁻¹ ρ^ξ_h` is the unique median-one
metric", [8, Lemma 10.3]). Non-vacuity anchor (closure condition C1, ruling N4): for `d ≥ 3` and every
subcritical `ξ > 0` there is a strong assignment at `(ξ, Q(ξ))` whose unit distance `E_h(0, e₁)` has median one
under the law of the normalized LGF, so the version clauses of `theorem11Xi` and `theorem11` are not vacuous
(without this anchor `D ξ := |x − y|` for every `ξ` would prove them).

Proof body: the region between the `FROZEN_ANCHOR_PROOF` markers. Its state is recorded by the manifest:
`DRAFT_SORRY` (body exactly `by sorry`) or `SEALED` (body exactly
`by exact HigherDimLQGContinuity.medianOneStrong_exists_impl`, provider
`HigherDimLQGContinuity.Assembly.MedianOneStrongExists`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGContinuity

open HigherDimLQGMetric

/-- **Non-vacuity of the version clauses.** For `d ≥ 3` and every subcritical `ξ > 0` there is a strong
assignment at `(ξ, Q(ξ))` with median one. -/
theorem medianOneStrong_exists :
    ∀ d : ℕ, 3 ≤ d → ∀ ξ : ℝ, 0 < ξ → Real.sqrt (2 * d) < distExp d ξ →
      ∃ E : DistRd d → ContMetric d, IsStrongExpMetric d ξ (distExp d ξ) E ∧ IsMedianOne d E :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact HigherDimLQGContinuity.medianOneStrong_exists_impl
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end HigherDimLQGContinuity
-- FROZEN_ANCHOR_SUFFIX_END
