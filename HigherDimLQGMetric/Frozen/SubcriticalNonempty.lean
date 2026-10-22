-- FROZEN_ANCHOR_PREFIX_BEGIN
import HigherDimLQGMetric.Frozen.DistExp
import Mathlib.Analysis.SpecialFunctions.Sqrt
import HigherDimLQGMetric.Assembly.SubcriticalNonempty

/-!
# Frozen theorem: `subcritical_nonempty`

Anchor of the statement surface of the higher-dimensional LQG metric formalization (manifest
`HigherDimLQGMetric/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, M7, M13).
Source: `source/higher-dimensional-lqg-metric.pdf` ([S], cited by line of the text extraction `.txt`):
[S] l. 50 ("`Q = Q(ξ) > √(2d)`"); [2] (1.9) (`Q(ξ) ≥ 1/ξ - √(2d)`); ruling M7. Sanity anchor (MA0
fidelity note 4): the subcritical hypothesis `√(2d) < distExp d ξ` of the main theorems holds for all small
`ξ > 0` (non-vacuity).

State `DRAFT_SORRY` (ruling M13): the body is exactly `by sorry` until it is sealed as
`by exact HigherDimLQGMetric.subcritical_nonempty_impl` (provider `HigherDimLQGMetric.Assembly.SubcriticalNonempty`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- Sanity anchor: the subcritical range `{ξ > 0 : √(2d) < Q(ξ)}` contains an interval `(0, ξ₀)`. -/
theorem subcritical_nonempty :
    ∀ (d : ℕ), 2 ≤ d → ∃ ξ₀ : ℝ, 0 < ξ₀ ∧ ∀ ξ ∈ Ioo (0 : ℝ) ξ₀, Real.sqrt (2 * d) < distExp d ξ :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact HigherDimLQGMetric.subcritical_nonempty_impl
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end HigherDimLQGMetric
-- FROZEN_ANCHOR_SUFFIX_END
