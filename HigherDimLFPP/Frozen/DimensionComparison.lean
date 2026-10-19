-- FROZEN_ANCHOR_PREFIX_BEGIN
import HigherDimLFPP.Frozen.Kappa
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import HigherDimLFPP.Var.Theorem11

/-!
# Frozen theorem: `dimension_comparison`

Anchor of the statement surface of the higher-dimensional LFPP formalization (manifest
`HigherDimLFPP/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`).
Source: `source/higher-dimensional-lfpp-limit.pdf`, (1.8) (from Lemma 2.3).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace HigherDimLFPP

/-- **(1.8)** `(d-1)^{2/3} κ₂ ≤ κ_d ≤ (d-1) κ₂` for every `d ≥ 2`. -/
theorem dimension_comparison : ∀ d : ℕ, 2 ≤ d →
    ((d : ℝ) - 1) ^ (2 / 3 : ℝ) * kappa 2 ≤ kappa d ∧ kappa d ≤ ((d : ℝ) - 1) * kappa 2 :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact HigherDimLFPP.dimension_comparison_impl
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end HigherDimLFPP
-- FROZEN_ANCHOR_SUFFIX_END
