-- FROZEN_ANCHOR_PREFIX_BEGIN
import HigherDimLFPP.Frozen.Kappa
import LQGMetric.Statement.Dimension
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import HigherDimLFPP.TwoD.DimensionAsymptotics

/-!
# Frozen theorem: `lqg_dimension_asymptotics`

Anchor of the statement surface of the higher-dimensional LFPP formalization (manifest
`HigherDimLFPP/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`).
Source: the 2D paper (`LQGDimension`, Theorem 1.1, (1.6)) with its hypotheses discharged for the LQG
dimension `LQGMetric.dGamma` (ruling H9 (ii)); `κ₂ = a*/log 16` by `kappa_two_eq`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace HigherDimLFPP

/-- **d = 2, LQG dimension.** `(d_γ - 2)/γ^{4/3} → 2^{-1/3} κ₂` as `γ ↓ 0`, where `d_γ` is the
dimension of γ-Liouville quantum gravity (`LQGMetric.dGamma`). -/
theorem lqg_dimension_asymptotics :
    Tendsto (fun γ : ℝ => (LQGMetric.dGamma γ - 2) / γ ^ (4 / 3 : ℝ)) (𝓝[>] 0)
      (𝓝 (2 ^ (-1 / 3 : ℝ) * kappa 2)) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact HigherDimLFPP.lqg_dimension_asymptotics_impl
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end HigherDimLFPP
-- FROZEN_ANCHOR_SUFFIX_END
