-- FROZEN_ANCHOR_PREFIX_BEGIN
import Mathlib
import HigherDimLQGMetric.Frozen.IsStrongExpMetric
import HigherDimLQGMetric.Frozen.IsNormalizedLGF
import HigherDimLQGMetric.Frozen.DistExp
import HigherDimLQGMetric.Frozen.AEps
import HigherDimLQGMetric.Frozen.LfppDist
import HigherDimLQGContinuity.Frozen.IsMedianOne
import HigherDimLFPP.Frozen.IsLFPPKernel
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Instances.ENNReal.Lemmas
import HigherDimLFPPAS.Implementation.AsConvergenceMedianOne

/-!
# Frozen theorem: `asConvergence_medianOne`

Anchor of the statement surface of the HigherDimLFPPAS formalization (manifest
`HigherDimLFPPAS/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, L1, L7, L8; statement audit
`planning/audits/S1-statement-audit.md`).
Source: `source/higher-dimensional-lfpp-almost-sure.pdf` ([AS], sha256 `7476d6f4…da93197`, cited by line of the
text extraction `source/higher-dimensional-lfpp-almost-sure.txt`): Theorem 1.2, l. 118–125, unconditional for
nonnegative seeds (ruling L1), with the limit identified: as `asConvergence_nonneg`, for **every** median-one strong
assignment (not only one): the almost-sure limit is the median-one strong metric. Together with the sealed
`HigherDimLQGContinuity.medianOneStrong_exists` it implies `asConvergence_nonneg`.

Proof body: the region between the `FROZEN_ANCHOR_PROOF` markers. Its state is recorded by the manifest:
`DRAFT_SORRY` (body exactly `by sorry`) or `SEALED` (body exactly
`by exact HigherDimLFPPAS.Implementation.asConvergence_medianOne_impl`, provider
`HigherDimLFPPAS.Implementation.AsConvergenceMedianOne`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace HigherDimLFPPAS

open HigherDimLQGMetric HigherDimLQGContinuity
open HigherDimLFPP (Rd)

/-- **Theorem 1.2 for nonnegative seeds, every median-one strong limit.** -/
theorem asConvergence_medianOne :
    ∀ (d : ℕ) (ξ : ℝ), 3 ≤ d → 0 < ξ → Real.sqrt (2 * d) < distExp d ξ →
    ∀ D : DistRd d → ContMetric d, IsStrongExpMetric d ξ (distExp d ξ) D → IsMedianOne d D →
      ∀ κ : Rd d → ℝ, HigherDimLFPP.IsLFPPKernel κ →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsNormalizedLGF h P →
        ∀ᵐ ω ∂P, ∀ F : Set (Rd d), IsCompact F →
          Tendsto (fun ε : ℝ => ⨆ p ∈ F ×ˢ F,
              edist (((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω)) p) ((D (h ω)).1 p))
            (𝓝[>] 0) (𝓝 0) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact HigherDimLFPPAS.Implementation.asConvergence_medianOne_impl
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end HigherDimLFPPAS
-- FROZEN_ANCHOR_SUFFIX_END
