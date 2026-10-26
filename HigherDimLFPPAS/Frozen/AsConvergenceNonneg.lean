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
import HigherDimLFPPAS.Implementation.AsConvergenceNonneg

/-!
# Frozen theorem: `asConvergence_nonneg`

Anchor of the statement surface of the HigherDimLFPPAS formalization (manifest
`HigherDimLFPPAS/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, L1, L7, L8; statement audit
`planning/audits/S1-statement-audit.md`).
Source: `source/higher-dimensional-lfpp-almost-sure.pdf` ([AS], sha256 `7476d6f4…da93197`, cited by line of the
text extraction `source/higher-dimensional-lfpp-almost-sure.txt`): Theorem 1.2, l. 118–125, made unconditional for
nonnegative seeds (ruling L1: "the unconditional corollary wherever the repository proves Assumption 1.1"). For
`d ≥ 3`, `ξ > 0`, `Q(ξ) > √(2d)` there is one strong assignment `D` at `(ξ, Q(ξ))`, with median one (the
continuity paper's (1.2), the frozen `HigherDimLQGContinuity.IsMedianOne`), such that for every nonnegative seed
(`HigherDimLFPP.IsLFPPKernel`, the kernels of `HigherDimLQGMetric.theorem12`, its ruling M6) and every normalized
LGF on every probability space, the conclusion (1.7) of Theorem 1.2 holds almost surely. Assumption 1.1 is supplied
by the sealed `HigherDimLQGMetric.theorem12`; it is not a hypothesis here.

Proof body: the region between the `FROZEN_ANCHOR_PROOF` markers. Its state is recorded by the manifest:
`DRAFT_SORRY` (body exactly `by sorry`) or `SEALED` (body exactly
`by exact HigherDimLFPPAS.Implementation.asConvergence_nonneg_impl`, provider
`HigherDimLFPPAS.Implementation.AsConvergenceNonneg`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace HigherDimLFPPAS

open HigherDimLQGMetric HigherDimLQGContinuity
open HigherDimLFPP (Rd)

/-- **Theorem 1.2, unconditional for nonnegative seeds.** For `d ≥ 3` and subcritical `ξ > 0` there is a
median-one strong assignment `D` at `(ξ, Q(ξ))` to which, for every nonnegative seed and every normalized LGF,
the median-normalized convolution LFPP converges almost surely, locally uniformly, along all `ε ↓ 0`. -/
theorem asConvergence_nonneg :
    ∀ (d : ℕ) (ξ : ℝ), 3 ≤ d → 0 < ξ → Real.sqrt (2 * d) < distExp d ξ →
    ∃ D : DistRd d → ContMetric d, IsStrongExpMetric d ξ (distExp d ξ) D ∧ IsMedianOne d D ∧
      ∀ κ : Rd d → ℝ, HigherDimLFPP.IsLFPPKernel κ →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsNormalizedLGF h P →
        ∀ᵐ ω ∂P, ∀ F : Set (Rd d), IsCompact F →
          Tendsto (fun ε : ℝ => ⨆ p ∈ F ×ˢ F,
              edist (((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω)) p) ((D (h ω)).1 p))
            (𝓝[>] 0) (𝓝 0) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact HigherDimLFPPAS.Implementation.asConvergence_nonneg_impl
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end HigherDimLFPPAS
-- FROZEN_ANCHOR_SUFFIX_END
