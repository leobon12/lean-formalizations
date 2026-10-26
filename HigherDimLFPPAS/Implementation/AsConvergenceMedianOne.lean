import Mathlib
import HigherDimLFPPAS.Frozen.IsAdmissibleSeed
import HigherDimLFPPAS.Frozen.Assumption11
import HigherDimLFPPAS.Main.Final
import HigherDimLFPPAS.Rescale.PairLaw
import HigherDimLFPPAS.Rescale.Loc
import HigherDimLFPPAS.Rescale.Conv

/-!
# Provider of the frozen theorem `HigherDimLFPPAS.asConvergence_medianOne`

`asConvergence_medianOne_impl` states the frozen anchor `HigherDimLFPPAS/Frozen/AsConvergenceMedianOne.lean`
(approval version 2, ruling L10) verbatim: Theorem 1.2 of [AS] for nonnegative seeds and every median-one strong
assignment, so the almost-sure limit is identified (rulings L1, L7, L8). Proof: the final composition
`HigherDimLFPPAS.Main.asConvergence_medianOne_of_rz` (packet ASM1) applied to the three rescaling producers
`HigherDimLFPPAS.Rescale.pairLaw_holds` (packet RZP), `HigherDimLFPPAS.Rescale.rescaledLoc_holds` (RZL) and
`HigherDimLFPPAS.Rescale.rescaledConv_holds` (RZC). This provider does not use the providers of `asConvergence` or
`asConvergence_nonneg`. `import Mathlib` comes first, as in the anchor's frozen prefix (ruling L10), so that the
statement elaborates here exactly as in the anchor (the instance `SupSet ℝ≥0∞` of the `⨆`). This module imports no
frozen theorem anchor of this library.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace HigherDimLFPPAS.Implementation

open HigherDimLQGMetric HigherDimLQGContinuity
open HigherDimLFPP (Rd)

/-- The frozen statement of `asConvergence_medianOne` (Theorem 1.2 for nonnegative seeds, every median-one strong
limit), proved. -/
theorem asConvergence_medianOne_impl :
    ∀ (d : ℕ) (ξ : ℝ), 3 ≤ d → 0 < ξ → Real.sqrt (2 * d) < distExp d ξ →
    ∀ D : DistRd d → ContMetric d, IsStrongExpMetric d ξ (distExp d ξ) D → IsMedianOne d D →
      ∀ κ : Rd d → ℝ, HigherDimLFPP.IsLFPPKernel κ →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsNormalizedLGF h P →
        ∀ᵐ ω ∂P, ∀ F : Set (Rd d), IsCompact F →
          Tendsto (fun ε : ℝ => ⨆ p ∈ F ×ˢ F,
              edist (((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω)) p) ((D (h ω)).1 p))
            (𝓝[>] 0) (𝓝 0) :=
  HigherDimLFPPAS.Main.asConvergence_medianOne_of_rz (fun hS => HigherDimLFPPAS.Rescale.pairLaw_holds hS)
    (fun hS => HigherDimLFPPAS.Rescale.rescaledLoc_holds hS)
    (fun hS hloc => HigherDimLFPPAS.Rescale.rescaledConv_holds hS hloc)

end HigherDimLFPPAS.Implementation
