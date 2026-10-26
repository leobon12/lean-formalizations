import Mathlib
import HigherDimLFPPAS.Frozen.IsAdmissibleSeed
import HigherDimLFPPAS.Frozen.Assumption11
import HigherDimLFPPAS.Main.Final
import HigherDimLFPPAS.Rescale.PairLaw
import HigherDimLFPPAS.Rescale.Loc
import HigherDimLFPPAS.Rescale.Conv

/-!
# Provider of the frozen theorem `HigherDimLFPPAS.asConvergence`

`asConvergence_impl` states the frozen anchor `HigherDimLFPPAS/Frozen/AsConvergence.lean` (approval version 2,
ruling L10) verbatim: Theorem 1.2 of [AS] for signed admissible seeds under Assumption 1.1 (rulings L6, L7, L8).
Proof: the final composition `HigherDimLFPPAS.Main.asConvergence_of_rz` (packet ASM1) applied to the three
rescaling producers `HigherDimLFPPAS.Rescale.pairLaw_holds` (packet RZP), `HigherDimLFPPAS.Rescale.rescaledLoc_holds`
(RZL) and `HigherDimLFPPAS.Rescale.rescaledConv_holds` (RZC). `import Mathlib` comes first, as in the anchor's frozen
prefix (ruling L10), so that the statement elaborates here exactly as in the anchor (the instance `SupSet ℝ≥0∞` of
the `⨆`). This module imports no frozen theorem anchor of this library.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace HigherDimLFPPAS.Implementation

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

/-- The frozen statement of `asConvergence` (Theorem 1.2), proved. -/
theorem asConvergence_impl :
    ∀ (d : ℕ) (ξ : ℝ), 3 ≤ d → 0 < ξ →
    ∀ κ : Rd d → ℝ, IsAdmissibleSeed κ →
    ∀ D : DistRd d → ContMetric d,
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistRd d),
      IsNormalizedLGF h P → Assumption11 d ξ κ D P h →
      ∀ᵐ ω ∂P, ∀ F : Set (Rd d), IsCompact F →
        Tendsto (fun ε : ℝ => ⨆ p ∈ F ×ˢ F,
            edist (((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω)) p) ((D (h ω)).1 p))
          (𝓝[>] 0) (𝓝 0) :=
  HigherDimLFPPAS.Main.asConvergence_of_rz (fun hS => HigherDimLFPPAS.Rescale.pairLaw_holds hS)
    (fun hS => HigherDimLFPPAS.Rescale.rescaledLoc_holds hS)
    (fun hS hloc => HigherDimLFPPAS.Rescale.rescaledConv_holds hS hloc)

end HigherDimLFPPAS.Implementation
