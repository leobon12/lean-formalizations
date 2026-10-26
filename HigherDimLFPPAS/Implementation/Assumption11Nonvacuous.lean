import HigherDimLFPPAS.Frozen.IsAdmissibleSeed
import HigherDimLFPPAS.Frozen.Assumption11
import HigherDimLQGMetric.Frozen.IsNormalizedLGF
import HigherDimLQGMetric.Frozen.Theorem12
import HigherDimLQGMetric.Field.LGFPlusCont
import HigherDimLFPP.Frozen.IsLFPPKernel

/-!
# Provider of the frozen theorem `HigherDimLFPPAS.assumption11_nonvacuous`

`assumption11_nonvacuous_impl` states the frozen anchor `HigherDimLFPPAS/Frozen/Assumption11Nonvacuous.lean`
verbatim (non-vacuity of Assumption 1.1 for nonnegative seeds, one assignment for all seeds and fields; ruling L1).
Proof (the statement audit's witness `w_nonvacuous`, `planning/audits/S1-statement-audit.md` §Details): the sealed
`HigherDimLQGMetric.theorem12` gives, for `d ≥ 3` and subcritical `ξ > 0`, one strong assignment `D` at
`(ξ, Q(ξ))` such that (1.6) holds for every nonnegative seed and every LGF plus a bounded continuous function; a
nonnegative seed is an admissible seed (drop `nonneg`), and a normalized LGF is such a field
(`IsWholeSpaceLGF.isLGFPlusBddCont`). This module imports no frozen theorem anchor of this library.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory

namespace HigherDimLFPPAS.Implementation

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

/-- The frozen statement of `assumption11_nonvacuous`, proved. -/
theorem assumption11_nonvacuous_impl :
    ∀ (d : ℕ) (ξ : ℝ), 3 ≤ d → 0 < ξ → Real.sqrt (2 * d) < distExp d ξ →
    ∃ D : DistRd d → ContMetric d, ∀ κ : Rd d → ℝ, HigherDimLFPP.IsLFPPKernel κ →
      IsAdmissibleSeed κ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsNormalizedLGF h P → Assumption11 d ξ κ D P h := by
  intro d ξ hd hξ hsub
  obtain ⟨⟨D, hD, hconv⟩, -⟩ := theorem12 d ξ hd hξ hsub
  refine ⟨D, fun κ hκ => ⟨⟨hκ.contDiff, hκ.hasCompactSupport, hκ.radial, hκ.integral_sq⟩, ?_⟩⟩
  intro Ω _ P _ h hh
  exact ⟨hsub, hD, hconv κ hκ P h hh.1.isLGFPlusBddCont⟩

end HigherDimLFPPAS.Implementation
