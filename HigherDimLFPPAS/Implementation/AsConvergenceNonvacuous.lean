import HigherDimLFPPAS.Frozen.IsAdmissibleSeed
import HigherDimLFPPAS.Frozen.Assumption11
import HigherDimLQGMetric.Frozen.IsNormalizedLGF
import HigherDimLQGMetric.Frozen.Theorem12
import HigherDimLQGMetric.Frozen.SubcriticalNonempty
import HigherDimLQGMetric.Frozen.NormLGFLawSpec
import HigherDimLQGMetric.Field.LGFPlusCont
import HigherDimLFPP.Field.Exists

/-!
# Provider of the frozen theorem `HigherDimLFPPAS.asConvergence_nonvacuous`

`asConvergence_nonvacuous_impl` states the frozen anchor `HigherDimLFPPAS/Frozen/AsConvergenceNonvacuous.lean`
verbatim (the hypotheses of Theorem 1.2 are jointly satisfiable for `d ≥ 3` and all small `ξ > 0`; ruling L1).
Proof (the statement audit's witness `w_asNonvacuous`, `planning/audits/S1-statement-audit.md` §Details): the sealed
`HigherDimLQGMetric.subcritical_nonempty` gives `ξ₀ > 0` with `(0, ξ₀)` subcritical; `HigherDimLFPP.exists_isLFPPKernel`
a nonnegative seed `κ`, which is an admissible seed (drop `nonneg`); the sealed `HigherDimLQGMetric.theorem12` a strong
assignment `D` at `(ξ, Q(ξ))` with (1.6) for `κ` and every LGF plus a bounded continuous function; the sealed
`HigherDimLQGMetric.normLGFLaw_spec` the normalized LGF `id` under its law `normLGFLaw d` on `DistRd d`, which is such
a field (`IsWholeSpaceLGF.isLGFPlusBddCont`). Self-contained (it does not use the sibling provider
`Implementation.Assumption11Nonvacuous`); this module imports no frozen theorem anchor of this library.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory

namespace HigherDimLFPPAS.Implementation

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

/-- The frozen statement of `asConvergence_nonvacuous`, proved. -/
theorem asConvergence_nonvacuous_impl :
    ∀ d : ℕ, 3 ≤ d → ∃ ξ₀ : ℝ, 0 < ξ₀ ∧ ∀ ξ ∈ Set.Ioo (0 : ℝ) ξ₀,
      ∃ (κ : Rd d → ℝ) (D : DistRd d → ContMetric d) (Ω : Type) (_ : MeasurableSpace Ω)
        (P : Measure Ω) (h : Ω → DistRd d),
        IsAdmissibleSeed κ ∧ IsProbabilityMeasure P ∧ IsNormalizedLGF h P ∧ Assumption11 d ξ κ D P h := by
  intro d hd
  obtain ⟨ξ₀, hξ₀, hsub⟩ := subcritical_nonempty d (by omega)
  refine ⟨ξ₀, hξ₀, fun ξ hξ => ?_⟩
  obtain ⟨κ, hκ⟩ := HigherDimLFPP.exists_isLFPPKernel d
  obtain ⟨⟨D, hD, hconv⟩, -⟩ := theorem12 d ξ hd hξ.1 (hsub ξ hξ)
  obtain ⟨hP, hN, -⟩ := normLGFLaw_spec d (by omega)
  exact ⟨κ, D, DistRd d, inferInstance, normLGFLaw d, id,
    ⟨hκ.contDiff, hκ.hasCompactSupport, hκ.radial, hκ.integral_sq⟩, hP, hN,
    ⟨hsub ξ hξ, hD, hconv κ hκ (normLGFLaw d) id hN.1.isLGFPlusBddCont⟩⟩

end HigherDimLFPPAS.Implementation
