import HigherDimLQGMetric.Sphere.Conv

/-!
# Provider of the frozen theorem `HigherDimLQGMetric.normLGFLaw_spec`

`normLGFLaw_spec_impl` states the frozen anchor `HigherDimLQGMetric/Frozen/NormLGFLawSpec.lean` verbatim. Its proof is
packet F3's `normLGFLaw_spec_holds` (`HigherDimLQGMetric/Sphere/Conv.lean`), i.e. packet F2's reduction
`normLGFLaw_spec_of_sphereAvg_spec'` (existence of the LGF from white noise and uniqueness of the normalized law,
`HigherDimLQGMetric/LGF/*`) applied to `sphereAvg_spec_holds`. This module imports no frozen theorem anchor.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- The frozen statement of `normLGFLaw_spec`, proved. -/
theorem normLGFLaw_spec_impl :
    ∀ (d : ℕ), 2 ≤ d → IsProbabilityMeasure (normLGFLaw d) ∧ IsNormalizedLGF id (normLGFLaw d) ∧
      ∀ μ : Measure (DistRd d), IsProbabilityMeasure μ → IsNormalizedLGF id μ → μ = normLGFLaw d :=
  normLGFLaw_spec_holds

end HigherDimLQGMetric
