import HigherDimLQGMetric.Sphere.Conv

/-!
# Provider of the frozen theorem `HigherDimLQGMetric.sphereAvg_spec`

`sphereAvg_spec_impl` states the frozen anchor `HigherDimLQGMetric/Frozen/SphereAvgSpec.lean` verbatim. Its proof is
packet F3's `sphereAvg_spec_holds` (`HigherDimLQGMetric/Sphere/Conv.lean`: variance `≤ C 2^{-n}/r` of the increments
of the mollified sphere averages, Borel–Cantelli; MA0 D-F3, ruling M17). This module imports no frozen theorem
anchor.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- The frozen statement of `sphereAvg_spec`, proved. -/
theorem sphereAvg_spec_impl :
    ∀ (d : ℕ), 2 ≤ d → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistRd d), IsLGFPlusCont h P → ∀ r : ℝ, 0 < r → ∀ z : Rd d,
        ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => ∫ u, h ω (bumpTest n (z + r • u)) ∂(unitSphereProb d))
          atTop (𝓝 (sphereAvg (h ω) r z)) :=
  sphereAvg_spec_holds

end HigherDimLQGMetric
