import HigherDimLQGMetric.ConvField.Spec

/-!
# Provider of the frozen theorem `HigherDimLQGMetric.convMollify_spec`

`convMollify_spec_impl` states the frozen anchor `HigherDimLQGMetric/Frozen/ConvMollifySpec.lean` verbatim. Its proof is
packet L2b's `convMollify_spec_proof` (`HigherDimLQGMetric/ConvField/Spec.lean`: the improper limit of the truncated
pairings `h(convTrunc κ ε z n)` exists a.s. for all `z` simultaneously and equals the frozen `convMollify`, for every LGF
plus a bounded continuous function; MA5 A4, ruling M16 C1). This module imports no frozen theorem anchor.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- The frozen statement of `convMollify_spec`, proved. -/
theorem convMollify_spec_impl :
    ∀ (d : ℕ), 2 ≤ d → ∀ κ : Rd d → ℝ, HigherDimLFPP.IsLFPPKernel κ →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsLGFPlusBddCont h P → ∀ ε : ℝ, 0 < ε → ∀ᵐ ω ∂P, ∀ z : Rd d,
          Tendsto (fun n : ℕ => h ω (convTrunc κ ε z n)) atTop (𝓝 (convMollify κ ε (h ω) z)) :=
  convMollify_spec_proof

end HigherDimLQGMetric
