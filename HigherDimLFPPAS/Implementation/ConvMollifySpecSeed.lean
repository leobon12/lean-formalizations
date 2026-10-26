import HigherDimLFPPAS.Frozen.IsAdmissibleSeed
import HigherDimLFPPAS.Signed.Radial
import HigherDimLQGMetric.Frozen.ConvMollify
import HigherDimLQGMetric.Frozen.IsLGFPlusBddCont

/-!
# Provider of the frozen theorem `HigherDimLFPPAS.convMollify_spec_seed`

`convMollify_spec_seed_impl` states the frozen anchor `HigherDimLFPPAS/Frozen/ConvMollifySpecSeed.lean` verbatim
(for every admissible seed and an LGF plus a bounded continuous function, `h * K_ε` exists a.s. everywhere;
rulings L7, L8). Proof: the sign-free copy `HigherDimLFPPAS.Signed.convMollify_spec_impl_seed` (packet G1) of the
host provider `HigherDimLQGMetric.convMollify_spec_impl`, whose type is this statement. This module imports no
frozen theorem anchor of this library.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology

namespace HigherDimLFPPAS.Implementation

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

/-- The frozen statement of `convMollify_spec_seed`, proved. -/
theorem convMollify_spec_seed_impl :
    ∀ (d : ℕ), 2 ≤ d → ∀ κ : Rd d → ℝ, IsAdmissibleSeed κ →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsLGFPlusBddCont h P → ∀ ε : ℝ, 0 < ε → ∀ᵐ ω ∂P, ∀ z : Rd d,
          Tendsto (fun n : ℕ => h ω (convTrunc κ ε z n)) atTop (𝓝 (convMollify κ ε (h ω) z)) :=
  Signed.convMollify_spec_impl_seed

end HigherDimLFPPAS.Implementation
