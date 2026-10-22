import HigherDimLQGMetric.Kernel.ConvKernelMain
import HigherDimLFPP.Field.Measures

/-!
# Pairability above a positive scale

Mass-zero finite measure pairs with bounded support admit the white-noise
pairing on every band bounded away from scale zero.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ} {κ : Rd d → ℝ}

theorem pairable_above_of_bounded_support (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {ε : ℝ} (hε : 0 < ε) {μ ν : Measure (Rd d)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hmass : μ.real univ = ν.real univ)
    {D : ℝ} (hμD : ∀ᵐ z ∂μ, ‖z‖ ≤ D)
    (hνD : ∀ᵐ z ∂ν, ‖z‖ ≤ D) :
    HigherDimLFPP.IsPairable κ (Ioi ε) μ ν :=
  HigherDimLFPP.isPairable_of_subset_Ici hκ measurableSet_Ioi hε
    (fun _ h => show ε ≤ _ from le_of_lt h) μ ν hmass hμD hνD

end HigherDimLQGMetric
