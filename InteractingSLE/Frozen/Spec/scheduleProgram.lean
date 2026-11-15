import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Process.Stopping
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Order.Interval.Finset.Fin
import QuantumZipper.Loewner.Forward
import QuantumZipper.GFF.Kernels
import LQGMetric.Field.ZeroBoundary
import InteractingSLE.Frozen.Spec.Instr

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

/-- The program of a finite angle schedule `[(θ₁, τ₁), …, (θ_ℓ, τ_ℓ)]` whose switch and terminal times
`τ₁ < ⋯ < τ_ℓ` are in the history's own capacity clock (§5.2, p. 136; GW2): angle `θ_j` for own time `τ_j − τ_{j−1}`
(`τ₀ = 0`), i.e. the *flow* instructions `.inl (θ_j, τ_j − τ_{j−1})`. -/
def scheduleProgram : ℝ≥0 → List (ℝ × ℝ≥0) → List Instr
  | _, [] => []
  | τ₀, (θ, τ) :: l => Sum.inl (θ, ((τ - τ₀ : ℝ≥0) : ℝ≥0∞)) :: scheduleProgram τ l

end InteractingSLE
