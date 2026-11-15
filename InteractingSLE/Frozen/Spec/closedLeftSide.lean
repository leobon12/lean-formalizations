import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Process.Stopping
import Mathlib.Probability.ConditionalExpectation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import QuantumZipper.Loewner.Forward
import QuantumZipper.GFF.Kernels
import LQGMetric.Field.ZeroBoundary
import Mathlib.Analysis.Complex.Basic
import Mathlib.Order.Interval.Finset.Fin
import InteractingSLE.Frozen.Spec.seedRayClosure

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

/-- The full closed left Jordan side of a proper curve `γ` in `closure ℍ` from a real seed to
`∞` (Specification p. 528, W0): the connected component of the complement of
`seedRayClosure γ` containing the point `γ 0 - 1 - i` (which lies to the left of the upward
oriented seed ray), together with the closed curve itself ("Include the curve itself"). -/
def closedLeftSide (γ : ℝ≥0 → ℂ) : Set ℂ :=
  connectedComponentIn (seedRayClosure γ)ᶜ (γ 0 - 1 - Complex.I) ∪ seedRayClosure γ

end InteractingSLE
