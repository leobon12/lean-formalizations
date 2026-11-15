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

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

/-- The unbounded part of `U ⊆ ℂ`: the points whose connected component in `U` is unbounded.
For `U = ℍ \ A` with `A` bounded this is the unique unbounded connected component of `U`. -/
def unboundedPart (U : Set ℂ) : Set ℂ :=
  {z ∈ U | ¬ Bornology.IsBounded (connectedComponentIn U z)}

end InteractingSLE
