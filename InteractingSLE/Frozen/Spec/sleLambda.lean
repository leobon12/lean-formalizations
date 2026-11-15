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

/-- `λ(a) = π / √a` (Specification p. 2, "Parameters and angle labels"). The companion
`χ(a) = 2 / √a - √a / 2` is reused: `QuantumZipper.chiC` (`QuantumZipper/Common/Basic.lean:38`). -/
def sleLambda (a : ℝ) : ℝ := Real.pi / Real.sqrt a

end InteractingSLE
