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
import InteractingSLE.Frozen.Spec.PiecewiseConstantBoundaryData_jumpSet

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

/-- The number of right marks of the flow-line force word (see `flowLineNL`): the seed mark `0⁺`
and one mark for each genuine jump `y > x` of `b`. -/
def flowLineNR (b : ℝ → ℝ) (jumps : Finset ℝ) (x : ℝ) : ℕ :=
  ((PiecewiseConstantBoundaryData.jumpSet b jumps).filter (x < ·)).card + 1

end InteractingSLE
