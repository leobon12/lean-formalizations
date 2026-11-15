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
import InteractingSLE.Frozen.Spec.PiecewiseConstantBoundaryData_rightLim
import InteractingSLE.Frozen.Spec.PiecewiseConstantBoundaryData_leftLim

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

/-- The genuine jump points of `b` (the points of `jumps` where the one-sided limits differ).
For piecewise-constant data this set depends only on `b`, not on the chosen finite set `jumps`. -/
def PiecewiseConstantBoundaryData.jumpSet (b : ℝ → ℝ) (jumps : Finset ℝ) : Finset ℝ :=
  jumps.filter fun y =>
    PiecewiseConstantBoundaryData.leftLim b y ≠ PiecewiseConstantBoundaryData.rightLim b y

end InteractingSLE
