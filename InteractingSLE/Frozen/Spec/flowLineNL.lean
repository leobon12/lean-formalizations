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

/-- The number of left marks of the force word of the angle-`θ` flow line from `x` of a field with
boundary data `b` (Specification p. 9, Theorem 1.1; p. 10, Definition; p. 11; seed weights as in
W0a, p. 528): the seed mark `0⁻` and one mark for each genuine jump `y < x` of `b`. The whole word
is `flowLineXL`, `flowLineXR` (positions) and `flowLineRhoL`, `flowLineRhoR` (weights). -/
def flowLineNL (b : ℝ → ℝ) (jumps : Finset ℝ) (x : ℝ) : ℕ :=
  ((PiecewiseConstantBoundaryData.jumpSet b jumps).filter (· < x)).card + 1

end InteractingSLE
