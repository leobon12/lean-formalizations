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
import InteractingSLE.Frozen.Spec.flowLineNR

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

/-- The right mark positions of the flow-line force word, read in the chart `z ↦ z - x`
(see `flowLineNL`): `0` (the seed mark `0⁺`), then every genuine jump `y > x` of `b`, in
increasing order, at `y - x`. -/
def flowLineXR (b : ℝ → ℝ) (jumps : Finset ℝ) (x : ℝ) : Fin (flowLineNR b jumps x) → ℝ :=
  Fin.cons 0 fun i =>
    ((PiecewiseConstantBoundaryData.jumpSet b jumps).filter (x < ·)).orderEmbOfFin rfl i - x

end InteractingSLE
