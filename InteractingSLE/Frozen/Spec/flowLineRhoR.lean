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
import InteractingSLE.Frozen.Spec.sleLambda
import InteractingSLE.Frozen.Spec.PiecewiseConstantBoundaryData_rightLim
import InteractingSLE.Frozen.Spec.PiecewiseConstantBoundaryData_leftLim
import InteractingSLE.Frozen.Spec.PiecewiseConstantBoundaryData_jumpSet
import InteractingSLE.Frozen.Spec.flowLineNR

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

/-- The right mark weights of the force word of the angle-`θ` flow line from `x` (see
`flowLineRhoL`): the seed mark `0⁺` has weight `(b(x⁺) + θχ)/λ - 1`, and the mark at `y - x` of a
genuine jump `y > x` has weight `(b(y⁺) - b(y⁻))/λ`. With these weights the force-word boundary
data of Theorem 1.1, `λ(1 + Σ_{i ≤ j} ρ^{i,R})` on the right, equal `b(· + x) + θχ` off the marks.
The seed mark is kept even when its weight is `0` (passive mark). -/
def flowLineRhoR (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (x θ : ℝ) :
    Fin (flowLineNR b jumps x) → ℝ :=
  Fin.cons
    ((PiecewiseConstantBoundaryData.rightLim b x + θ * QuantumZipper.chiC κ) / sleLambda κ - 1)
    fun i =>
      let y := ((PiecewiseConstantBoundaryData.jumpSet b jumps).filter (x < ·)).orderEmbOfFin rfl i
      (PiecewiseConstantBoundaryData.rightLim b y - PiecewiseConstantBoundaryData.leftLim b y) /
        sleLambda κ

end InteractingSLE
