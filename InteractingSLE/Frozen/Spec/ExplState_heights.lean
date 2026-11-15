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
import InteractingSLE.Frozen.Spec.PiecewiseConstantBoundaryData_leftLim
import InteractingSLE.Frozen.Spec.PiecewiseConstantBoundaryData_rightLim
import InteractingSLE.Frozen.Spec.sleLambda
import InteractingSLE.Frozen.Spec.ExplState

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

/-- The one-sided heights `(left, right)` of the flow background `h` (boundary data `b`) at the current real point,
in the conditional field: original values `b(pt⁻)`, `b(pt⁺)`, except that at a right (left) threshold the left
(right) side is the exposed side of the last piece, of height `−λ − θχ` (`λ − θχ`) (Theorem 1.1, p. 9; GW1
active-word classification, p. 619). -/
def ExplState.heights (κ : ℝ) (b : ℝ → ℝ) (s : ExplState) : ℝ × ℝ :=
  let (_, _, _, _, _, status, pt, angle, _, _) := s
  match status with
  | .inr (.inr (.inl (some true))) =>  -- thr (some true)
      (-sleLambda κ - angle * QuantumZipper.chiC κ, PiecewiseConstantBoundaryData.rightLim b pt)
  | .inr (.inr (.inl (some false))) =>  -- thr (some false)
      (PiecewiseConstantBoundaryData.leftLim b pt, sleLambda κ - angle * QuantumZipper.chiC κ)
  | _ => (PiecewiseConstantBoundaryData.leftLim b pt, PiecewiseConstantBoundaryData.rightLim b pt)

end InteractingSLE
