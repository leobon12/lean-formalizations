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
import InteractingSLE.Frozen.Spec.PiecewiseConstantBoundaryData_jumpSet
import InteractingSLE.Frozen.Spec.PiecewiseConstantBoundaryData_rightLim
import InteractingSLE.Frozen.Spec.sleLambda

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

open Classical in
/-- The fixed rational roots of GW2 (p. 621), for boundary data `b` (locally constant off `jumps`): if the lower
extreme (angle `−π/2`) is immediately inadmissible at `0` because its right seed group is bad
(`b(0⁺) − πχ/2 ≤ −λ`; the only possible case, GW1.1), the rational points `v > 0` of its first low right boundary
arc, i.e. such that every original jump `x ∈ (0, v]` keeps the outward height low (`b(x⁺) − πχ/2 ≤ −λ`, BW2.1);
otherwise none. -/
def lowerArcRoots (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) : Set ℝ :=
  if PiecewiseConstantBoundaryData.rightLim b 0 - Real.pi / 2 * QuantumZipper.chiC κ ≤ -sleLambda κ then
    {v | (∃ q : ℚ, v = q) ∧ 0 < v ∧ ∀ x ∈ PiecewiseConstantBoundaryData.jumpSet b jumps, 0 < x → x ≤ v →
      PiecewiseConstantBoundaryData.rightLim b x - Real.pi / 2 * QuantumZipper.chiC κ ≤ -sleLambda κ}
  else ∅

end InteractingSLE
