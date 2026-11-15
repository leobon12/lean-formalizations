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

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

/-- The points of `ℍ \ A` on the right of `A`: those whose connected component in `ℍ \ A` has a point of the
positive real axis outside `A` in its closure. For a simple curve `A` from `0` to `∞` in `closure ℍ` these are
exactly the points on its right side. -/
def rightSideOf (A : Set ℂ) : Set ℂ :=
  {z | z ∈ QuantumZipper.H \ A ∧ ∃ x : ℝ, 0 < x ∧ (x : ℂ) ∉ A ∧
    (x : ℂ) ∈ closure (connectedComponentIn (QuantumZipper.H \ A) z)}

end InteractingSLE
