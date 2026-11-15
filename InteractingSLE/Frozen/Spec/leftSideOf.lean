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

/-- The points of `ℍ \ A` on the left of `A` (reflection of `rightSideOf`). -/
def leftSideOf (A : Set ℂ) : Set ℂ :=
  {z | z ∈ QuantumZipper.H \ A ∧ ∃ x : ℝ, x < 0 ∧ (x : ℂ) ∉ A ∧
    (x : ℂ) ∈ closure (connectedComponentIn (QuantumZipper.H \ A) z)}

/-! ## G7. Components between the walks (Lemma GW3, Theorem GW4) -/

end InteractingSLE
