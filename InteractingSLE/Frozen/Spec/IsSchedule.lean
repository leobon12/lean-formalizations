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

/-- A finite `Θ`-angle schedule with switch and terminal times in `Q`, strictly increasing. -/
def IsSchedule (Θ : Set ℝ) (Q : Set ℝ≥0) (l : List (ℝ × ℝ≥0)) : Prop :=
  (∀ p ∈ l, p.1 ∈ Θ ∧ p.2 ∈ Q) ∧ l.Pairwise (fun p q => p.2 < q.2)

end InteractingSLE
