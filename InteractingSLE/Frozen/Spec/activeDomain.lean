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
import InteractingSLE.Frozen.Spec.unboundedPart

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

/-- The active domain after the prefixes `η₁([0, s])` and `η₂([0, t])`: the unbounded connected
component of `ℍ \ (η₁([0, s]) ∪ η₂([0, t]))` (Specification p. 290, Lemma 7.8, "`D` the unique
unbounded connected component of `ℍ \ K`"). -/
def activeDomain (η₁ : ℝ≥0 → ℂ) (s : ℝ≥0) (η₂ : ℝ≥0 → ℂ) (t : ℝ≥0) : Set ℂ :=
  unboundedPart (QuantumZipper.H \ (η₁ '' Set.Icc 0 s ∪ η₂ '' Set.Icc 0 t))

end InteractingSLE
