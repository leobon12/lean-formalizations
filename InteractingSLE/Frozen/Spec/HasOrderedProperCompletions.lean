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
import InteractingSLE.Frozen.Spec.closedLeftSide
import InteractingSLE.Frozen.Spec.IsProperCompletion

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

/-- **Convention W0** (Specification p. 528): the prefixes `α([0, a])` and `β([0, c])` have
ordered proper completions — continuous injective proper extensions `α̂`, `β̂` in the closed upper
half-plane from their seeds to `∞`, with `β̂` in the full closed left Jordan side of `α̂`. This is
the precise sense of "`α` stays to the right of `β`" (Theorem 7.10, p. 459; W5, pp. 533–534). -/
def HasOrderedProperCompletions (α : ℝ≥0 → ℂ) (a : ℝ≥0) (β : ℝ≥0 → ℂ) (c : ℝ≥0) : Prop :=
  ∃ α' β' : ℝ≥0 → ℂ, IsProperCompletion α a α' ∧ IsProperCompletion β c β' ∧
    Set.range β' ⊆ closedLeftSide α'

end InteractingSLE
