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

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

/-- An interior available contact of two curves with available lifetimes `ζ₁`, `ζ₂`
(Specification p. 5, Theorem 1.5: "interior contacts while the relevant continuations are
available"; "common terminal points are excluded"): `η₁ s = η₂ t ∈ ℍ` with `s < ζ₁`, `t < ζ₂`. -/
def IsInteriorAvailableContact (η₁ : ℝ≥0 → ℂ) (ζ₁ : ℝ≥0∞) (η₂ : ℝ≥0 → ℂ) (ζ₂ : ℝ≥0∞)
    (s t : ℝ≥0) : Prop :=
  (s : ℝ≥0∞) < ζ₁ ∧ (t : ℝ≥0∞) < ζ₂ ∧ η₁ s = η₂ t ∧ η₁ s ∈ QuantumZipper.H

end InteractingSLE
