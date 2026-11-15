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

/-- `(s₀, t₀)` is the first contact of the available paths `η₁|[0, ζ₁]`, `η₂|[0, ζ₂]`, at finite
parameters and with finite terminal values included: `η₁ s₀ = η₂ t₀`, and every contact
`η₁ s = η₂ t` has `s₀ ≤ s` and `t₀ ≤ t`. So both first-contact infima are attained, at one common
point (Specification p. 542, Theorem 7.12C: "their first contacts occur at one common point"). -/
def IsFirstContact (η₁ : ℝ≥0 → ℂ) (ζ₁ : ℝ≥0∞) (η₂ : ℝ≥0 → ℂ) (ζ₂ : ℝ≥0∞) (s₀ t₀ : ℝ≥0) :
    Prop :=
  (s₀ : ℝ≥0∞) ≤ ζ₁ ∧ (t₀ : ℝ≥0∞) ≤ ζ₂ ∧ η₁ s₀ = η₂ t₀ ∧
    ∀ s t : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ → (t : ℝ≥0∞) ≤ ζ₂ → η₁ s = η₂ t → s₀ ≤ s ∧ t₀ ≤ t

end InteractingSLE
