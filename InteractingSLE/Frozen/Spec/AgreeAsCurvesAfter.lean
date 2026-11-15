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

/-- After the contact `η₁ s₀ = η₂ t₀` the two available paths agree as ordered unparametrized
curves until the shorter available portion ends (Specification p. 460, Corollary 7.12E; p. 542,
Theorem 7.12C, equal angles): there are end parameters `a ≤ ζ₁`, `c ≤ ζ₂`, one of them the
whole available lifetime, and an order isomorphism `e` from `{s | s₀ ≤ s ≤ a}` onto
`{t | t₀ ≤ t ≤ c}` with `η₂ ∘ e = η₁`. -/
def AgreeAsCurvesAfter (η₁ : ℝ≥0 → ℂ) (ζ₁ : ℝ≥0∞) (s₀ : ℝ≥0) (η₂ : ℝ≥0 → ℂ) (ζ₂ : ℝ≥0∞)
    (t₀ : ℝ≥0) : Prop :=
  ∃ a c : ℝ≥0∞, (s₀ : ℝ≥0∞) ≤ a ∧ a ≤ ζ₁ ∧ (t₀ : ℝ≥0∞) ≤ c ∧ c ≤ ζ₂ ∧ (a = ζ₁ ∨ c = ζ₂) ∧
    ∃ e : {s : ℝ≥0 // s₀ ≤ s ∧ (s : ℝ≥0∞) ≤ a} ≃o {t : ℝ≥0 // t₀ ≤ t ∧ (t : ℝ≥0∞) ≤ c},
      ∀ s, η₂ (e s) = η₁ s

end InteractingSLE
