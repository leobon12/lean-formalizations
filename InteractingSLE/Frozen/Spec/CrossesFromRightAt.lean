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
import InteractingSLE.Frozen.Spec.HasOrderedProperCompletions
import InteractingSLE.Frozen.Spec.activeDomain
import InteractingSLE.Frozen.Spec.IsActiveChart

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

/-- At the contact `p = η₁ s₀ = η₂ t₀`, the first path crosses the second from its right to its
left and never crosses back, in the precise stopped-order sense of Theorem 7.12C (Specification
p. 542; p. 461): in a common active chart `φ` of the active domain `D` of the two incoming
prefixes, centered at `p`, the outgoing available paths stay in `closure D` and have continuous
chart images `γ₁`, `γ₂` (`γᵢ u` is the limit of `φ` at `ηᵢ(· + u)` within `D`), and every pair of
strict finite outgoing prefixes has ordered proper completions with the first path's image on the
left: `HasOrderedProperCompletions γ₂ v γ₁ u`. -/
def CrossesFromRightAt (η₁ : ℝ≥0 → ℂ) (ζ₁ : ℝ≥0∞) (s₀ : ℝ≥0) (η₂ : ℝ≥0 → ℂ) (ζ₂ : ℝ≥0∞)
    (t₀ : ℝ≥0) : Prop :=
  ∃ φ : ℂ → ℂ, IsActiveChart (activeDomain η₁ s₀ η₂ t₀) (η₁ s₀) φ ∧
    ∃ γ₁ γ₂ : ℝ≥0 → ℂ,
      (∀ u : ℝ≥0, ((s₀ + u : ℝ≥0) : ℝ≥0∞) < ζ₁ →
        η₁ (s₀ + u) ∈ closure (activeDomain η₁ s₀ η₂ t₀) ∧
          Tendsto φ (𝓝[activeDomain η₁ s₀ η₂ t₀] (η₁ (s₀ + u))) (𝓝 (γ₁ u))) ∧
      (∀ v : ℝ≥0, ((t₀ + v : ℝ≥0) : ℝ≥0∞) < ζ₂ →
        η₂ (t₀ + v) ∈ closure (activeDomain η₁ s₀ η₂ t₀) ∧
          Tendsto φ (𝓝[activeDomain η₁ s₀ η₂ t₀] (η₂ (t₀ + v))) (𝓝 (γ₂ v))) ∧
      ∀ u v : ℝ≥0, ((s₀ + u : ℝ≥0) : ℝ≥0∞) < ζ₁ → ((t₀ + v : ℝ≥0) : ℝ≥0∞) < ζ₂ →
        HasOrderedProperCompletions γ₂ v γ₁ u

end InteractingSLE
