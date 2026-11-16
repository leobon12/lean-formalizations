import InteractingSLE.Spec.RealContact.Main

/-!
# Provider for a frozen anchor (sealed)

Anchor file: `InteractingSLE/Frozen/Spec/IsFlowLine_start_or_terminal_of_contact_of_critical.lean`.

The statement is the frozen anchor's with all arguments implicit and its hypotheses as auto-parameters (provider
convention); the proof is the closed theorem `InteractingSLE.RealContact.criticalOrderedContact_holds` (ruling R124).

Parameter order: the auto-parameters `hh`, `hη₁`, `hη₂` come first (each matches one hypothesis of the anchor and fixes
`h`, `θ₁`, `θ₂`); the inequalities follow, as in the provider of `IsFlowLine_first_or_terminal_of_contact_of_critical`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Spec.Provider

theorem IsFlowLine_start_or_terminal_of_contact_of_critical {κ : ℝ} (hκ : 0 < κ := by assumption)
    (hκ4 : κ < 4 := by assumption)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps := by assumption)
    {x₁ x₂ θ₁ θ₂ : ℝ}
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps := by assumption)
    {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ := by assumption)
    (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ := by assumption)
    (hx : x₂ ≤ x₁ := by assumption) (hθ : θ₁ < θ₂ := by assumption)
    (hcrit : Real.pi * κ / (4 - κ) ≤ θ₂ - θ₁ := by assumption) :
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → (t : ℝ≥0∞) ≤ ζ₂ ω → η₁ ω s = η₂ ω t →
      (x₁ = x₂ ∧ s = 0 ∧ t = 0) ∨ ((s : ℝ≥0∞) = ζ₁ ω ∧ (t : ℝ≥0∞) = ζ₂ ω) :=
  by exact InteractingSLE.RealContact.criticalOrderedContact_holds hκ hκ4 b jumps hb hx hθ hh hη₁ hη₂ hcrit

end InteractingSLE.Spec.Provider
