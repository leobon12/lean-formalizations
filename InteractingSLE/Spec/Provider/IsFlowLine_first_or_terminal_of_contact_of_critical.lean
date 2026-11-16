import InteractingSLE.Spec.RealContact.Main

/-!
# Provider for a frozen anchor (sealed)

Anchor file: `InteractingSLE/Frozen/Spec/IsFlowLine_first_or_terminal_of_contact_of_critical.lean`.

The statement is the frozen anchor's with all arguments implicit and its hypotheses as auto-parameters (provider
convention); the proof is the closed theorem `InteractingSLE.RealContact.criticalCrossingContact_holds` (ruling R124).

Parameter order: the conclusion fixes only the paths and their lifetimes, so the auto-parameters `hh`, `hη₁`, `hη₂`
come first (each matches one hypothesis of the anchor and fixes `h`, `x₁`, `θ₁`, `x₂`, `θ₂`); the inequalities follow.
In the anchor's order, `assumption` for `hx : ?x₂ < ?x₁` would match `hθπ : θ₁ < θ₂ + π`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Spec.Provider

theorem IsFlowLine_first_or_terminal_of_contact_of_critical {κ : ℝ} (hκ : 0 < κ := by assumption)
    (hκ4 : κ < 4 := by assumption)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps := by assumption)
    {x₁ x₂ θ₁ θ₂ : ℝ}
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps := by assumption)
    {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ := by assumption)
    (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ := by assumption)
    (hx : x₂ < x₁ := by assumption) (hθ : θ₂ < θ₁ := by assumption)
    (hθπ : θ₁ < θ₂ + Real.pi := by assumption)
    (hcrit : Real.pi * κ / (4 - κ) ≤ θ₁ - θ₂ := by assumption) :
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → (t : ℝ≥0∞) ≤ ζ₂ ω → η₁ ω s = η₂ ω t →
      IsFirstContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) s t ∨ ((s : ℝ≥0∞) = ζ₁ ω ∧ (t : ℝ≥0∞) = ζ₂ ω) :=
  by exact InteractingSLE.RealContact.criticalCrossingContact_holds hκ hκ4 b jumps hb hx hθ hθπ hh hη₁ hη₂ hcrit

end InteractingSLE.Spec.Provider
