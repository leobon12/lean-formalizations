import InteractingSLE.Spec.AuditFix.BoundaryContactStrong
import InteractingSLE.Spec.AuditFix.BoundaryContact

/-!
# Provider for a frozen anchor (sealed)

Anchor file: `InteractingSLE/Frozen/Spec/IsFlowLine_crosses_of_lt_of_contact.lean`.

The statement is the frozen anchor's with all arguments implicit and its hypotheses as auto-parameters (provider
convention); the proof is the closed theorem
`InteractingSLE.AuditFix.strongCrossesUponAvailableContact_holds` and
`InteractingSLE.AuditFix.criticalCrossingNoLaterInteriorPoint_holds` (external-audit response, ruling R122).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Spec.Provider

theorem IsFlowLine_crosses_of_lt_of_contact {κ : ℝ} (hκ : 0 < κ := by assumption) (hκ4 : κ < 4 := by assumption)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps := by assumption)
    {x₁ x₂ θ₁ θ₂ : ℝ}
    (hθ : θ₂ < θ₁ := by assumption) (hθπ : θ₁ < θ₂ + Real.pi := by assumption)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps := by assumption)
    {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ := by assumption)
    (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ := by assumption)
    (hx : x₂ < x₁ := by assumption) :
    (∀ᵐ ω ∂P, ∀ s t : ℝ≥0, (s : ℝ≥0∞) < ζ₁ ω → (t : ℝ≥0∞) < ζ₂ ω → η₁ ω s = η₂ ω t →
        ∃ s₀ t₀ : ℝ≥0, IsFirstContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) s₀ t₀ ∧
          CrossesFromRightAt (η₁ ω) (ζ₁ ω) s₀ (η₂ ω) (ζ₂ ω) t₀ ∧
          (∀ a a' : ℝ≥0, s₀ ≤ a → a < a' → (a' : ℝ≥0∞) ≤ ζ₁ ω →
            ¬ η₁ ω '' Set.Ioo a a' ⊆ η₂ ω '' {t : ℝ≥0 | t₀ ≤ t ∧ (t : ℝ≥0∞) < ζ₂ ω}) ∧
          ∀ c c' : ℝ≥0, t₀ ≤ c → c < c' → (c' : ℝ≥0∞) ≤ ζ₂ ω →
            ¬ η₂ ω '' Set.Ioo c c' ⊆ η₁ ω '' {s : ℝ≥0 | s₀ ≤ s ∧ (s : ℝ≥0∞) < ζ₁ ω}) ∧
      (Real.pi * κ / (4 - κ) ≤ θ₁ - θ₂ → ∀ᵐ ω ∂P, ∀ s t : ℝ≥0,
        (s : ℝ≥0∞) ≤ ζ₁ ω → (t : ℝ≥0∞) ≤ ζ₂ ω → η₁ ω s = η₂ ω t → η₁ ω s ∈ QuantumZipper.H →
          IsFirstContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) s t) :=
  by exact ⟨InteractingSLE.AuditFix.strongCrossesUponAvailableContact_holds hκ hκ4 b jumps hb hx hθ hθπ hh hη₁ hη₂,
    fun hcrit => InteractingSLE.AuditFix.criticalCrossingNoLaterInteriorPoint_holds hκ hκ4 b jumps hb hx hθ hθπ hh hη₁
      hη₂ hcrit⟩

end InteractingSLE.Spec.Provider
