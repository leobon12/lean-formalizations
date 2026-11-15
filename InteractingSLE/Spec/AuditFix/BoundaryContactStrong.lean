/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.AuditFix.BoundaryContact
import InteractingSLE.Spec.AuditFix.StrongCross

/-!
# Theorem 1.5 (iii) with both audit fixes: every available contact, and no common outgoing arc

Packets PROVE-AF-CONTACT (audit §2.1, contact scope) and PROVE-AF-CROSS (audit §2.2, crossing excludes merging),
combined. `CrossesUponAvailableContactStatement` (this packet, `BoundaryContact.lean`) widens the trigger of the
frozen crossing clause to every available contact, real points included; PROVE-AF-CROSS's
`noCommonOutgoingArc_upon_availableContact` (`StrongCross.lean`) proves, at the first contact forced by any available
contact, that the outgoing available paths have no common open arc. Both concern the same first contact (it is
unique, `Sec7.IsFirstContact.unique`), so they combine into:

* **`StrongCrossesUponAvailableContactStatement`**, **`strongCrossesUponAvailableContact_holds`**: Theorem 1.5 (iii)
  (paper p. 30: "upon intersecting, crosses and then never crosses back"; Proposition 7.12, p. 141, at the first
  intersection, possibly on `∂ℍ`; specification Theorem 7.12C, p. 542: "They have no common nontrivial open outgoing
  arc") at every available contact;
* `strongCrossStatement_firstClause_of_strongCrossesUponAvailableContact`: it implies the first clause of
  PROVE-AF-CROSS's `StrongCrossStatement`.

No new mathematics.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.AuditFix

/-- **Theorem 1.5 (iii), crossing excludes merging, at every available contact.** For `x₂ < x₁` and
`θ₂ < θ₁ < θ₂ + π`: almost surely, if the flow lines have an available contact `η₁ s = η₂ t` (`s < ζ₁`, `t < ζ₂`, the
point interior or real), then their first contact `(s₀, t₀)` is attained at one common point, the first curve crosses
the second there (`CrossesFromRightAt`), and the outgoing available paths `η₁([s₀, ζ₁))`, `η₂([t₀, ζ₂))` have no common
open arc. -/
def StrongCrossesUponAvailableContactStatement : Prop :=
  ∀ {κ : ℝ} (_hκ : 0 < κ) (_hκ4 : κ < 4)
    (b : ℝ → ℝ) (jumps : Finset ℝ) (_hb : IsPiecewiseConstantBoundaryData b jumps)
    {x₁ x₂ θ₁ θ₂ : ℝ} (_hx : x₂ < x₁) (_hθ : θ₂ < θ₁) (_hθπ : θ₁ < θ₂ + Real.pi)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (_hh : IsGFFWithBoundaryData P h b jumps)
    {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    (_hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (_hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂),
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, (s : ℝ≥0∞) < ζ₁ ω → (t : ℝ≥0∞) < ζ₂ ω → η₁ ω s = η₂ ω t →
      ∃ s₀ t₀ : ℝ≥0, IsFirstContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) s₀ t₀ ∧
        CrossesFromRightAt (η₁ ω) (ζ₁ ω) s₀ (η₂ ω) (ζ₂ ω) t₀ ∧
        (∀ a a' : ℝ≥0, s₀ ≤ a → a < a' → (a' : ℝ≥0∞) ≤ ζ₁ ω →
          ¬ η₁ ω '' Set.Ioo a a' ⊆ η₂ ω '' {t : ℝ≥0 | t₀ ≤ t ∧ (t : ℝ≥0∞) < ζ₂ ω}) ∧
        ∀ c c' : ℝ≥0, t₀ ≤ c → c < c' → (c' : ℝ≥0∞) ≤ ζ₂ ω →
          ¬ η₂ ω '' Set.Ioo c c' ⊆ η₁ ω '' {s : ℝ≥0 | s₀ ≤ s ∧ (s : ℝ≥0∞) < ζ₁ ω}

/-- **Proved**: `crossesUponAvailableContact_holds` and PROVE-AF-CROSS's `noCommonOutgoingArc_upon_availableContact`
at the same (unique) first contact. -/
theorem strongCrossesUponAvailableContact_holds : StrongCrossesUponAvailableContactStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ hθπ Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂
  filter_upwards [crossesUponAvailableContact_holds hκ hκ4 b jumps hb hx hθ hθπ hh hη₁ hη₂,
    noCommonOutgoingArc_upon_availableContact hκ hκ4 b jumps hb hx hθ hθπ hh hη₁ hη₂] with ω hC hA
  intro s t hs ht hst
  obtain ⟨s₀, t₀, h₀, hcross⟩ := hC s t hs ht hst
  obtain ⟨s₀', t₀', h₀', harc₁, harc₂⟩ := hA s t hs ht hst
  obtain ⟨rfl, rfl⟩ := Sec7.IsFirstContact.unique h₀' h₀
  exact ⟨_, _, h₀, hcross, harc₁, harc₂⟩

/-- The combined statement implies the first clause of PROVE-AF-CROSS's `StrongCrossStatement` (an interior
available contact is an available contact). -/
theorem strongCrossStatement_firstClause_of_strongCrossesUponAvailableContact
    (hS : StrongCrossesUponAvailableContactStatement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (b : ℝ → ℝ) (jumps : Finset ℝ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    {x₁ x₂ θ₁ θ₂ : ℝ} (hx : x₂ < x₁) (hθ : θ₂ < θ₁) (hθπ : θ₁ < θ₂ + Real.pi)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂) :
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, IsInteriorAvailableContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) s t →
      ∃ s₀ t₀ : ℝ≥0, IsFirstContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) s₀ t₀ ∧
        CrossesFromRightAt (η₁ ω) (ζ₁ ω) s₀ (η₂ ω) (ζ₂ ω) t₀ ∧
        (∀ a a' : ℝ≥0, s₀ ≤ a → a < a' → (a' : ℝ≥0∞) ≤ ζ₁ ω →
          ¬ η₁ ω '' Set.Ioo a a' ⊆ η₂ ω '' {t : ℝ≥0 | t₀ ≤ t ∧ (t : ℝ≥0∞) < ζ₂ ω}) ∧
        ∀ c c' : ℝ≥0, t₀ ≤ c → c < c' → (c' : ℝ≥0∞) ≤ ζ₂ ω →
          ¬ η₂ ω '' Set.Ioo c c' ⊆ η₁ ω '' {s : ℝ≥0 | s₀ ≤ s ∧ (s : ℝ≥0∞) < ζ₁ ω} := by
  filter_upwards [hS hκ hκ4 b jumps hb hx hθ hθπ hh hη₁ hη₂] with ω hω s t hst
  exact hω s t hst.1 hst.2.1 hst.2.2.1

end InteractingSLE.AuditFix
