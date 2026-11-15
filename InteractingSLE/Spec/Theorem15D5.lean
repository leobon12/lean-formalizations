/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Theorem15D5Critical
import InteractingSLE.Spec.Theorem15D5Crossing

/-!
# Theorem 1.5 (constant-angle interaction) by the short final proof of D.5

Packet PROVE-T15-D5 (ruling R38; follow-up note `source/external/AstraIG1/ig1_followup_proofs.txt` L2303–L2386).
The three frozen clauses of Theorem 1.5 (Specification p. 5) are proved here with **exactly their frozen
conclusions and binders**, from the five D.5 interfaces only (`Theorem15D5Inputs.lean` has the table):

* `stays_right_of_lt_of_d5` (i): **order** — W5 is the stays-to-the-right clause (strict prefixes, the frozen
  available-time convention); **critical-angle exclusion** — Theorem 7.12D (`thm712DStatement_of_d5`: the
  rational-cut collar, (7.12D.1) `D ≥ κ/2 ⟹` exposed-side weight `D − 2 ≥ c`, G7 + GB7a, W0b), with the angle
  conversion `D_θ ≥ κ/2 ⟺ θ₂ − θ₁ ≥ πκ/(4 − κ)` (`Theorem15.half_le_mul_chiC_div_sleLambda_iff`).
* `merges_of_d5` (ii): **equal-angle merging** — Lemma 7.7's first contact (in place of Theorem W8), the restart
  kernel and universal determination (`Restart.merges_of_restart`: one canonical conditional path; for `x₁ = x₂` the
  universal determining graph directly).
* `crosses_of_lt_of_d5` (iii): **crossing** — at Lemma 7.7's first contact, W5 applied to the outgoing paths under
  the restart kernel (`chartOrderAfterCrossingStatement_of_restartLim`); **no interior contact after a crossing at
  the critical angle** — 7.12D in the first-contact chart (`Restart.criticalExclusionAfterCrossingStatement_of_restart`
  with `thm712DStatement_of_d5` on the canonical space).

Of the eight named inputs of `Theorem15.lean` (W5, W8, 7.12C crossing, 7.12C merging, 7.12D, the critical exclusion
after a crossing, Aux. 25, Lemma 7.5), five are gone (W8, both 7.12C statements, 7.12D, the critical exclusion
after a crossing: each is now proved from the D.5 interfaces); W5, Aux. 25 and Lemma 7.5 remain as D.5 interfaces 3
and 1. Not used: W2a, W6, W7, W8, CP2–CP3, S0–S9, the light-cone theorem.

The interfaces appear at the universe of the statement and, where the canonical restart space is used, at
universe `0` (they are universe-polymorphic named propositions).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Theorem15D5

open Sec7 Theorem15 Supp10 Restart

/-- **Theorem 1.5 (i)** (Specification p. 5) by D.5, with exactly the conclusion of the frozen
`IsFlowLine.stays_right_of_lt`. Interfaces: W5 with its contact-order theorems (Aux. 84, G5), W0b, G7 + GB7a at a
retained pair, Aux. 25 and the reality of finite continuation endpoints. -/
theorem stays_right_of_lt_of_d5 (hW5 : W5Statement.{u}) (hFH : G7GB7aFirstHitStatement.{u})
    (hE : FiniteEndpointRealStatement.{u}) (hW0b : Supp9.W0bStatement.{u}) (h84 : Aux84Statement)
    (hG5 : G5Statement) (hA25 : Aux25Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (b : ℝ → ℝ) (jumps : Finset ℝ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    {x₁ x₂ θ₁ θ₂ : ℝ} (hx : x₂ ≤ x₁) (hθ : θ₁ < θ₂)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂) :
    (∀ᵐ ω ∂P, ∀ a c : ℝ≥0, (a : ℝ≥0∞) < ζ₁ ω → (c : ℝ≥0∞) < ζ₂ ω →
        HasOrderedProperCompletions (η₁ ω) a (η₂ ω) c) ∧
      (Real.pi * κ / (4 - κ) ≤ θ₂ - θ₁ → ∀ᵐ ω ∂P, ∀ s t : ℝ≥0,
        ¬ IsInteriorAvailableContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) s t) :=
  stays_right_of_lt_of_inputs hW5 (thm712DStatement_of_d5 hFH hE hW0b hW5 h84 hG5 hA25) hκ hκ4 b jumps hb hx
    hθ hh hη₁ hη₂

/-- **Theorem 1.5 (ii)** (Specification p. 5) by D.5, with exactly the conclusion of the frozen
`IsFlowLine.merges`. Interfaces: Lemma 7.7 (first contact), the restart carrier (7.8), universal determination
(Lemma 7.5, also on the canonical space) and Aux. 25. -/
theorem merges_of_d5 (h77 : Lemma77Statement.{u}) (hR : FirstContactRestartStatement.{u})
    (hL75 : Lemma75Statement.{u}) (hL75₀ : Lemma75Statement.{0}) (hA25 : Aux25Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (b : ℝ → ℝ) (jumps : Finset ℝ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    {x₁ x₂ θ : ℝ} (hx : x₂ ≤ x₁)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    (hη₁ : IsFlowLine κ b jumps x₁ θ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ P h η₂ ζ₂) :
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, IsInteriorAvailableContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) s t →
      AgreeAsCurvesAfter (η₁ ω) (ζ₁ ω) s (η₂ ω) (ζ₂ ω) t :=
  merges_of_restart (w8FirstContactStatement_of_lemma77 h77) hA25 hL75 hL75₀ hR hκ hκ4 b jumps hb hx hh hη₁ hη₂

/-- **Theorem 1.5 (iii)** (Specification p. 5) by D.5, with exactly the conclusion of the frozen
`IsFlowLine.crosses_of_lt`. Interfaces: Lemma 7.7, the restart carrier with the active prime end, W5 on the
canonical space, 7.12D's interfaces on the canonical space (G7 + GB7a, W0b, Aux. 84, G5, Aux. 25, real finite
endpoints) and Aux. 25. -/
theorem crosses_of_lt_of_d5 (h77 : Lemma77Statement.{u}) (hR : FirstContactRestartLimStatement.{u})
    (hW5₀ : W5Statement.{0}) (hFH₀ : G7GB7aFirstHitStatement.{0}) (hE₀ : FiniteEndpointRealStatement.{0})
    (hW0b₀ : Supp9.W0bStatement.{0}) (h84 : Aux84Statement) (hG5 : G5Statement)
    (hA25₀ : Aux25Statement.{0}) (hA25 : Aux25Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (b : ℝ → ℝ) (jumps : Finset ℝ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    {x₁ x₂ θ₁ θ₂ : ℝ} (hx : x₂ < x₁) (hθ : θ₂ < θ₁) (hθπ : θ₁ < θ₂ + Real.pi)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂) :
    (∀ᵐ ω ∂P, ∀ s t : ℝ≥0, IsInteriorAvailableContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) s t →
        ∃ s₀ t₀ : ℝ≥0, IsFirstContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) s₀ t₀ ∧
          CrossesFromRightAt (η₁ ω) (ζ₁ ω) s₀ (η₂ ω) (ζ₂ ω) t₀) ∧
      (Real.pi * κ / (4 - κ) ≤ θ₁ - θ₂ → ∀ᵐ ω ∂P, ∀ s t : ℝ≥0,
        IsInteriorAvailableContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) s t →
          IsFirstContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) s t) :=
  crosses_of_lt_of_inputs (w8FirstContactStatement_of_lemma77 h77)
    (thm712CCrossingStatement_of_inputs h77 (chartOrderAfterCrossingStatement_of_restartLim hR hW5₀))
    (criticalExclusionAfterCrossingStatement_of_restart (firstContactRestartStatement_of_lim hR)
      (thm712DStatement_of_d5 hFH₀ hE₀ hW0b₀ hW5₀ h84 hG5 hA25₀) h77 hA25)
    hA25 hκ hκ4 b jumps hb hx hθ hθπ hh hη₁ hη₂

end Theorem15D5

end InteractingSLE
