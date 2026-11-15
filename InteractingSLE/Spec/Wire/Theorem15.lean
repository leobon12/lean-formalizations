/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Theorem15D5
import InteractingSLE.Spec.Supplement.S9EAssembly
import InteractingSLE.Spec.Supplement.S9CTip
import InteractingSLE.Spec.Supplement.S9BOrder
import InteractingSLE.Spec.Sec4.Aux25Term
import InteractingSLE.Foundations.Loewner.FiniteEndpointStatement

/-!
# Theorem 1.5 with the newly proved inputs discharged

Packet PROVE-WIRE1 (no new mathematics). PROVE-T15-D5 proved the three frozen clauses of Theorem 1.5 from the D.5
interfaces (`Theorem15D5.stays_right_of_lt_of_d5`, `merges_of_d5`, `crosses_of_lt_of_d5`, `Spec/Theorem15D5.lean`).
Four of those interfaces are now theorems and are discharged here:

| Interface | Now proved by |
|---|---|
| `Theorem15.Aux25Statement` (Aux. lemma 25, simplicity; universes `u` and `0`) | `Theorem15.aux25Statement` |
| `Supp10.Aux84Statement` (contact order, ordered distinct seeds) | `Supp9B.aux84Statement` |
| `Supp10.G5Statement` (contact order, common seed) | `Supp9B.g5Statement` |
| `Supp10.FiniteEndpointRealStatement` (a finite continuation endpoint is real) | `Supp10.finiteEndpointRealStatement` |

Theorem W5 (`Theorem15.W5Statement`, interface 3) is still open. It has two landed reductions, both with Aux. 25
(and W4, through `Supp9B.w4Statement_of_aux25`) discharged:

* `w5Statement_of_remaining` (PROVE-W5-REST2's `Supp9D.w5Statement_of_g12Evol`): Lemma G12 in source form, W0b, Lemma
  7.7 at universe `0`, the two retained-pair carriers, W5's common-seed comparison;
* `w5Statement_of_remaining_w2` (`Supp9B.w5Statement_of_inputs_of_aux25`): W0a, W0b, W2, the common-seed comparison
  and the local-frame comparison.

The clause theorems `…_of_remaining` take W5 itself; the `…_of_remaining_g12` versions substitute the first reduction,
so that each lists only open named statements of the finest landed form.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Wire

open Sec7 Theorem15 Supp10 Restart Theorem15D5

/-! ### Theorem W5 from its remaining inputs -/

/-- **Theorem W5** from Lemma G12 (source form), W0b, Lemma 7.7 (universe `0`), the joint retained pair, the retained
local completion and the common-seed comparison (`Supp9D.w5Statement_of_g12Evol`; Aux. 25 and W0a discharged there). -/
theorem w5Statement_of_remaining (hG12 : Supp7.G12EvolStatement.{u}) (hW0b : Supp9.W0bStatement.{u})
    (h77 : Supp10.Lemma77Statement.{0}) (hJ : Supp9D.JointRetainedPairStatement.{u})
    (hL : Supp9D.RetainedLocalCompletionStatement.{u}) (hCS : Supp9.W5CommonSeedStatement.{u}) :
    W5Statement.{u} :=
  Supp9D.w5Statement_of_g12Evol hG12 hW0b h77 hJ hL hCS

/-- **Theorem W5** from W0a, W0b, W2, the common-seed and the local-frame comparisons
(`Supp9B.w5Statement_of_inputs_of_aux25` with Aux. 25 discharged; W4 is discharged there by
`Supp9B.w4Statement_of_aux25`). -/
theorem w5Statement_of_remaining_w2 (hW0a : Supp9.W0aStatement.{u}) (hW0b : Supp9.W0bStatement.{u})
    (hW2 : Supp9.W2Statement.{u}) (hCS : Supp9.W5CommonSeedStatement.{u})
    (hLF : Supp9.W5LocalFrameStatement.{u}) : W5Statement.{u} :=
  Supp9B.w5Statement_of_inputs_of_aux25 aux25Statement hW0a hW0b hW2 hCS hLF

/-- **Lemma W4** on the frozen carriers, unconditional (`Supp9B.w4Statement_of_aux25` with Aux. 25 proved). -/
theorem w4Statement : Supp9.W4Statement.{u} :=
  Supp9B.w4Statement_of_aux25 aux25Statement

/-! ### The three clauses, with W5 as an input -/

/-- **Theorem 1.5 (i)** (Specification p. 5), exactly the conclusion of the frozen `IsFlowLine.stays_right_of_lt`
(conditional helper): `Theorem15D5.stays_right_of_lt_of_d5` with Aux. 25, Aux. 84, G5 and the reality of finite
endpoints discharged. Remaining: W5, G7 + GB7a at a retained pair, W0b. -/
theorem stays_right_of_lt_of_remaining (hW5 : W5Statement.{u}) (hFH : G7GB7aFirstHitStatement.{u})
    (hW0b : Supp9.W0bStatement.{u})
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
  stays_right_of_lt_of_d5 hW5 hFH finiteEndpointRealStatement hW0b Supp9B.aux84Statement Supp9B.g5Statement
    aux25Statement hκ hκ4 b jumps hb hx hθ hh hη₁ hη₂

/-- **Theorem 1.5 (ii)** (Specification p. 5), exactly the conclusion of the frozen `IsFlowLine.merges` (conditional
helper): `Theorem15D5.merges_of_d5` with Aux. 25 discharged. Remaining: Lemma 7.7, the restart carrier, Lemma 7.5
(universes `u` and `0`). -/
theorem merges_of_remaining (h77 : Lemma77Statement.{u}) (hR : FirstContactRestartStatement.{u})
    (hL75 : Lemma75Statement.{u}) (hL75₀ : Lemma75Statement.{0})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (b : ℝ → ℝ) (jumps : Finset ℝ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    {x₁ x₂ θ : ℝ} (hx : x₂ ≤ x₁)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    (hη₁ : IsFlowLine κ b jumps x₁ θ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ P h η₂ ζ₂) :
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, IsInteriorAvailableContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) s t →
      AgreeAsCurvesAfter (η₁ ω) (ζ₁ ω) s (η₂ ω) (ζ₂ ω) t :=
  merges_of_d5 h77 hR hL75 hL75₀ aux25Statement hκ hκ4 b jumps hb hx hh hη₁ hη₂

/-- **Theorem 1.5 (iii)** (Specification p. 5), exactly the conclusion of the frozen `IsFlowLine.crosses_of_lt`
(conditional helper): `Theorem15D5.crosses_of_lt_of_d5` with Aux. 25 (both universes), Aux. 84, G5 and the reality of
finite endpoints discharged. Remaining: Lemma 7.7, the restart carrier with the active prime end, and on the canonical
space (universe `0`) W5, G7 + GB7a, W0b. -/
theorem crosses_of_lt_of_remaining (h77 : Lemma77Statement.{u}) (hR : FirstContactRestartLimStatement.{u})
    (hW5₀ : W5Statement.{0}) (hFH₀ : G7GB7aFirstHitStatement.{0}) (hW0b₀ : Supp9.W0bStatement.{0})
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
  crosses_of_lt_of_d5 h77 hR hW5₀ hFH₀ finiteEndpointRealStatement hW0b₀ Supp9B.aux84Statement
    Supp9B.g5Statement aux25Statement aux25Statement hκ hκ4 b jumps hb hx hθ hθπ hh hη₁ hη₂

/-! ### The three clauses, with W5 replaced by its finest landed reduction -/

/-- **Theorem 1.5 (i)** from the finest remaining inputs (conditional helper): `stays_right_of_lt_of_remaining` with
W5 from `w5Statement_of_remaining`. Remaining: G7 + GB7a, W0b, Lemma G12 (source form), Lemma 7.7 (universe `0`), the
joint retained pair, the retained local completion, W5's common-seed comparison. -/
theorem stays_right_of_lt_of_remaining_g12 (hFH : G7GB7aFirstHitStatement.{u}) (hW0b : Supp9.W0bStatement.{u})
    (hG12 : Supp7.G12EvolStatement.{u}) (h77₀ : Supp10.Lemma77Statement.{0})
    (hJ : Supp9D.JointRetainedPairStatement.{u}) (hL : Supp9D.RetainedLocalCompletionStatement.{u})
    (hCS : Supp9.W5CommonSeedStatement.{u})
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
  stays_right_of_lt_of_remaining (w5Statement_of_remaining hG12 hW0b h77₀ hJ hL hCS) hFH hW0b hκ hκ4 b jumps hb
    hx hθ hh hη₁ hη₂

/-- **Theorem 1.5 (iii)** from the finest remaining inputs (conditional helper): `crosses_of_lt_of_remaining` with
W5 on the canonical space from `w5Statement_of_remaining`. Remaining: Lemma 7.7 (universes `u` and `0`), the restart
carrier with the active prime end, and on the canonical space G7 + GB7a, W0b, Lemma G12 (source form), the joint
retained pair, the retained local completion, W5's common-seed comparison. -/
theorem crosses_of_lt_of_remaining_g12 (h77 : Lemma77Statement.{u}) (hR : FirstContactRestartLimStatement.{u})
    (hFH₀ : G7GB7aFirstHitStatement.{0}) (hW0b₀ : Supp9.W0bStatement.{0})
    (hG12₀ : Supp7.G12EvolStatement.{0}) (h77₀ : Supp10.Lemma77Statement.{0})
    (hJ₀ : Supp9D.JointRetainedPairStatement.{0}) (hL₀ : Supp9D.RetainedLocalCompletionStatement.{0})
    (hCS₀ : Supp9.W5CommonSeedStatement.{0})
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
  crosses_of_lt_of_remaining h77 hR (w5Statement_of_remaining hG12₀ hW0b₀ h77₀ hJ₀ hL₀ hCS₀) hFH₀ hW0b₀ hκ hκ4
    b jumps hb hx hθ hθπ hh hη₁ hη₂

end Wire

end InteractingSLE
