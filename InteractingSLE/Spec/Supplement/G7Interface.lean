/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB7aCmp
import InteractingSLE.Spec.Wire.Theorem15

/-!
# Theorem 1.5's interface 4 from Lemma G7 alone

Packet PROVE-GB7A3. With Lemma GB7a proved (`Supp8.gb7aFlowStatement`, `GB7aCmp.lean`), the first-hit interface
`Theorem15D5.G7GB7aFirstHitStatement` follows from Lemma G7 at the retained pair (`Supp7.G7RetainedPairStatement`)
alone (`Supp7.g7GB7aFirstHitStatement_of_g7`). This file restates PROVE-WIRE1's conditional helpers for clauses (i) and
(iii) of Theorem 1.5 with that substitution: each is a one-term application, with the conclusion and the remaining
binders verbatim and the input `G7GB7aFirstHitStatement` replaced by `G7RetainedPairStatement`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Supp7

open Sec7 Theorem15 Supp10 Restart Theorem15D5 Wire

/-- **Theorem 7.12D** (critical-angle exclusion of interior contacts; supplement §10.1, p. 543) from Lemma G7 at the
retained pair, W0b and W5 (conditional helper): `Theorem15D5.thm712DStatement_of_d5` with GB7a, Aux. 84, G5, Aux. 25
and the reality of finite continuation endpoints discharged. -/
theorem thm712DStatement_of_g7 (hG7 : G7RetainedPairStatement.{u}) (hW0b : Supp9.W0bStatement.{u})
    (hW5 : W5Statement.{u}) : Thm712DStatement.{u} :=
  thm712DStatement_of_d5 (g7GB7aFirstHitStatement_of_g7 hG7) finiteEndpointRealStatement hW0b hW5
    Supp9B.aux84Statement Supp9B.g5Statement aux25Statement

/-- **Theorem 1.5 (i)** (conditional helper), `Wire.stays_right_of_lt_of_remaining` with interface 4 from Lemma G7
(GB7a proved). Remaining: W5, Lemma G7 at the retained pair, W0b. -/
theorem stays_right_of_lt_of_g7 (hW5 : W5Statement.{u}) (hG7 : G7RetainedPairStatement.{u})
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
  Wire.stays_right_of_lt_of_remaining hW5 (g7GB7aFirstHitStatement_of_g7 hG7) hW0b hκ hκ4 b jumps hb hx hθ hh hη₁ hη₂

/-- **Theorem 1.5 (iii)** (conditional helper), `Wire.crosses_of_lt_of_remaining` with interface 4 from Lemma G7
(GB7a proved). -/
theorem crosses_of_lt_of_g7 (h77 : Lemma77Statement.{u}) (hR : FirstContactRestartLimStatement.{u})
    (hW5₀ : W5Statement.{0}) (hG7₀ : G7RetainedPairStatement.{0}) (hW0b₀ : Supp9.W0bStatement.{0})
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
  Wire.crosses_of_lt_of_remaining h77 hR hW5₀ (g7GB7aFirstHitStatement_of_g7 hG7₀) hW0b₀ hκ hκ4 b jumps hb hx hθ hθπ hh
    hη₁ hη₂

/-- **Theorem 1.5 (i)** from the finest remaining inputs (conditional helper),
`Wire.stays_right_of_lt_of_remaining_g12` with interface 4 from Lemma G7 (GB7a proved). -/
theorem stays_right_of_lt_of_g7_g12 (hG7 : G7RetainedPairStatement.{u}) (hW0b : Supp9.W0bStatement.{u})
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
  Wire.stays_right_of_lt_of_remaining_g12 (g7GB7aFirstHitStatement_of_g7 hG7) hW0b hG12 h77₀ hJ hL hCS hκ hκ4 b jumps hb
    hx hθ hh hη₁ hη₂

/-- **Theorem 1.5 (iii)** from the finest remaining inputs (conditional helper),
`Wire.crosses_of_lt_of_remaining_g12` with interface 4 from Lemma G7 (GB7a proved). -/
theorem crosses_of_lt_of_g7_g12 (h77 : Lemma77Statement.{u}) (hR : FirstContactRestartLimStatement.{u})
    (hG7₀ : G7RetainedPairStatement.{0}) (hW0b₀ : Supp9.W0bStatement.{0})
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
  Wire.crosses_of_lt_of_remaining_g12 h77 hR (g7GB7aFirstHitStatement_of_g7 hG7₀) hW0b₀ hG12₀ h77₀ hJ₀ hL₀ hCS₀ hκ hκ4 b
    jumps hb hx hθ hθπ hh hη₁ hη₂

end Supp7

end InteractingSLE
