/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.G12Low
import InteractingSLE.Spec.Wire.Theorem15

/-!
# Theorem W5 and Theorem 1.5 (i)/(iii) without Lemma G12 as an input

Packet PROVE-G12C. Downstream, Lemma G12 enters Theorem W5 (and through it Theorem 1.5) only through Corollary W0a,
which is now unconditional (`Supp7.w0aStatement`, from the flow-line form `Supp7.g12FlowStatement`). These wrappers
restate the existing reductions with the `G12EvolStatement` (resp. `W0aStatement`) input discharged; their
conclusions are verbatim those of the wrapped theorems.

* `Supp9D.w5Statement_of_w0b`: `Supp9D.w5Statement_of_g12Evol` without `hG12`;
* `Wire.w5Statement_of_remaining_w2_w0b`: `Wire.w5Statement_of_remaining_w2` without `hW0a`;
* `Wire.stays_right_of_lt_of_remaining_w0b`, `Wire.crosses_of_lt_of_remaining_w0b`: the `…_remaining_g12` forms of
  Theorem 1.5 (i) and (iii) without `hG12`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Supp9D

/-- **Theorem W5** from W0b, Lemma 7.7, the two retained-pair carriers and the common-seed comparison (Aux. 25, W0a and
Lemma G12 discharged). -/
theorem w5Statement_of_w0b (hW0b : Supp9.W0bStatement.{u}) (h77 : Supp10.Lemma77Statement.{0})
    (hJ : JointRetainedPairStatement.{u}) (hL : RetainedLocalCompletionStatement.{u})
    (hCS : Supp9.W5CommonSeedStatement.{u}) : Theorem15.W5Statement.{u} :=
  w5Statement_of_inputs'' Theorem15.aux25Statement Supp7.w0aStatement hW0b h77 hJ hL hCS

end Supp9D

namespace Wire

open Sec7 Theorem15 Supp10 Restart Theorem15D5

/-- **Theorem W5** from W0b, W2, the common-seed and the local-frame comparisons (W0a discharged). -/
theorem w5Statement_of_remaining_w2_w0b (hW0b : Supp9.W0bStatement.{u}) (hW2 : Supp9.W2Statement.{u})
    (hCS : Supp9.W5CommonSeedStatement.{u}) (hLF : Supp9.W5LocalFrameStatement.{u}) : W5Statement.{u} :=
  w5Statement_of_remaining_w2 Supp7.w0aStatement hW0b hW2 hCS hLF

/-- **Theorem 1.5 (i)** from the finest remaining inputs without Lemma G12 (conditional helper):
`stays_right_of_lt_of_remaining_g12` with `hG12` discharged. -/
theorem stays_right_of_lt_of_remaining_w0b (hFH : G7GB7aFirstHitStatement.{u}) (hW0b : Supp9.W0bStatement.{u})
    (h77₀ : Supp10.Lemma77Statement.{0})
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
  stays_right_of_lt_of_remaining (Supp9D.w5Statement_of_w0b hW0b h77₀ hJ hL hCS) hFH hW0b hκ hκ4 b jumps hb
    hx hθ hh hη₁ hη₂

/-- **Theorem 1.5 (iii)** from the finest remaining inputs without Lemma G12 (conditional helper):
`crosses_of_lt_of_remaining_g12` with `hG12₀` discharged. -/
theorem crosses_of_lt_of_remaining_w0b (h77 : Lemma77Statement.{u}) (hR : FirstContactRestartLimStatement.{u})
    (hFH₀ : G7GB7aFirstHitStatement.{0}) (hW0b₀ : Supp9.W0bStatement.{0})
    (h77₀ : Supp10.Lemma77Statement.{0})
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
  crosses_of_lt_of_remaining h77 hR (Supp9D.w5Statement_of_w0b hW0b₀ h77₀ hJ₀ hL₀ hCS₀) hFH₀ hW0b₀ hκ hκ4
    b jumps hb hx hθ hθπ hh hη₁ hη₂

end Wire

end InteractingSLE
