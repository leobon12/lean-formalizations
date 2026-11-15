/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.G7Restart
import InteractingSLE.Spec.Supplement.G7Interface

/-!
# Theorem 7.12D and Theorem 1.5 (i)/(iii) from the clock-supplied retained-pair input

Packet PROVE-G7B. `G7Restart.lean` proves `RetainedPairRestartStatement` from `RetainedKernelClockStatement` (the
relative capacity clocks of both retained continuations are proved). This file restates PROVE-G7's wrappers
(`G7RetainedInterface.lean`) with that substitution; conclusions and remaining binders are verbatim.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Supp7

open Sec7 Theorem15 Supp10 Restart Theorem15D5 Wire

/-- **Theorem 7.12D** from the retained-pair restart input, W0b and W5 (conditional helper). -/
theorem thm712DStatement_of_kernelClock (hRP : RetainedKernelClockStatement.{u}) (hW0b : Supp9.W0bStatement.{u})
    (hW5 : W5Statement.{u}) : Thm712DStatement.{u} :=
  thm712DStatement_of_g7 (g7RetainedPairStatement_of_kernelClock hRP) hW0b hW5

/-- **Theorem 1.5 (i)** from the finest remaining inputs, with Lemma G7 and the joint carrier replaced by
`RetainedKernelClockStatement` (conditional helper). -/
theorem stays_right_of_lt_of_kernelClock (hRP : RetainedKernelClockStatement.{u}) (hW0b : Supp9.W0bStatement.{u})
    (hG12 : Supp7.G12EvolStatement.{u}) (h77₀ : Supp10.Lemma77Statement.{0})
    (hL : Supp9D.RetainedLocalCompletionStatement.{u}) (hCS : Supp9.W5CommonSeedStatement.{u})
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
  stays_right_of_lt_of_g7_g12 (g7RetainedPairStatement_of_kernelClock hRP) hW0b hG12 h77₀
    (jointRetainedPairStatement_of_kernelClock hRP) hL hCS hκ hκ4 b jumps hb hx hθ hh hη₁ hη₂

/-- **Theorem 1.5 (iii)** from the finest remaining inputs, with Lemma G7 and the joint carrier replaced by
`RetainedKernelClockStatement` (conditional helper). -/
theorem crosses_of_lt_of_kernelClock (h77 : Lemma77Statement.{u}) (hR : FirstContactRestartLimStatement.{u})
    (hRP₀ : RetainedKernelClockStatement.{0}) (hW0b₀ : Supp9.W0bStatement.{0})
    (hG12₀ : Supp7.G12EvolStatement.{0}) (h77₀ : Supp10.Lemma77Statement.{0})
    (hL₀ : Supp9D.RetainedLocalCompletionStatement.{0}) (hCS₀ : Supp9.W5CommonSeedStatement.{0})
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
  crosses_of_lt_of_g7_g12 h77 hR (g7RetainedPairStatement_of_kernelClock hRP₀) hW0b₀ hG12₀ h77₀
    (jointRetainedPairStatement_of_kernelClock hRP₀) hL₀ hCS₀ hκ hκ4 b jumps hb hx hθ hθπ hh hη₁ hη₂

end Supp7

end InteractingSLE
