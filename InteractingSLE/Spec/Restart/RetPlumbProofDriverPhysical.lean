/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.RetPlumbProofDriverObservable
import InteractingSLE.Spec.Restart.RetPlumbProofResidualSafe

/-!
# Retained driver reconstruction in the actual physical filtration

Packet PROVE-RETPLUMB. Combine physical-prefix reconstruction from current
killed histories with the measurable inverse-Loewner reader. The conclusion
contains no separate observation, clock or adapted-driver hypothesis.
-/
set_option autoImplicit false
noncomputable section
open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
namespace InteractingSLE.Restart.RetAux79
open Supp7 Sec7.Lemma76F DomainMarkov.Aux79
open LQGMetric (DistOn)
universe v
variable {Ω : Type v} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Killed observability and a globally continuous adapted driver in the time
change of the actual physical filtration follow from the landed flow lines. -/
theorem retDriver_observable_adapted_of_flowLines
    {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ}
    {h : Ω → DistOn upperHalfPlaneOpens} {η₁ η₂ η₁' η₂' : Ω → ℝ≥0 → ℂ}
    {ζ₁ ζ₂ : Ω → ℝ≥0∞} {G : ℝ≥0 → Set Ω} {u r : ℝ≥0} {F : Set Ω}
    {c₀ : BoundaryWord} {g₃ g₄ : ℝ}
    (hL75 : Theorem15.Lemma75Statement.{v}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁)
    (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    (ha₁ : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → η₁' ω s = η₁ ω s)
    (ha₂ : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₂ ω → η₂' ω s = η₂ ω s)
    (hd : ∀ r', (retFam G η₁' η₂' u r').IsMeasGood)
    (hGsub : G r ⊆ {ω | (u : ℝ≥0∞) < ζ₁ ω ∧ (r : ℝ≥0∞) < ζ₂ ω})
    (hGae : ∀ᵐ ω ∂P, (u : ℝ≥0∞) < ζ₁ ω → (r : ℝ≥0∞) < ζ₂ ω → ω ∈ G r)
    (hF : MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ u r] F) (hG : F ⊆ G r)
    (hp₁ : ∀ ω ∈ F, IsPathGood (η₁' ω) (ζ₁ ω) x₁)
    (hp₂ : ∀ ω ∈ F, IsPathGood (η₂' ω) (ζ₂ ω) x₂) (hx : x₂ < x₁)
    (hpair : ∀ ω ∈ F,
      Sec7.Lemma76Exit.IsDisjointPair (η₁' ω) (ζ₁ ω) u (η₂' ω) (ζ₂ ω) r)
    (hc₀ : StrictMonoOn c₀.2.1 (Iio c₀.1)) :
    ∃ hQa : ∀ t, Measurable[retPhysFiltration P η₁ η₂ ζ₁ ζ₂ u r t]
        (F.indicator (retClock G η₁' η₂' ζ₂ u r t)),
      RetKilledDriverObservable
        (timeChange (retPhysFiltration P η₁ η₂ ζ₁ ζ₂ u r)
          (fun t => F.indicator (retClock G η₁' η₂' ζ₂ u r t)) hQa)
        F G η₁' η₂' ζ₁ ζ₂ u r κ θ c₀ g₃ g₄ ∧
      RetAdaptedDriverExists
        (timeChange (retPhysFiltration P η₁ η₂ ζ₁ ζ₂ u r)
          (fun t => F.indicator (retClock G η₁' η₂' ζ₂ u r t)) hQa)
        F G η₁' η₂' ζ₁ ζ₂ u r κ θ c₀ g₃ g₄ := by
  have ho := retPrefixObservations_of_flowLines hL75 hκ hκ4 hb hh hη₁ hη₂ ha₁ ha₂
    (hd r) hGsub hGae hF hG hp₁ hp₂ hpair
  exact ⟨ho.measurable_clock (hd r) hG hp₂ hpair,
    ho.retKilledDriverObservable hd hG hp₁ hp₂ hx hpair hc₀ hκ,
    ho.retAdaptedDriverExists hd hG hp₁ hp₂ hx hpair hc₀ hκ⟩

end InteractingSLE.Restart.RetAux79
