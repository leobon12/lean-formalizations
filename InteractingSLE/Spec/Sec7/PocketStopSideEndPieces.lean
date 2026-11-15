/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketStopSideEndGeometry
import InteractingSLE.Spec.Sec7.PocketStopSideFinalPieces

/-!
# Incident reference selection for either Jordan pocket shape

PROVE-STRIPSYS38. Finite landings now follow from the incoming Jordan data in
both shapes. A corner exclusion is required only when the entry is outside H.
The named old-hull hypothesis below concerns filled hulls inside the pocket;
the no-visit identity for raw ranges does not establish it.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric Bornology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketStopSide

open PocketTraversal Lemma71C PocketStop PocketStopField PocketUnionPt PocketCoupling

/-- The remaining physical selection hypotheses, with the incoming inverse
extension proved in both Jordan cases and the interior-entry corner input removed. -/
theorem incidentReferenceCover_of_jordan_cases {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {A : Set Ω} {γ : Ω → ℝ → ℂ} {c : Ω → Chart} {C Fnow : Ω → Set ℂ}
    {Fold : ℚ≥0 → Ω → Set ℂ} {q : ℝ≥0} {J : Ω → Set ℝ} {faces : CoverRef → Ω → Set ℝ}
    {ψ : Ω → ℂ → ℂ} {seed : Ω → ℂ}
    (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω)) (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = C ω)
    (heq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (C ω))
    (hJordan : ∀ ω ∈ A,
      (∃ pole : ℂ, IsBounded (C ω) ∧ pole ∉ C ω ∧ Sec6.IsJordanCoord (C ω) pole (seed ω) (ψ ω)) ∨
        Sec6.IsJordanCoordInf (C ω) (seed ω) (ψ ω))
    (hclosure : ∀ ω ∈ A, closure (C ω) ⊆ H ∪ {seed ω})
    (hact : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) → activeDom A γ c q ω = C ω ∩ (H \ Fnow ω))
    (hCo : ∀ ω ∈ A, IsOpen (C ω))
    (hFo : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) → IsOpen (H \ Fnow ω))
    (hRealCorner : ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (γ ω) → seed ω ∉ H →
      ∀ ξ : ℝ, ξ ∉ J ω → ∀ p : ℂ,
        Tendsto (relChart c γ q ω).2.1 (𝓝[H] (ξ : ℂ)) (𝓝 p) → p ≠ seed ω)
    (hWallFaces : ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (γ ω) →
      ∀ ξ : ℝ, ξ ∉ J ω → ∀ p ∈ frontier (C ω), p ∉ Fnow ω →
        Tendsto (relChart c γ q ω).2.1 (𝓝[H] (ξ : ℂ)) (𝓝 p) →
          ∃ j : Fin 2, ξ ∈ faces (Sum.inl j) ω)
    (hOldHullSeparation : ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (γ ω) →
      ∀ ξ : ℝ, ξ ∉ J ω → ∀ p ∈ Fnow ω,
        Tendsto (relChart c γ q ω).2.1 (𝓝[H] (ξ : ℂ)) (𝓝 p) →
          ∃ (s : ℚ≥0) (r : ℝ), 0 < r ∧ ξ ∈ faces (Sum.inr s) ω ∧
            Fold s ω ⊆ Fnow ω ∧ Disjoint (C ω ∩ (Fnow ω \ Fold s ω)) (ball p r)) :
    IncidentReferenceCover P A γ c C Fnow Fold q J faces := by
  have hland : ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (γ ω) →
      ∀ ξ : ℝ, ξ ∉ J ω → ∃ p ∈ H, Tendsto (relChart c γ q ω).2.1 (𝓝[H] (ξ : ℂ)) (𝓝 p) := by
    filter_upwards [hRealCorner] with ω hcorner hω hq ξ hξ
    by_cases hseed : seed ω ∈ H
    · exact exists_relative_inverse_landing_of_jordan_cases_seed_mem_H (hγ ω hω) hq
        (hJordan ω hω) (hc ω hω) (hdom ω hω) (heq ω hω) (hclosure ω hω) hseed ξ
    · obtain ⟨E, hE, hEc, -⟩ := exists_inverse_extension_of_jordan_cases
        (hJordan ω hω) (hc ω hω) (hdom ω hω) (heq ω hω)
      obtain ⟨p, -, ht⟩ := exists_relative_inverse_landing_in_closure (hγ ω hω) hq (hc ω hω) hE hEc ξ
      exact ⟨p, relative_landing_mem_H_of_seed_exclusion (hγ ω hω) hq (hc ω hω)
        (hdom ω hω) (hclosure ω hω) ht (hcorner hω hq hseed ξ hξ p ht), ht⟩
  exact incidentReferenceCover_of_landings hγ hc hact hCo hFo hland hWallFaces hOldHullSeparation

end InteractingSLE.Sec7.PocketStopSide
