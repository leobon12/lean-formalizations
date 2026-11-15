/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCK2BdryWord

/-!
# Original-boundary readings of the source seed

The incident heights of the supplied mean-identifying word are determined
on all first-contact branches, including collapsed exposed intervals.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn)
open QuantumZipper (chiC)

namespace InteractingSLE.Restart.FCPlumb
open PiecewiseConstantBoundaryData
universe u

/-- All incident heights of the actual supplied β, almost surely on the
source meeting set. Collapsed sides read the original one-sided limit at
the corresponding filled-base endpoint. -/
theorem ae_incident_heights_of_boxMean
    (h75 : Theorem15.Lemma75Statement.{u}) (h77 : Supp10.Lemma77Statement.{u})
    (h56 : RetainedRangeEntranceStatement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {x₁ x₂ θ₁ θ₂ : ℝ} (hx : x₂ < x₁) (hθ : θ₁ < θ₂ + Real.pi)
    {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁)
    (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    {d : PairData Ω} (hd : d.IsMeasGood) (hζ₁ : d.ζ₁ = ζ₁) (hζ₂ : d.ζ₂ = ζ₂)
    (hae : ∀ᵐ ω ∂P, ω ∈ d.G ∧
      (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → d.η₁ ω s = η₁ ω s) ∧
      ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₂ ω → d.η₂ ω s = η₂ ω s)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {β : Ω → BoundaryWord} (hs : ∀ᵐ ω ∂P, ω ∈ meetSet d → (β ω).IsSorted)
    (hm : IsBoxMeanIdentification κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd β) :
    ∀ᵐ ω ∂P, ω ∈ meetSet d →
      leftLim (β ω).fn 0 = (if d.wordL ω = 0 then leftLim b (d.baseL ω)
        else -sleLambda κ - θ₂ * chiC κ) ∧
      rightLim (β ω).fn 0 = (if d.wordR ω = 0 then rightLim b (d.baseR ω)
        else sleLambda κ - θ₁ * chiC κ) := by
  obtain ⟨c₀, hc₀, hJ, hb₀⟩ := BoundaryWord.exists_fn_eq_strictMonoOn hb
  have hside := Sec7.SideHeightBox.isBoxSideLimit_of_flowLines h75 h77 h56 hκ hκ4 hb hx hθ hh
    hη₁ hη₂ hd hζ₁ hζ₂ hae hu₀
  have hword := isBoxMeanIdentification_word h75 h77 h56 hκ hκ4 hb hx hθ hh hη₁ hη₂ hd hζ₁ hζ₂
    hae hu₀ hc₀ hJ hb₀ hside
  have he := ae_mean_integrals_eq_of_boxMean h75 h77 h56 hκ hκ4 hb hx hθ hh hη₁ hη₂ hd hu₀ hword hm
  have eL : leftLim c₀.fn = leftLim b := leftLim_congr hb₀
  have eR : rightLim c₀.fn = rightLim b := rightLim_congr hb₀
  filter_upwards [hs, he] with ω hsω heω hω
  have hE := (mem_meetSet_iff.1 hω).1
  obtain ⟨hL, hR⟩ := word_limits_eq_of_mean_integrals
    (hd.word_isSorted hE hc₀ _ _) (hsω hω) (heω hω)
  rw [← hL, ← hR, word_leftLim_zero hd hE hc₀, word_rightLim_zero hd hE hc₀, eL, eR]
  exact ⟨rfl, rfl⟩

/-- Given the incident-height readings, source seed admissibility is
equivalent to the two original-boundary inequalities at collapsed sides.
The canonical exposed-side inequalities are discharged for both angles. -/
theorem admissible_iff_original_incident_bounds {κ θ₁ θ₂ θ : ℝ}
    (hκ : 0 < κ) (hκ4 : κ < 4) (hθ : θ₁ < θ₂ + Real.pi) (hθi : θ = θ₁ ∨ θ = θ₂)
    {b : ℝ → ℝ} {Ω : Type*} (d : PairData Ω) (ω : Ω) (β : BoundaryWord)
    (hL : leftLim β.fn 0 = if d.wordL ω = 0 then leftLim b (d.baseL ω)
      else -sleLambda κ - θ₂ * chiC κ)
    (hR : rightLim β.fn 0 = if d.wordR ω = 0 then rightLim b (d.baseR ω)
      else sleLambda κ - θ₁ * chiC κ) :
    ExplState.IsAdmissibleSeed κ (leftLim β.fn 0) (rightLim β.fn 0) θ ↔
      (d.wordL ω = 0 → leftLim b (d.baseL ω) + θ * chiC κ < sleLambda κ) ∧
      (d.wordR ω = 0 → -sleLambda κ < rightLim b (d.baseR ω) + θ * chiC κ) := by
  classical
  have hc := firstContact_exposedSides_admissible hκ hκ4 hθ
  have hcan : ExplState.IsAdmissibleSeed κ (-sleLambda κ - θ₂ * chiC κ)
      (sleLambda κ - θ₁ * chiC κ) θ := hθi.elim (fun he => he ▸ hc.1) (fun he => he ▸ hc.2)
  rcases hcan with ⟨hcleft, hcright⟩
  rw [ExplState.IsAdmissibleSeed, hL, hR]
  by_cases hleft : d.wordL ω = 0 <;> by_cases hright : d.wordR ω = 0 <;>
    simp only [hleft, hright, ite_true, ite_false, true_implies, false_implies,
      hcleft, hcright, true_and, and_true]

end InteractingSLE.Restart.FCPlumb
