/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCK2Source

/-!
# First-contact seed inequalities on the two exposed sides

The supplied measurable word is identified by its mean, rather than by its
representation. At noncollapsed exposed sides its incident heights are the
two canonical side heights. Collapsed sides remain a separate boundary case.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn)
open QuantumZipper (chiC)

namespace InteractingSLE.Restart.FCPlumb
open PiecewiseConstantBoundaryData RetAux79
universe u

/-- Incident heights are unchanged by equality of all harmonic mean pairings. -/
theorem word_limits_eq_of_mean_integrals {c e : BoundaryWord}
    (hc : c.IsSorted) (he : e.IsSorted)
    (hm : ∀ φ : TestOn upperHalfPlaneOpens,
      (∫ z, c.mean z * φ z) = ∫ z, e.mean z * φ z) :
    leftLim c.fn = leftLim e.fn ∧ rightLim c.fn = rightLim e.fn := by
  have hf := word_fn_eq_of_mean_integrals hc he hm
  exact ⟨leftLim_congr hf, rightLim_congr hf⟩

variable {Ω : Type*} [MeasurableSpace Ω] {d : PairData Ω}

/-- Both incident heights of the explicit box word, when both exposed
intervals have positive length. No hypothesis on original boundary heights
is needed in this case. -/
theorem word_limits_zero_of_exposed (hd : d.IsMeasGood) {ω : Ω} (hE : ω ∈ d.E)
    {c₀ : BoundaryWord} (hc₀ : StrictMonoOn c₀.2.1 (Iio c₀.1))
    (hL hR : ℝ) (hleft : d.wordL ω < 0) (hright : 0 < d.wordR ω) :
    leftLim (d.word c₀ hL hR ω).fn 0 = hL ∧
      rightLim (d.word c₀ hL hR ω).fn 0 = hR := by
  constructor
  · exact Sec4.leftLim_eq_of_forall hleft fun _ hy =>
      hd.word_fn_of_mem_Ioo_left hE hc₀ hL hR hy.1 hy.2
  · exact Sec4.rightLim_eq_of_forall hright fun _ hy =>
      hd.word_fn_of_mem_Ioo_right hE hc₀ hL hR hy.1 hy.2

/-- The mean-identifying word is admissible at both continuation angles on
the exposed-side branch. This assertion concerns the actual supplied β. -/
theorem ae_admissible_of_boxMean_exposed
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
    ∀ᵐ ω ∂P, ω ∈ meetSet d → d.wordL ω < 0 → 0 < d.wordR ω →
      ExplState.IsAdmissibleSeed κ (leftLim (β ω).fn 0) (rightLim (β ω).fn 0) θ₁ ∧
      ExplState.IsAdmissibleSeed κ (leftLim (β ω).fn 0) (rightLim (β ω).fn 0) θ₂ := by
  obtain ⟨c₀, hc₀, hJ, hb₀⟩ := BoundaryWord.exists_fn_eq_strictMonoOn hb
  have hside := Sec7.SideHeightBox.isBoxSideLimit_of_flowLines h75 h77 h56 hκ hκ4 hb hx hθ hh
    hη₁ hη₂ hd hζ₁ hζ₂ hae hu₀
  have hword := isBoxMeanIdentification_word h75 h77 h56 hκ hκ4 hb hx hθ hh hη₁ hη₂ hd hζ₁ hζ₂
    hae hu₀ hc₀ hJ hb₀ hside
  have he := ae_mean_integrals_eq_of_boxMean h75 h77 h56 hκ hκ4 hb hx hθ hh hη₁ hη₂ hd hu₀ hword hm
  filter_upwards [hs, he] with ω hsω heω hω hL hR
  have hE := (mem_meetSet_iff.1 hω).1
  obtain ⟨eL, eR⟩ := word_limits_eq_of_mean_integrals
    (hd.word_isSorted hE hc₀ _ _) (hsω hω) (heω hω)
  obtain ⟨cL, cR⟩ := word_limits_zero_of_exposed hd hE hc₀
    (-sleLambda κ - θ₂ * chiC κ) (sleLambda κ - θ₁ * chiC κ) hL hR
  rw [← eL, ← eR, cL, cR]
  exact firstContact_exposedSides_admissible hκ hκ4 hθ

end InteractingSLE.Restart.FCPlumb
