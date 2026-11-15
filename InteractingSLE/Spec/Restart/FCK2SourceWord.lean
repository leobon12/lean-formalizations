/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCK2Realize
import InteractingSLE.Spec.Restart.RetPlumbProofInputsWord

/-!
# Finite force types from the first-contact box mean identification

The chosen measurable word need not be the explicit geometric word. Compare
their mean pairings on each box and reuse the retained-word mean uniqueness
theorem to transfer the finite palette without controlling redundant entries.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn)
open QuantumZipper (chiC)

namespace InteractingSLE.Restart.FCPlumb
open RetAux79 Sec6 LocalSets
universe u

section Source
variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ}
  {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
  {d : PairData Ω} {u₀ : ℂ → ℝ}

/-- Two box mean identifications agree against every test simultaneously,
almost surely on the meeting set. The same actual local-set mean is used in
both identities, avoiding any disintegration of the source space. -/
theorem ae_mean_integrals_eq_of_boxMean
    (h75 : Theorem15.Lemma75Statement.{u}) (h77 : Supp10.Lemma77Statement.{u})
    (h56 : RetainedRangeEntranceStatement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hx : x₂ < x₁) (hθ : θ₁ < θ₂ + Real.pi)
    (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁)
    (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    (hd : d.IsMeasGood)
    (hu₀ : IsBoundedHarmonicExtension b jumps u₀) {β β' : Ω → BoundaryWord}
    (hm : IsBoxMeanIdentification κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd β)
    (hm' : IsBoxMeanIdentification κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd β') :
    ∀ᵐ ω ∂P, ω ∈ meetSet d → ∀ φ : TestOn upperHalfPlaneOpens,
      (∫ z, (β ω).mean z * φ z) = ∫ z, (β' ω).mean z * φ z := by
  have hbox (m : ℕ) : ∀ᵐ ω ∂P, ω ∈ meetBox d m → ∀ φ : TestOn upperHalfPlaneOpens,
      (∫ z, (β ω).mean z * φ z) = ∫ z, (β' ω).mean z * φ z := by
    obtain ⟨α₁, α₂, hc₁, hc₂, hm₁, hm₂, ha₁, ha₂, g, hg, _⟩ :=
      exists_fcUnion_marked_of_isFlowLine h75 h77 h56 hκ hκ4 hb hx hθ hh hη₁ hη₂ hu₀ m
    filter_upwards [hm m α₁ α₂ g hc₁ hc₂ hm₁ hm₂ ha₁ ha₂ hg,
      hm' m α₁ α₂ g hc₁ hc₂ hm₁ hm₂ ha₁ ha₂ hg] with ω he he' hω φ
    exact (he hω φ).symm.trans (he' hω φ)
  filter_upwards [ae_all_iff.2 hbox] with ω he hω φ
  obtain ⟨m, hm⟩ := mem_iUnion.1 hω
  exact he m hm φ

/-- The arbitrary sorted mean-identifying word has the same harmonic mean as
the explicit first-contact word, with its two source side heights. -/
theorem exists_ae_firstContact_word_mean
    (h75 : Theorem15.Lemma75Statement.{u}) (h77 : Supp10.Lemma77Statement.{u})
    (h56 : RetainedRangeEntranceStatement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hx : x₂ < x₁) (hθ : θ₁ < θ₂ + Real.pi)
    (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁)
    (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    (hd : d.IsMeasGood) (hζ₁ : d.ζ₁ = ζ₁) (hζ₂ : d.ζ₂ = ζ₂)
    (hae : ∀ᵐ ω ∂P, ω ∈ d.G ∧
      (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → d.η₁ ω s = η₁ ω s) ∧
      ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₂ ω → d.η₂ ω s = η₂ ω s)
    (hu₀ : IsBoundedHarmonicExtension b jumps u₀) {β : Ω → BoundaryWord}
    (hs : ∀ᵐ ω ∂P, ω ∈ meetSet d → (β ω).IsSorted)
    (hm : IsBoxMeanIdentification κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd β) :
    ∃ c₀ : BoundaryWord, ∀ᵐ ω ∂P, ω ∈ meetSet d →
      let c := d.word c₀ (-sleLambda κ - θ₂ * chiC κ) (sleLambda κ - θ₁ * chiC κ) ω
      c.IsSorted ∧ (β ω).IsSorted ∧ ∀ φ : TestOn upperHalfPlaneOpens,
        (∫ z, c.mean z * φ z) = ∫ z, (β ω).mean z * φ z := by
  obtain ⟨c₀, hc₀, hJ, hb₀⟩ := BoundaryWord.exists_fn_eq_strictMonoOn hb
  have hside := Sec7.SideHeightBox.isBoxSideLimit_of_flowLines h75 h77 h56 hκ hκ4 hb hx hθ hh
    hη₁ hη₂ hd hζ₁ hζ₂ hae hu₀
  have hword := isBoxMeanIdentification_word h75 h77 h56 hκ hκ4 hb hx hθ hh hη₁ hη₂ hd hζ₁ hζ₂
    hae hu₀ hc₀ hJ hb₀ hside
  refine ⟨c₀, ?_⟩
  filter_upwards [hs, ae_mean_integrals_eq_of_boxMean h75 h77 h56 hκ hκ4 hb hx hθ hh hη₁ hη₂
    hd hu₀ hword hm] with ω hsω he hω
  exact ⟨hd.word_isSorted (mem_meetSet_iff.1 hω).1 hc₀ _ _, hsω hω, he hω⟩

/-- Uniform finite force bounds for the chosen word on the actual source
coupling, at every angle simultaneously. Exceptional word values are ignored
only in the almost-sure conclusion. -/
theorem exists_ae_boundedForceTypes_of_boxMean
    (h75 : Theorem15.Lemma75Statement.{u}) (h77 : Supp10.Lemma77Statement.{u})
    (h56 : RetainedRangeEntranceStatement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hx : x₂ < x₁) (hθ : θ₁ < θ₂ + Real.pi)
    (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁)
    (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    (hd : d.IsMeasGood) (hζ₁ : d.ζ₁ = ζ₁) (hζ₂ : d.ζ₂ = ζ₂)
    (hae : ∀ᵐ ω ∂P, ω ∈ d.G ∧
      (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → d.η₁ ω s = η₁ ω s) ∧
      ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₂ ω → d.η₂ ω s = η₂ ω s)
    (hu₀ : IsBoundedHarmonicExtension b jumps u₀) {β : Ω → BoundaryWord}
    (hs : ∀ᵐ ω ∂P, ω ∈ meetSet d → (β ω).IsSorted)
    (hm : IsBoxMeanIdentification κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd β) :
    ∃ (N : ℕ) (heights : Finset ℝ), ∀ᵐ ω ∂P, ω ∈ meetSet d → ∀ θ : ℝ,
      HasBoundedForceType κ θ N (flowWeightPalette κ θ heights) (β ω) := by
  obtain ⟨c₀, he⟩ := exists_ae_firstContact_word_mean h75 h77 h56 hκ hκ4 hb hx hθ hh hη₁ hη₂ hd
    hζ₁ hζ₂ hae hu₀ hs hm
  refine ⟨2 * c₀.1 + 4, retainedHeightPalette c₀ (-sleLambda κ - θ₂ * chiC κ)
    (sleLambda κ - θ₁ * chiC κ) (-sleLambda κ - θ₂ * chiC κ) (sleLambda κ - θ₁ * chiC κ), ?_⟩
  filter_upwards [he] with ω heω hω θ
  obtain ⟨hc, hsω, heφ⟩ := heω hω
  obtain ⟨hn, hh⟩ := firstContact_word_length_heights d c₀
    (-sleLambda κ - θ₂ * chiC κ) (sleLambda κ - θ₁ * chiC κ) ω
  exact hasBoundedForceType_of_mean_integrals hc hsω heφ (hasBoundedForceType_of_heights hn hh)

end Source
end InteractingSLE.Restart.FCPlumb
