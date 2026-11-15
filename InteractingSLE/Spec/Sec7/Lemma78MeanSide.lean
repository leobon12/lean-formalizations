/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma78MeanWord

/-!
# Lemma 7.8's mean formula for the explicit word, from the exposed-side heights

Packet PROVE-PRIMEEND2. With the explicit boundary word `d.word c₀ hL hR` (`Lemma78MeanWord`), the chart boundary
statement `IsBoxChartBoundaryLimit` splits along the real chart line into

* `(−∞, L)` and `(R, ∞)`: untouched original real boundary; proved here from the real-boundary decay
  (`ae_tendsto_chart_word_of_untouched`);
* `(L, 0)` and `(0, R)`: the exposed left side of the second prefix and right side of the first one, where the heights
  are `hL = −λ − θ₂χ` and `hR = λ − θ₁χ` (Lemma 7.8's proof, p. 293: the single-path comparisons at the ordinary
  stops); this part is the named statement `IsBoxSideLimit`.

## Main results

* `ae_tendsto_chart_word_of_untouched`: the untouched part, for every cap, every pair of capped versions and every
  version of the union mean;
* `IsBoxSideLimit`: the exposed-side heights in the chart;
* `isBoxChartBoundaryLimit_word`: `IsBoxSideLimit` gives `IsBoxChartBoundaryLimit` for the word;
* **`isBoxPointwiseMean_word`**, **`isBoxMeanIdentification_word`**: Lemma 7.8's mean formula on every box for the
  explicit word, from `IsBoxSideLimit` (and the inputs of the glued (R1)).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

universe u

namespace InteractingSLE

namespace Restart

open LQGMetric (DistOn TestOn)
open LocalSets

section Side

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **The exposed-side heights in the first-contact chart** (Lemma 7.8's proof, p. 293: "The relative zero-GFF
boundary comparison, with separation from the added range, identifies its mean germ there with the known single-path
germ at `r`. This proves the required height on every exposed side except at the finite endpoints"). For every cap,
every pair of capped versions and every version `g` of the union mean, almost surely on the box, for every harmonic
representative `v` of `g`: outside a finite set of real chart points, `(v + 𝔥₀ + χ arg φ′) ∘ ψ` tends to `hL` at the
points of `(L, 0)` and to `hR` at the points of `(0, R)`. -/
def IsBoxSideLimit (κ : ℝ) (P : Measure Ω) (h : Ω → DistOn upperHalfPlaneOpens) (η₁ η₂ : Ω → ℝ≥0 → ℂ)
    (ζ₁ ζ₂ : Ω → ℝ≥0∞) (u₀ : ℂ → ℝ) (d : PairData Ω) (hL hR : ℝ) : Prop :=
  ∀ (m : ℕ) (ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ) (g : Ω → DistOn upperHalfPlaneOpens),
    (∀ ω, Continuous (ηc₁ ω)) → (∀ ω, Continuous (ηc₂ ω)) → (∀ t, Measurable fun ω => ηc₁ ω t) →
    (∀ t, Measurable fun ω => ηc₂ ω t) → (∀ᵐ ω ∂P, ∀ t, ηc₁ ω t = η₁ ω (capTime m (ζ₁ ω) t)) →
    (∀ᵐ ω ∂P, ∀ t, ηc₂ ω t = η₂ ω (capTime m (ζ₂ ω) t)) →
    IsLocalSetMean (fcUnion ηc₁ ηc₂) (WholeField.centredField h u₀) P g →
    ∀ᵐ ω ∂P, ω ∈ meetBox d m → ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ fcUnion ηc₁ ηc₂ ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ fcUnion ηc₁ ηc₂ ω → g ω φ = ∫ z, v z * φ z) →
      ∃ E : Set ℝ, E.Finite ∧ ∀ w : ℝ, w ∉ E →
        (d.wordL ω < w → w < 0 →
          Tendsto (fun z => v (d.inv ω z) + u₀ (d.inv ω z) + QuantumZipper.chiC κ * d.lift ω (d.inv ω z))
            (𝓝[H] (w : ℂ)) (𝓝 hL)) ∧
        (0 < w → w < d.wordR ω →
          Tendsto (fun z => v (d.inv ω z) + u₀ (d.inv ω z) + QuantumZipper.chiC κ * d.lift ω (d.inv ω z))
            (𝓝[H] (w : ℂ)) (𝓝 hR))

end Side

section Untouched

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {η₁ η₂ : Ω → ℝ≥0 → ℂ}
  {ζ₁ ζ₂ : Ω → ℝ≥0∞}

/-- **The untouched part of the chart boundary values for the explicit word**: off `[L, R]`, at chart points that are
not jumps of the word, `(v + 𝔥₀ + χ arg φ′) ∘ ψ` tends to the word's datum (the original datum at `ψ(w)`). -/
theorem ae_tendsto_chart_word_of_untouched (hL75 : Theorem15.Lemma75Statement.{u})
    (hL77 : Supp10.Lemma77Statement.{u}) (hA56 : RetainedRangeEntranceStatement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hx : x₂ < x₁) (hθ : θ₁ < θ₂ + Real.pi)
    (hh : IsGFFWithBoundaryData P h b jumps) (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁)
    (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂) {d : PairData Ω} (hd : d.IsMeasGood) (hζ₁ : d.ζ₁ = ζ₁)
    (hζ₂ : d.ζ₂ = ζ₂)
    (hae : ∀ᵐ ω ∂P, ω ∈ d.G ∧ (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → d.η₁ ω s = η₁ ω s) ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ₂ ω → d.η₂ ω t = η₂ ω t)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) {c₀ : BoundaryWord}
    (hc₀ : StrictMonoOn c₀.2.1 (Iio c₀.1)) (hc₀J : c₀.jumps = jumps) (hc₀b : ∀ y ∉ jumps, c₀.fn y = b y)
    (hL hR : ℝ) (m : ℕ) {ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ}
    {g : Ω → DistOn upperHalfPlaneOpens} (hc₁ : ∀ ω, Continuous (ηc₁ ω)) (hc₂ : ∀ ω, Continuous (ηc₂ ω))
    (hm₁ : ∀ t, Measurable fun ω => ηc₁ ω t) (hm₂ : ∀ t, Measurable fun ω => ηc₂ ω t)
    (hag₁ : ∀ᵐ ω ∂P, ∀ t, ηc₁ ω t = η₁ ω (capTime m (ζ₁ ω) t))
    (hag₂ : ∀ᵐ ω ∂P, ∀ t, ηc₂ ω t = η₂ ω (capTime m (ζ₂ ω) t))
    (hg : IsLocalSetMean (fcUnion ηc₁ ηc₂) (WholeField.centredField h u₀) P g) :
    ∀ᵐ ω ∂P, ω ∈ meetBox d m → ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ fcUnion ηc₁ ηc₂ ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ fcUnion ηc₁ ηc₂ ω → g ω φ = ∫ z, v z * φ z) →
      ∀ w : ℝ, (w < d.wordL ω ∨ d.wordR ω < w) → w ∉ (d.word c₀ hL hR ω).jumps →
        Tendsto (fun z => v (d.inv ω z) + u₀ (d.inv ω z) + QuantumZipper.chiC κ * d.lift ω (d.inv ω z))
          (𝓝[H] (w : ℂ)) (𝓝 ((d.word c₀ hL hR ω).fn w)) := by
  filter_upwards [ae_tendsto_chart_of_untouched hL75 hL77 hA56 hκ hκ4 hb hx hθ hh hη₁ hη₂ hd hζ₁ hζ₂ hae hu₀ m
    hc₁ hc₂ hm₁ hm₂ hag₁ hag₂ hg] with ω hω hbox v hv hvrep w hw hwj
  have hE : ω ∈ d.E := (mem_meetBox_iff.1 hbox).1
  rcases hw with hw | hw
  · obtain ⟨hxa, hψ, -⟩ := hd.inv_of_lt_wordL hE hw
    obtain ⟨ρ, hρ, hK, -⟩ := hd.exists_ball_of_lt_baseL hxa
    have hxj : (d.inv ω w).re ∉ jumps := fun hj =>
      hwj (hd.mem_word_jumps_of_lt_wordL hE hc₀ hL hR hw (hc₀J ▸ hj))
    have hlim := hω hbox v hv hvrep w (by rw [hψ]; simp) ⟨ρ, hρ, by rw [hψ]; exact hK⟩ hxj
    rwa [hd.word_fn_of_lt_wordL hE hc₀ hL hR hw, hc₀b _ hxj]
  · obtain ⟨hxb, hψ, -⟩ := hd.inv_of_wordR_lt hE hw
    obtain ⟨ρ, hρ, hK, -⟩ := hd.exists_ball_of_baseR_lt hxb
    have hxj : (d.inv ω w).re ∉ jumps := fun hj =>
      hwj (hd.mem_word_jumps_of_wordR_lt hE hc₀ hL hR hw (hc₀J ▸ hj))
    have hlim := hω hbox v hv hvrep w (by rw [hψ]; simp) ⟨ρ, hρ, by rw [hψ]; exact hK⟩ hxj
    rwa [hd.word_fn_of_wordR_lt hE hc₀ hL hR hw, hc₀b _ hxj]

/-- **The chart boundary values of the explicit word from the exposed-side heights.** -/
theorem isBoxChartBoundaryLimit_word (hL75 : Theorem15.Lemma75Statement.{u})
    (hL77 : Supp10.Lemma77Statement.{u}) (hA56 : RetainedRangeEntranceStatement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hx : x₂ < x₁) (hθ : θ₁ < θ₂ + Real.pi)
    (hh : IsGFFWithBoundaryData P h b jumps) (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁)
    (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂) {d : PairData Ω} (hd : d.IsMeasGood) (hζ₁ : d.ζ₁ = ζ₁)
    (hζ₂ : d.ζ₂ = ζ₂)
    (hae : ∀ᵐ ω ∂P, ω ∈ d.G ∧ (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → d.η₁ ω s = η₁ ω s) ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ₂ ω → d.η₂ ω t = η₂ ω t)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) {c₀ : BoundaryWord}
    (hc₀ : StrictMonoOn c₀.2.1 (Iio c₀.1)) (hc₀J : c₀.jumps = jumps) (hc₀b : ∀ y ∉ jumps, c₀.fn y = b y)
    {hL hR : ℝ} (hside : IsBoxSideLimit κ P h η₁ η₂ ζ₁ ζ₂ u₀ d hL hR) :
    IsBoxChartBoundaryLimit κ P h η₁ η₂ ζ₁ ζ₂ u₀ d (d.word c₀ hL hR) := by
  intro m ηc₁ ηc₂ g hc₁ hc₂ hm₁ hm₂ hag₁ hag₂ hg
  filter_upwards [ae_tendsto_chart_word_of_untouched hL75 hL77 hA56 hκ hκ4 hb hx hθ hh hη₁ hη₂ hd hζ₁ hζ₂ hae hu₀
    hc₀ hc₀J hc₀b hL hR m hc₁ hc₂ hm₁ hm₂ hag₁ hag₂ hg, hside m ηc₁ ηc₂ g hc₁ hc₂ hm₁ hm₂ hag₁ hag₂ hg]
    with ω hunt hsd hbox v hv hvrep
  have hE : ω ∈ d.E := (mem_meetBox_iff.1 hbox).1
  obtain ⟨E, hEf, hEs⟩ := hsd hbox v hv hvrep
  refine ⟨E ∪ {d.wordL ω, 0, d.wordR ω} ∪ ↑(d.word c₀ hL hR ω).jumps,
    (hEf.union (toFinite _)).union (Finset.finite_toSet _), fun w hw => ?_⟩
  simp only [mem_union, mem_insert_iff, mem_singleton_iff, Finset.mem_coe, not_or] at hw
  obtain ⟨⟨hwE, hwL, hw0, hwR⟩, hwj⟩ := hw
  rcases lt_or_gt_of_ne hwL with h1 | h1
  · exact hunt hbox v hv hvrep w (Or.inl h1) hwj
  rcases lt_or_gt_of_ne hwR with h2 | h2
  · rcases lt_or_gt_of_ne hw0 with h3 | h3
    · rw [hd.word_fn_of_mem_Ioo_left hE hc₀ hL hR h1 h3]
      exact (hEs w hwE).1 h1 h3
    · rw [hd.word_fn_of_mem_Ioo_right hE hc₀ hL hR h3 h2]
      exact (hEs w hwE).2 h3 h2
  · exact hunt hbox v hv hvrep w (Or.inr h2) hwj

/-- **Lemma 7.8's mean formula on every box for the explicit word** (`IsBoxPointwiseMean`), from the exposed-side
heights (`IsBoxSideLimit`) and the inputs of the glued (R1) (Lemmas 7.5, 7.7, Aux. 56 at first entrances). The word is
built from any strictly sorted word `c₀` representing the original data. -/
theorem isBoxPointwiseMean_word (hL75 : Theorem15.Lemma75Statement.{u})
    (hL77 : Supp10.Lemma77Statement.{u}) (hA56 : RetainedRangeEntranceStatement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hx : x₂ < x₁) (hθ : θ₁ < θ₂ + Real.pi)
    (hh : IsGFFWithBoundaryData P h b jumps) (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁)
    (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂) {d : PairData Ω} (hd : d.IsMeasGood) (hζ₁ : d.ζ₁ = ζ₁)
    (hζ₂ : d.ζ₂ = ζ₂)
    (hae : ∀ᵐ ω ∂P, ω ∈ d.G ∧ (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → d.η₁ ω s = η₁ ω s) ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ₂ ω → d.η₂ ω t = η₂ ω t)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) {c₀ : BoundaryWord}
    (hc₀ : StrictMonoOn c₀.2.1 (Iio c₀.1)) (hc₀J : c₀.jumps = jumps) (hc₀b : ∀ y ∉ jumps, c₀.fn y = b y)
    {hL hR : ℝ} (hside : IsBoxSideLimit κ P h η₁ η₂ ζ₁ ζ₂ u₀ d hL hR) :
    IsBoxPointwiseMean κ P h η₁ η₂ ζ₁ ζ₂ u₀ d (d.word c₀ hL hR) :=
  isBoxPointwiseMean_of_chartBoundaryLimit hL75 hL77 hA56 hκ hκ4 hb hx hθ hh hη₁ hη₂ hd hζ₁ hζ₂ hae hu₀
    (Eventually.of_forall fun ω hω => by
      obtain ⟨m, hm⟩ := mem_iUnion.1 hω
      exact hd.word_isSorted (mem_meetBox_iff.1 hm).1 hc₀ hL hR)
    (isBoxChartBoundaryLimit_word hL75 hL77 hA56 hκ hκ4 hb hx hθ hh hη₁ hη₂ hd hζ₁ hζ₂ hae hu₀ hc₀ hc₀J hc₀b hside)

/-- **The mean part of `FirstContactWordKernelStatement` for the explicit word** (the chart form
`IsBoxMeanIdentification` used by the glued (R1)), from the exposed-side heights. -/
theorem isBoxMeanIdentification_word (hL75 : Theorem15.Lemma75Statement.{u})
    (hL77 : Supp10.Lemma77Statement.{u}) (hA56 : RetainedRangeEntranceStatement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hx : x₂ < x₁) (hθ : θ₁ < θ₂ + Real.pi)
    (hh : IsGFFWithBoundaryData P h b jumps) (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁)
    (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂) {d : PairData Ω} (hd : d.IsMeasGood) (hζ₁ : d.ζ₁ = ζ₁)
    (hζ₂ : d.ζ₂ = ζ₂)
    (hae : ∀ᵐ ω ∂P, ω ∈ d.G ∧ (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → d.η₁ ω s = η₁ ω s) ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ₂ ω → d.η₂ ω t = η₂ ω t)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) {c₀ : BoundaryWord}
    (hc₀ : StrictMonoOn c₀.2.1 (Iio c₀.1)) (hc₀J : c₀.jumps = jumps) (hc₀b : ∀ y ∉ jumps, c₀.fn y = b y)
    {hL hR : ℝ} (hside : IsBoxSideLimit κ P h η₁ η₂ ζ₁ ζ₂ u₀ d hL hR) :
    IsBoxMeanIdentification κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd (d.word c₀ hL hR) :=
  isBoxMeanIdentification_of_pointwise hd
    (isBoxPointwiseMean_word hL75 hL77 hA56 hκ hκ4 hb hx hθ hh hη₁ hη₂ hd hζ₁ hζ₂ hae hu₀ hc₀ hc₀J hc₀b hside)

end Untouched

end Restart

end InteractingSLE
