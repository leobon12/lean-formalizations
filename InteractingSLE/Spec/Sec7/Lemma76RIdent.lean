/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma76GMain

/-!
# The mean identification for the explicit measurable word of retained data

Packet PROVE-RETAUX79C. LEMMA76G proved the mean identification of Lemma 7.6 for a word `β` measurable for the retained
σ-algebra (`Lemma76G.lemma76MeanIdentStatement_of_lemma75`, existential). The later lines of the retained
continuation need it for the explicit word `wordM d …` of the retained data `d` of the line (whose boundary data the
continuation's force data match, `RetAux79.exists_retLine_facts_R`). Its proof does not use the measurability, so it
applies verbatim:

* `ae_wordM_eq_zoneWord`: at a disjoint pair the measurable word of `d` is the truncated zone word, `ω` is in the chart
  event and LEMMA76G's setting holds (as `hword` in the proof of `lemma76ChartBoundaryStatement_of_lemma75`);
* **`isRetChartBoundaryLimit_wordM`**: its datum is the boundary value of the conditional mean in the retained chart
  outside finitely many chart points (the proof of `lemma76ChartBoundaryStatement_of_lemma75`, copied with `β` the
  word of `d` itself);
* **`isRetMeanIdent_wordM`**: the mean identification `IsRetMeanIdent` for `wordM d …`; `ae_isSorted_wordM`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

universe u

namespace InteractingSLE

namespace Sec7

namespace Lemma76G

open LQGMetric (DistOn TestOn)
open LocalSets Sec6 Restart Supp7 Lemma76F SideHeightBox

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ} {Ω : Type u} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {η₁ η₂ : Ω → ℝ≥0 → ℂ}
  {ζ₁ ζ₂ : Ω → ℝ≥0∞} {d : RetData Ω}

/-- **At a disjoint pair the measurable word of the retained data is the truncated zone word** (and `ω` is in the chart
event, LEMMA76G's setting holds, and the retained union is the union of the prefixes of the paths). -/
theorem ae_wordM_eq_zoneWord (hκ : 0 < κ) (hκ4 : κ < 4) (hx : x₂ < x₁)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂) (hd : d.IsMeasGood)
    (hag : ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
      (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t)
    {c₀ : BoundaryWord} (hc₀ : StrictMonoOn c₀.2.1 (Iio c₀.1)) (g₁ g₂ g₃ g₄ : ℝ) :
    ∀ᵐ ω ∂P, Lemma76Exit.IsDisjointPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r →
      wordM d c₀ g₁ g₂ g₃ g₄ ω = ((zoneData (d.fwd ω) (η₁ ω) d.u (η₂ ω) d.r).word c₀ g₁ g₂ g₃ g₄).trunc ∧
      IsSetting (η₁ ω) (ζ₁ ω) x₁ d.u (η₂ ω) (ζ₂ ω) x₂ d.r (d.fwd ω) (d.inv ω) (d.lift ω) ∧ ω ∈ d.E ∧
      d.K ω = prefixSet (η₁ ω) d.u (η₂ ω) d.r := by
  filter_upwards [hag, ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₁,
    ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₂] with ω hagω hp₁ hp₂ hp
  obtain ⟨hG, a₁, a₂⟩ := hagω hp.1 hp.2.1
  have hE : ω ∈ d.E := mem_E_of_isDisjointPair hd hG a₁ a₂ hp
  have hC : IsRetChart (η₁ ω) d.u (η₂ ω) d.r (d.fwd ω) (d.inv ω) (d.lift ω) :=
    (isRetChart_congr a₁ a₂).1 (hd.isRetChart hE).2
  have hs : IsSetting (η₁ ω) (ζ₁ ω) x₁ d.u (η₂ ω) (ζ₂ ω) x₂ d.r (d.fwd ω) (d.inv ω) (d.lift ω) :=
    ⟨hp₁, hp₂, hx, hp, hC⟩
  refine ⟨wordM_eq_of_setting hd hE hs a₁ a₂ hc₀ g₁ g₂ g₃ g₄, hs, hE, ?_⟩
  rw [RetData.K_of_mem hE]
  exact prefixSet_congr' a₁ a₂

/-- **The datum of the measurable word of the retained data is the boundary value of the conditional mean in the
retained chart** outside finitely many chart points (the proof of `lemma76ChartBoundaryStatement_of_lemma75`, copied
with the word of `d` itself in place of the word of its stopped capped copy). -/
theorem isRetChartBoundaryLimit_wordM (hL75 : Theorem15.Lemma75Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hx : x₂ < x₁) (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂) (hd : d.IsMeasGood)
    (hag : ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
      (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) {c₀ : BoundaryWord}
    (hc₀ : StrictMonoOn c₀.2.1 (Iio c₀.1)) (hc₀J : c₀.jumps = jumps) (hc₀b : ∀ y ∉ jumps, c₀.fn y = b y) :
    IsRetChartBoundaryLimit κ P h η₁ η₂ ζ₁ ζ₂ u₀ d
      (wordM d c₀ (-sleLambda κ - θ₂ * QuantumZipper.chiC κ) (sleLambda κ - θ₂ * QuantumZipper.chiC κ)
        (-sleLambda κ - θ₁ * QuantumZipper.chiC κ) (sleLambda κ - θ₁ * QuantumZipper.chiC κ)) := by
  set χ := QuantumZipper.chiC κ with hχ
  set g₁ := -sleLambda κ - θ₂ * χ with hg₁
  set g₂ := sleLambda κ - θ₂ * χ with hg₂
  set g₃ := -sleLambda κ - θ₁ * χ with hg₃
  set g₄ := sleLambda κ - θ₁ * χ with hg₄
  set m := capR d.u d.r with hm
  have hum : d.u < m := lt_capR_left d.u d.r
  have hrm : d.r < m := lt_capR_right d.u d.r
  have hword := ae_wordM_eq_zoneWord hκ hκ4 hx hη₁ hη₂ hd hag hc₀ g₁ g₂ g₃ g₄
  set β := wordM d c₀ g₁ g₂ g₃ g₄ with hβdef
  intro ηc₁ ηc₂ g hc₁ hc₂ hm₁ hm₂ hag₁ hag₂ hg
  have hh0 := isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  obtain ⟨hBm, hBloc, hBdet, hBunb⟩ :=
    cstUnion_facts hL75 hκ hκ4 hb hh hη₁ hη₂ hu₀ m d.u d.r hc₁ hc₂ hm₁ hm₂ hag₁ hag₂
  have hF₁ := range_facts hL75 WholeField.retainedRangeEntranceStatement hκ hκ4 hb hh hη₁ hu₀ m d.u hc₁ hm₁ hag₁
  have hF₂ := range_facts hL75 WholeField.retainedRangeEntranceStatement hκ hκ4 hb hh hη₂ hu₀ m d.r hc₂ hm₂ hag₂
  obtain ⟨G₁, hG₁⟩ := IsLocalSet.exists_isLocalSetMean hh0 hF₁.1 hF₁.2.1
  obtain ⟨G₂, hG₂⟩ := IsLocalSet.exists_isLocalSetMean hh0 hF₂.1 hF₂.2.1
  have hC₁ := ae_tendsto_sub_of_locals hh0 hBm hF₁.1 hBloc hF₁.2.1 hBdet hF₁.2.2.1 hBunb hF₁.2.2.2 hg hG₁
  have hC₂ := ae_tendsto_sub_of_locals hh0 hBm hF₂.1 hBloc hF₂.2.1 hBdet hF₂.2.2.1 hBunb hF₂.2.2.2 hg hG₂
  obtain ⟨_, _, W₁, _, _, _, -, hcoup₁, htr₁⟩ := id hη₁
  obtain ⟨_, _, W₂, _, _, _, -, hcoup₂, htr₂⟩ := id hη₂
  have hS₁ := singlePathSideHeight_slit (m := m) (q := d.u) hL75 WholeField.retainedRangeEntranceStatement hκ hκ4
    hb hh hη₁ htr₁ hu₀ hum.le hc₁ hm₁ hag₁ hG₁
  have hS₂ := singlePathSideHeight_slit (m := m) (q := d.r) hL75 WholeField.retainedRangeEntranceStatement hκ hκ4
    hb hh hη₂ htr₂ hu₀ hrm.le hc₂ hm₂ hag₂ hG₂
  have hdec := Sec7.IsLocalSetMean.ae_tendsto_zero_of_real hh0 hBm hBloc hg
  filter_upwards [hword, hag₁, hag₂, htr₁, htr₂, hcoup₁.1.2.2.2.2, hcoup₂.1.2.2.2.2, hC₁, hC₂, hS₁, hS₂, hdec,
    hG₁.2.1, hG₂.2.1] with ω hwordω e₁ e₂ htr₁ω htr₂ω hpath₁ hpath₂ hC₁ω hC₂ω hS₁ω hS₂ω hdecω hR₁ω hR₂ω hp
    v hv hvrep
  obtain ⟨hβω, hs, hE, hK⟩ := hwordω hp
  -- the sets
  have i₁ : ηc₁ ω '' Icc 0 d.u = η₁ ω '' Icc 0 d.u :=
    image_congr fun s hs => by rw [e₁ s, capTime_eq_of_lt hp.1 hum hs.2]
  have i₂ : ηc₂ ω '' Icc 0 d.r = η₂ ω '' Icc 0 d.r :=
    image_congr fun t ht => by rw [e₂ t, capTime_eq_of_lt hp.2.1 hrm ht.2]
  have hU : cstUnion ηc₁ ηc₂ d.u d.r ω = d.K ω ∩ H := by
    rw [cstUnion_eq, hK, prefixSet, i₁, i₂]
  have hA₁ : ηc₁ ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ d.u} ∩ H = η₁ ω '' Icc 0 d.u ∩ H := by
    rw [Sec7.image_capped_eq e₁ (le_min hp.1.le (ENNReal.coe_le_coe.2 hum.le))]
  have hA₂ : ηc₂ ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ d.r} ∩ H = η₂ ω '' Icc 0 d.r ∩ H := by
    rw [Sec7.image_capped_eq e₂ (le_min hp.2.1.le (ENNReal.coe_le_coe.2 hrm.le))]
  obtain ⟨vA₁, hvA₁, hvA₁r⟩ := hR₁ω
  obtain ⟨vA₂, hvA₂, hvA₂r⟩ := hR₂ω
  have hdec' := hdecω v hv hvrep
  have hcmp₁ := hC₁ω v vA₁ hv hvrep hvA₁ hvA₁r
  have hcmp₂ := hC₂ω v vA₂ hv hvrep hvA₂ hvA₂r
  rw [hU] at hdec' hcmp₁ hcmp₂
  rw [hA₁] at hcmp₁
  rw [hA₂] at hcmp₂
  have hsh₁ := hS₁ω hp.1 vA₁ hvA₁ hvA₁r
  have hsh₂ := hS₂ω hp.2.1 vA₂ hvA₂ hvA₂r
  obtain ⟨E, hEf, hlim⟩ := exists_finite_tendsto_word (χ := QuantumZipper.chiC κ) (g₁ := g₁) (g₂ := g₂)
    (g₃ := g₃) (g₄ := g₄) hd hE hs hK htr₁ω hpath₁.2.2.2.1 hpath₁.1 htr₂ω hpath₂.2.2.2.1 hpath₂.1 hu₀.2.2 hdec'
    hcmp₁ hcmp₂ (fun p F hF hFle y hy => hsh₁ p F hF hFle y hy) (fun p F hF hFle y hy => hsh₂ p F hF hFle y hy)
    hc₀ hc₀J hc₀b
  refine ⟨E, hEf, fun w hw => ?_⟩
  rw [hβω, BoundaryWord.trunc_fn]
  exact hlim w hw

/-- **The mean identification for the measurable word of the retained data** (`IsRetMeanIdent`, LEMMA76G's
assembly `isRetMeanIdent_of_chartBoundaryLimit`), and its sortedness at disjoint pairs. -/
theorem isRetMeanIdent_wordM (hL75 : Theorem15.Lemma75Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hx : x₂ < x₁) (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂) (hd : d.IsMeasGood)
    (hag : ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
      (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) {c₀ : BoundaryWord}
    (hc₀ : StrictMonoOn c₀.2.1 (Iio c₀.1)) (hc₀J : c₀.jumps = jumps) (hc₀b : ∀ y ∉ jumps, c₀.fn y = b y) :
    IsRetMeanIdent κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd
        (wordM d c₀ (-sleLambda κ - θ₂ * QuantumZipper.chiC κ) (sleLambda κ - θ₂ * QuantumZipper.chiC κ)
          (-sleLambda κ - θ₁ * QuantumZipper.chiC κ) (sleLambda κ - θ₁ * QuantumZipper.chiC κ)) ∧
      ∀ᵐ ω ∂P, Lemma76Exit.IsDisjointPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r →
        (wordM d c₀ (-sleLambda κ - θ₂ * QuantumZipper.chiC κ) (sleLambda κ - θ₂ * QuantumZipper.chiC κ)
          (-sleLambda κ - θ₁ * QuantumZipper.chiC κ) (sleLambda κ - θ₁ * QuantumZipper.chiC κ) ω).IsSorted := by
  have hsort : ∀ᵐ ω ∂P, Lemma76Exit.IsDisjointPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r →
      (wordM d c₀ (-sleLambda κ - θ₂ * QuantumZipper.chiC κ) (sleLambda κ - θ₂ * QuantumZipper.chiC κ)
        (-sleLambda κ - θ₁ * QuantumZipper.chiC κ) (sleLambda κ - θ₁ * QuantumZipper.chiC κ) ω).IsSorted := by
    filter_upwards [ae_wordM_eq_zoneWord hκ hκ4 hx hη₁ hη₂ hd hag hc₀ (-sleLambda κ - θ₂ * QuantumZipper.chiC κ)
      (sleLambda κ - θ₂ * QuantumZipper.chiC κ) (-sleLambda κ - θ₁ * QuantumZipper.chiC κ)
      (sleLambda κ - θ₁ * QuantumZipper.chiC κ)] with ω hω hp
    obtain ⟨hβω, hs, -, -⟩ := hω hp
    rw [hβω]
    exact (ZW.word_isSorted hs.zoneData_good hc₀).trunc
  exact ⟨isRetMeanIdent_of_chartBoundaryLimit hL75 hκ hκ4 hb hh hη₁ hη₂ hd hag hu₀ hsort
    (isRetChartBoundaryLimit_wordM hL75 hκ hκ4 hb hx hh hη₁ hη₂ hd hag hu₀ hc₀ hc₀J hc₀b), hsort⟩

end Lemma76G

end Sec7

end InteractingSLE
