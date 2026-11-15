/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCCondDetHist
import InteractingSLE.Spec.Supplement.RLCCondDetHistWord
import InteractingSLE.Spec.Supplement.RLCLPositivity
import InteractingSLE.Spec.Sec7.Lemma76RIdent

/-!
# The initial word of an ordinary pair: the disjoint prefixes from Lemma 7.6's zone word

Packet PROVE-CONDDET-HIST. `RLC.RetOrdMeanWordStatement` (the explicit initial word of an ordinary retained pair) splits
by whether the two retained prefixes meet. With disjoint prefixes (and then necessarily `x₂ < x₁`) an ordinary pair is a
disjoint pair of Lemma 7.6, and PROVE-LEMMA76G's measurable zone word `wordM` of the stopped capped copy of the data
has the mean identification (`Sec7.Lemma76G.isRetMeanIdent_wordM`) and the outer word (`isRetainedWord_zoneWord`,
`isUntouchedWord_zoneWord`). The remaining case, prefixes that meet (G7's junction between the second prefix's right
side and the first prefix's left side), is the named input `RetTouchMeanWordStatement`.

* `comap_le_retSigma76`, `disjSet`, `exists_retStop`: the stopped capped copy of the retained data, measurable for the
  retained σ-algebra, and the measurable event of disjoint prefixes;
* `ae_tipPt_eq_tipPos`: the measurable seed (the first tip's chart point) at the ordinary pairs;
* `exists_disjWord`: the word with the disjoint prefixes;
* **`retOrdMeanWordStatement_of_touch`**: `RetOrdMeanWordStatement` from Lemma 7.5 and `RetTouchMeanWordStatement`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

universe u

namespace InteractingSLE

namespace RLC

open Supp7 Supp9D Restart LQGMetric Sec7.Lemma76F Sec7.Lemma76G

/-! ### The retained σ-algebra contains the σ-algebra of an almost sure copy of the histories -/

section Transfer

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- A measurable copy `F` of the retained histories (almost surely equal) generates a sub-σ-algebra of `retSigma76`. -/
theorem comap_le_retSigma76 {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞} {u r : ℝ≥0} {F : Ω → KHist × KHist}
    (hFm : Measurable F) (hF : ∀ᵐ ω ∂P, F ω = retHist76 η₁ η₂ ζ₁ ζ₂ u r ω) :
    MeasurableSpace.comap F inferInstance ≤ retSigma76 P η₁ η₂ ζ₁ ζ₂ u r := by
  rintro S ⟨T, hT, rfl⟩
  refine MeasurableSpace.measurableSet_inf.2 ⟨hFm hT, ⟨retHist76 η₁ η₂ ζ₁ ζ₂ u r ⁻¹' T, ⟨T, hT, rfl⟩, ?_⟩⟩
  filter_upwards [hF] with ω hω
  simp only [mem_preimage, hω]

end Transfer

/-! ### The event of disjoint prefixes -/

section Disj

variable {Ω : Type*}

/-- The event (inside the good event) on which the two prefixes of retained data are disjoint. -/
def disjSet (d : RetData Ω) : Set Ω := d.G \ (d.G ∩ {ω | ∃ s ≤ d.u, ∃ t ≤ d.r, d.η₁ ω s = d.η₂ ω t})

theorem measurableSet_disjSet [MeasurableSpace Ω] {d : RetData Ω} (hd : d.IsMeasGood) : MeasurableSet (disjSet d) :=
  hd.measurableSet_G.diff (measurableSet_inter_exists_eq hd.measurableSet_G hd.meas₁ hd.meas₂
    (c₁ := fun _ => d.u) (c₂ := fun _ => d.r) measurable_const measurable_const
    (fun ω hω => by rw [← Icc_zero_eq_Iic]; exact (hd.good ω hω).1)
    (fun ω hω => by rw [← Icc_zero_eq_Iic]; exact (hd.good ω hω).2.1))

theorem mem_disjSet_iff {d : RetData Ω} {ω : Ω} (hG : ω ∈ d.G) :
    ω ∈ disjSet d ↔ Disjoint (d.η₁ ω '' Icc 0 d.u) (d.η₂ ω '' Icc 0 d.r) := by
  constructor
  · rintro ⟨-, hn⟩
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨s, hs, rfl⟩ ⟨t, ht, he⟩
    exact hn ⟨hG, s, hs.2, t, ht.2, he.symm⟩
  · intro hdis
    refine ⟨hG, ?_⟩
    rintro ⟨-, s, hs, t, ht, he⟩
    exact Set.disjoint_left.1 hdis ⟨s, ⟨zero_le, hs⟩, rfl⟩ ⟨t, ⟨zero_le, ht⟩, he.symm⟩

end Disj

/-- An ordinary retained pair with disjoint prefixes is a disjoint pair of Lemma 7.6. -/
theorem isDisjointPair_of_ordinary {α β : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞} {a c : ℝ≥0}
    (hord : IsOrdinaryRetainedPair α ζ₁ a β ζ₂ c) (hdis : Disjoint (α '' Icc 0 a) (β '' Icc 0 c)) :
    Sec7.Lemma76Exit.IsDisjointPair α ζ₁ a β ζ₂ c :=
  ⟨hord.1, hord.2.1, hord.2.2.2.1, hdis, hord.2.2.2.2.2.2.2.1, hord.2.2.2.2.2.2.1⟩

/-! ### The stopped capped copy of the retained data -/

section Stop

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {η₁ η₂ : Ω → ℝ≥0 → ℂ}
  {ζ₁ ζ₂ : Ω → ℝ≥0∞}

/-- **The stopped capped copy of retained data** (as in `Sec7.Lemma76G.lemma76ChartBoundaryStatement_of_lemma75`): the
paths `t ↦ ηsᵢ(t ∧ cutoff)` of Lemma 7.5's capped versions form retained data that is measurable for the retained
σ-algebra and agrees, almost surely before the lifetimes, with the flow lines on the prefixes. -/
theorem exists_retStop (hL75 : Theorem15.Lemma75Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂) (u₀ : ℂ → ℝ)
    (a r : ℝ≥0) :
    ∃ ηs₁ ηs₂ : Ω → ℝ≥0 → ℂ,
      @RetData.IsMeasGood Ω (retSigma76 P η₁ η₂ ζ₁ ζ₂ a r) (stopRet ηs₁ ηs₂ a r) ∧
      ∀ᵐ ω ∂P, (a : ℝ≥0∞) < ζ₁ ω → (r : ℝ≥0∞) < ζ₂ ω → ω ∈ (stopRet ηs₁ ηs₂ a r).G ∧
        (∀ s ≤ (stopRet ηs₁ ηs₂ a r).u, (stopRet ηs₁ ηs₂ a r).η₁ ω s = η₁ ω s) ∧
        ∀ t ≤ (stopRet ηs₁ ηs₂ a r).r, (stopRet ηs₁ ηs₂ a r).η₂ ω t = η₂ ω t := by
  set m := capR a r with hm
  have hum : a < m := lt_capR_left a r
  have hrm : r < m := lt_capR_right a r
  obtain ⟨ηs₁, hsc₁, hsm₁, hs0₁, -, hsag₁, -, -⟩ := exists_capped_version hL75 hκ hκ4 hb hh hη₁ u₀ m
  obtain ⟨ηs₂, hsc₂, hsm₂, hs0₂, -, hsag₂, -, -⟩ := exists_capped_version hL75 hκ hκ4 hb hh hη₂ u₀ m
  have hζm₁ := measurable_lifetime_of_isFlowLine hη₁
  have hζm₂ := measurable_lifetime_of_isFlowLine hη₂
  set F := cstHist ηs₁ ηs₂ (fun ω => cutLife (ζ₁ ω) m) (fun ω => cutLife (ζ₂ ω) m) a r with hF
  have hFm : Measurable F := measurable_cstHist hsm₁ hsm₂ ((measurable_cutLife m).comp hζm₁)
    ((measurable_cutLife m).comp hζm₂) a r
  have hd'F : @RetData.IsMeasGood Ω (MeasurableSpace.comap F inferInstance) (stopRet ηs₁ ηs₂ a r) :=
    isMeasGood_stopRet (ζ₁ := fun ω => cutLife (ζ₁ ω) m) (ζ₂ := fun ω => cutLife (ζ₂ ω) m) le_rfl hsc₁ hsc₂
      hs0₁ hs0₂
  have hFret : ∀ᵐ ω ∂P, F ω = retHist76 η₁ η₂ ζ₁ ζ₂ a r ω := by
    filter_upwards [hsag₁, hsag₂] with ω h1 h2
    have e1 : ηs₁ ω = cappedPath η₁ ζ₁ m ω := funext h1
    have e2 : ηs₂ ω = cappedPath η₂ ζ₂ m ω := funext h2
    simp only [hF, retHist76, cstHist, e1, e2]
    rfl
  refine ⟨ηs₁, ηs₂, RetData.IsMeasGood.mono_sigma hd'F (comap_le_retSigma76 hFm hFret), ?_⟩
  filter_upwards [hsag₁, hsag₂, Sec7.ae_im_nonneg_of_isFlowLine' hη₁, Sec7.ae_im_nonneg_of_isFlowLine' hη₂,
    ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₂] with ω e₁ e₂ hi₁ hi₂ hp₂ hu hr
  have b₁ : ∀ s ≤ a, (stopRet ηs₁ ηs₂ a r).η₁ ω s = η₁ ω s := fun s hs => by
    show hproj (ηs₁ ω (min s a)) = _
    rw [min_eq_left hs, e₁ s, capTime_eq_of_lt hu hum hs, hproj_of_im_nonneg]
    exact hi₁ s ((ENNReal.coe_le_coe.2 hs).trans hu.le)
  have b₂ : ∀ t ≤ r, (stopRet ηs₁ ηs₂ a r).η₂ ω t = η₂ ω t := fun t ht => by
    show hproj (ηs₂ ω (min t r)) = _
    rw [min_eq_left ht, e₂ t, capTime_eq_of_lt hr hrm ht, hproj_of_im_nonneg]
    exact hi₂ t ((ENNReal.coe_le_coe.2 ht).trans hr.le)
  refine ⟨?_, b₁, b₂⟩
  intro t ht he
  have he' : (stopRet ηs₁ ηs₂ a r).η₂ ω t = (stopRet ηs₁ ηs₂ a r).η₂ ω r := he
  rw [b₂ t ht.le, b₂ r le_rfl] at he'
  exact (ne_of_lt ht) ((Sec7.IsPathGood.injOn_Icc hp₂ hr.le) ⟨zero_le, ht.le⟩ ⟨zero_le, le_rfl⟩ he')

omit [IsProbabilityMeasure P] in
/-- **Retained data agreeing with the flow lines have the same chart** (almost surely before the lifetimes, on the chart
event). -/
theorem ae_agree_stopRet {d : RetData Ω} {ηs₁ ηs₂ : Ω → ℝ≥0 → ℂ}
    (hag : ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
      (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t)
    (hag' : ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ (stopRet ηs₁ ηs₂ d.u d.r).G ∧
      (∀ s ≤ d.u, (stopRet ηs₁ ηs₂ d.u d.r).η₁ ω s = η₁ ω s) ∧
      ∀ t ≤ d.r, (stopRet ηs₁ ηs₂ d.u d.r).η₂ ω t = η₂ ω t) :
    ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.E →
      ω ∈ (stopRet ηs₁ ηs₂ d.u d.r).E ∧ (stopRet ηs₁ ηs₂ d.u d.r).D ω = d.D ω ∧
      (stopRet ηs₁ ηs₂ d.u d.r).chart ω = d.chart ω ∧ (stopRet ηs₁ ηs₂ d.u d.r).fwd ω = d.fwd ω ∧
      (stopRet ηs₁ ηs₂ d.u d.r).inv ω = d.inv ω := by
  filter_upwards [hag, hag'] with ω h1 h2 hu hr hE
  obtain ⟨hG, a₁, a₂⟩ := h1 hu hr
  obtain ⟨hG', b₁, b₂⟩ := h2 hu hr
  obtain ⟨hEiff, hDeq, hch⟩ := RetData.chart_eq_of_agree (G' := (stopRet ηs₁ ηs₂ d.u d.r).G)
    (η₁' := (stopRet ηs₁ ηs₂ d.u d.r).η₁) (η₂' := (stopRet ηs₁ ηs₂ d.u d.r).η₂) hG hG'
    (fun s hs => (b₁ s hs).trans (a₁ s hs).symm) (fun t ht => (b₂ t ht).trans (a₂ t ht).symm)
  have hE' : ω ∈ (stopRet ηs₁ ηs₂ d.u d.r).E := hEiff.2 hE
  have h' : (stopRet ηs₁ ηs₂ d.u d.r).chart ω = d.chart ω := hch
  have h'' := h'
  rw [RetData.chart_of_mem hE', RetData.chart_of_mem hE] at h''
  exact ⟨hE', hDeq, h', (Prod.ext_iff.1 h'').1, (Prod.ext_iff.1 (Prod.ext_iff.1 h'').2).1⟩

/-- **The measurable seed is the first tip's chart position at an ordinary pair.** -/
theorem ae_tipPt_eq_tipPos (hκ : 0 < κ) (hκ4 : κ < 4) (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁)
    {d : RetData Ω} (hd : d.IsMeasGood) {ηs₁ ηs₂ : Ω → ℝ≥0 → ℂ}
    (hag : ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
      (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t)
    (hag' : ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ (stopRet ηs₁ ηs₂ d.u d.r).G ∧
      (∀ s ≤ d.u, (stopRet ηs₁ ηs₂ d.u d.r).η₁ ω s = η₁ ω s) ∧
      ∀ t ≤ d.r, (stopRet ηs₁ ηs₂ d.u d.r).η₂ ω t = η₂ ω t) :
    ∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r →
      tipPt (stopRet ηs₁ ηs₂ d.u d.r) ω = tipPos d η₁ ω := by
  filter_upwards [hag, hag', ae_agree_stopRet hag hag',
    ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₁] with ω h1 h2 h3 hp₁ hord
  obtain ⟨hG, a₁, a₂⟩ := h1 hord.1 hord.2.1
  obtain ⟨-, b₁, b₂⟩ := h2 hord.1 hord.2.1
  have hE : ω ∈ d.E := hd.mem_E_of_ordinary hG a₁ a₂ hord
  obtain ⟨hE', hDeq, -, hfwd, -⟩ := h3 hord.1 hord.2.1 hE
  have e₁ : EqOn (d.η₁ ω) (η₁ ω) (Icc 0 d.u) := fun s hs => a₁ s hs.2
  have e₂ : EqOn (d.η₂ ω) (η₂ ω) (Icc 0 d.r) := fun t ht => a₂ t ht.2
  have hDact : d.D ω = activeDomain (η₁ ω) d.u (η₂ ω) d.r := by
    rw [hd.D_of_mem hE, activeDomain_congr_Icc e₁ e₂]
  have htip : ω ∈ tipEv (stopRet ηs₁ ηs₂ d.u d.r) := by
    refine ⟨⟨hE', ?_⟩, ?_, ?_⟩
    · show (stopRet ηs₁ ηs₂ d.u d.r).η₁ ω d.u ∈ closure ((stopRet ηs₁ ηs₂ d.u d.r).D ω)
      rw [b₁ d.u le_rfl, hDeq, hDact]
      exact hord.2.2.2.2.2.2.1
    · show (stopRet ηs₁ ηs₂ d.u d.r).η₁ ω d.u ∉ (stopRet ηs₁ ηs₂ d.u d.r).η₂ ω '' Icc 0 d.r
      rw [b₁ d.u le_rfl, image_congr fun t ht => b₂ t ht.2]
      exact hord.2.2.2.2.2.1
    · intro s hs he
      have he' : (stopRet ηs₁ ηs₂ d.u d.r).η₁ ω s = (stopRet ηs₁ ηs₂ d.u d.r).η₁ ω d.u := he
      rw [b₁ s hs.le, b₁ d.u le_rfl] at he'
      exact (ne_of_lt hs) ((Sec7.IsPathGood.injOn_Icc hp₁ hord.1.le) ⟨zero_le, hs.le⟩ ⟨zero_le, le_rfl⟩ he')
  unfold tipPt
  rw [indicator_of_mem htip]
  show chartPt ((stopRet ηs₁ ηs₂ d.u d.r).fwd ω) ((stopRet ηs₁ ηs₂ d.u d.r).D ω)
      ((stopRet ηs₁ ηs₂ d.u d.r).η₁ ω d.u) = (limUnder (𝓝[d.D ω] (η₁ ω d.u)) (d.fwd ω)).re
  rw [hfwd, hDeq, b₁ d.u le_rfl]
  rfl

/-- **The initial word with disjoint prefixes** (from Lemma 7.5): a word measurable for the retained σ-algebra with the
mean identification at the ordinary pairs with disjoint prefixes, sorted there, with a positive first-tip chart position
and G7's outer word. Disjoint prefixes force `x₂ < x₁`; then the word is Lemma 7.6's zone word of the stopped capped
copy (`Sec7.Lemma76G.isRetMeanIdent_wordM`). -/
theorem exists_disjWord (hL75 : Theorem15.Lemma75Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hx : x₂ ≤ x₁) (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    {d : RetData Ω} (hd : d.IsMeasGood)
    (hag : ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
      (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) :
    ∃ βd : Ω → BoundaryWord, Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] βd ∧
      IsRetMeanIdentOn κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd {ω | IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r ∧
        Disjoint (η₁ ω '' Icc 0 d.u) (η₂ ω '' Icc 0 d.r)} βd ∧
      ∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r →
        Disjoint (η₁ ω '' Icc 0 d.u) (η₂ ω '' Icc 0 d.r) →
        (βd ω).IsSorted ∧ 0 < tipPos d η₁ ω ∧ IsRetainedWord κ θ₁ θ₂ (η₁ ω) d.u (η₂ ω) d.r (d.inv ω) (βd ω) ∧
        IsUntouchedWord b jumps (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) (d.inv ω) (βd ω) := by
  classical
  obtain ⟨c₀, hc₀, hc₀J, hc₀b⟩ := Restart.BoundaryWord.exists_fn_eq_strictMonoOn hb
  rcases hx.lt_or_eq with hx' | hx'
  swap
  · -- equal seeds: no ordinary pair has disjoint prefixes
    have hempty : ∀ᵐ ω ∂P, ¬ (IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r ∧
        Disjoint (η₁ ω '' Icc 0 d.u) (η₂ ω '' Icc 0 d.r)) := by
      filter_upwards [ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₁,
        ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₂] with ω hp₁ hp₂ hω
      refine Set.disjoint_left.1 hω.2 ⟨0, ⟨le_rfl, zero_le⟩, rfl⟩ ⟨0, ⟨le_rfl, zero_le⟩, ?_⟩
      rw [Sec7.IsPathGood.zero hp₁, Sec7.IsPathGood.zero hp₂, hx']
    refine ⟨fun _ => c₀, measurable_const, ?_, ?_⟩
    · intro ηc₁ ηc₂ g _ _ _ _ _ _ _
      filter_upwards [hempty] with ω hω h'
      exact absurd h' hω
    · filter_upwards [hempty] with ω hω hord hdis
      exact absurd ⟨hord, hdis⟩ hω
  set g₁ := -sleLambda κ - θ₂ * QuantumZipper.chiC κ with hg₁
  set g₂ := sleLambda κ - θ₂ * QuantumZipper.chiC κ with hg₂
  set g₃ := -sleLambda κ - θ₁ * QuantumZipper.chiC κ with hg₃
  set g₄ := sleLambda κ - θ₁ * QuantumZipper.chiC κ with hg₄
  obtain ⟨ηs₁, ηs₂, hd'R, hag'⟩ := exists_retStop hL75 hκ hκ4 hb hh hη₁ hη₂ u₀ d.u d.r
  set d' := stopRet ηs₁ ηs₂ d.u d.r with hd'def
  have hd' : d'.IsMeasGood := RetData.IsMeasGood.mono_sigma hd'R (retSigma76_le P η₁ η₂ ζ₁ ζ₂ d.u d.r)
  have hβ : Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] (wordM d' c₀ g₁ g₂ g₃ g₄) :=
    @measurable_wordM Ω (retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r) d' hd'R c₀ g₁ g₂ g₃ g₄
  obtain ⟨hmi, -⟩ := isRetMeanIdent_wordM hL75 hκ hκ4 hb hx' hh hη₁ hη₂ hd' hag' hu₀ hc₀ hc₀J hc₀b
  have hzw := ae_wordM_eq_zoneWord hκ hκ4 hx' hη₁ hη₂ hd' hag' hc₀ g₁ g₂ g₃ g₄
  have hagree := ae_agree_stopRet hag hag'
  refine ⟨wordM d' c₀ g₁ g₂ g₃ g₄, hβ, ?_, ?_⟩
  · intro ηc₁ ηc₂ g hc₁ hc₂ hm₁ hm₂ hag₁ hag₂ hg
    filter_upwards [hmi ηc₁ ηc₂ g hc₁ hc₂ hm₁ hm₂ hag₁ hag₂ hg, hagree, hag] with ω e hch hagω hω φ
    obtain ⟨hG, a₁, a₂⟩ := hagω hω.1.1 hω.1.2.1
    have hE := hd.mem_E_of_ordinary hG a₁ a₂ hω.1
    have he := e (isDisjointPair_of_ordinary hω.1 hω.2) φ
    rwa [chartTransport_congr_chart (hch hω.1.1 hω.1.2.1 hE).2.2.1 (hd'.isConformal_chart ω)
      (hd.isConformal_chart ω)] at he
  · filter_upwards [hzw, hagree, hag] with ω hzwω hch hagω hord hdis
    obtain ⟨hG, a₁, a₂⟩ := hagω hord.1 hord.2.1
    have hE := hd.mem_E_of_ordinary hG a₁ a₂ hord
    obtain ⟨-, -, -, hfwd, hinv⟩ := hch hord.1 hord.2.1 hE
    obtain ⟨hβω, hs, -, -⟩ := hzwω (isDisjointPair_of_ordinary hord hdis)
    have e₁ : EqOn (d.η₁ ω) (η₁ ω) (Icc 0 d.u) := fun s hs => a₁ s hs.2
    have e₂ : EqOn (d.η₂ ω) (η₂ ω) (Icc 0 d.r) := fun t ht => a₂ t ht.2
    have hDact : d.D ω = activeDomain (η₁ ω) d.u (η₂ ω) d.r := by
      rw [hd.D_of_mem hE, activeDomain_congr_Icc e₁ e₂]
    have hpos : 0 < tipPos d η₁ ω := by
      have h0 := zero_lt_M₁ hs
      show 0 < (limUnder (𝓝[d.D ω] (η₁ ω d.u)) (d.fwd ω)).re
      rw [hDact, ← hfwd]
      exact h0
    rw [hβω, ← hinv]
    exact ⟨(ZW.word_isSorted hs.zoneData_good hc₀).trunc, hpos, isRetainedWord_zoneWord hs hc₀ κ θ₁ θ₂,
      isUntouchedWord_zoneWord hs hc₀ hc₀J hc₀b g₁ g₂ g₃ g₄⟩

/-! ### The ordinary pairs whose prefixes meet, and the assembly -/

/-- **Named input: the initial word of an ordinary retained pair whose prefixes meet** (Lemma G7's premise and the
outer-word argument of Aux. 85–86 at the ordinary pairs of Theorem 7.12D, p. 543, in the case not covered by Lemma 7.6:
the second prefix touches the first, so the right side of the second prefix and the left side of the first meet at a
junction and no untouched real interval separates the bases). `RetOrdMeanWordStatement` restricted to the ordinary pairs
with meeting prefixes, without the seed (which is `tipPt` of the stopped capped copy, `ae_tipPt_eq_tipPos`).
**Not proved in Lean.** -/
def RetTouchMeanWordStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ ≤ x₁ → θ₁ < θ₂ →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
    ∀ (d : RetData Ω) (hd : d.IsMeasGood),
      (∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
        (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t) →
    ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension b jumps u₀ →
    ∃ β : Ω → BoundaryWord, Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] β ∧
      IsRetMeanIdentOn κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd {ω | IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r ∧
        ¬ Disjoint (η₁ ω '' Icc 0 d.u) (η₂ ω '' Icc 0 d.r)} β ∧
      ∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r →
        ¬ Disjoint (η₁ ω '' Icc 0 d.u) (η₂ ω '' Icc 0 d.r) →
        (β ω).IsSorted ∧ 0 < tipPos d η₁ ω ∧ IsRetainedWord κ θ₁ θ₂ (η₁ ω) d.u (η₂ ω) d.r (d.inv ω) (β ω) ∧
        IsUntouchedWord b jumps (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) (d.inv ω) (β ω)

/-- **The initial word of an ordinary retained pair from Lemma 7.5 and the meeting-prefix case.** The word is
Lemma 7.6's zone word (`exists_disjWord`) on the measurable event of disjoint prefixes of the stopped capped copy
(almost surely the event of disjoint prefixes at an ordinary pair) and the word of `RetTouchMeanWordStatement` off it;
the seed is the measurable first-tip chart point `tipPt` of the stopped capped copy. -/
theorem retOrdMeanWordStatement_of_touch (hL75 : Theorem15.Lemma75Statement.{u})
    (hT : RetTouchMeanWordStatement.{u}) : RetOrdMeanWordStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω mΩ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hag u₀ hu₀
  classical
  obtain ⟨βd, hβd, hmd, hwd⟩ := exists_disjWord (θ₁ := θ₁) (θ₂ := θ₂) hL75 hκ hκ4 hb hx hh hη₁ hη₂ hd hag hu₀
  obtain ⟨βt, hβt, hmt, hwt⟩ :=
    hT κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hag u₀ hu₀
  obtain ⟨ηs₁, ηs₂, hd'R, hag'⟩ := exists_retStop hL75 hκ hκ4 hb hh hη₁ hη₂ u₀ d.u d.r
  set d' := stopRet ηs₁ ηs₂ d.u d.r with hd'def
  have hDsm : MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] (disjSet d') :=
    @measurableSet_disjSet Ω (retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r) d' hd'R
  have hs₀ : Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] (tipPt d') :=
    @measurable_tipPt Ω (retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r) d' hd'R
  have hseed := ae_tipPt_eq_tipPos hκ hκ4 hη₁ hd hag hag'
  have hDiff : ∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r →
      (ω ∈ disjSet d' ↔ Disjoint (η₁ ω '' Icc 0 d.u) (η₂ ω '' Icc 0 d.r)) := by
    filter_upwards [hag'] with ω hω hord
    obtain ⟨hG', b₁, b₂⟩ := hω hord.1 hord.2.1
    rw [mem_disjSet_iff hG']
    show Disjoint (d'.η₁ ω '' Icc 0 d.u) (d'.η₂ ω '' Icc 0 d.r) ↔ _
    rw [image_congr fun s hs => b₁ s hs.2, image_congr fun t ht => b₂ t ht.2]
  refine ⟨fun ω => ((disjSet d').piecewise βd βt ω, tipPt d' ω),
    (Measurable.piecewise hDsm hβd hβt).prodMk hs₀, ?_, ?_⟩
  · intro ηc₁ ηc₂ g hc₁ hc₂ hm₁ hm₂ hag₁ hag₂ hg
    filter_upwards [hmd ηc₁ ηc₂ g hc₁ hc₂ hm₁ hm₂ hag₁ hag₂ hg, hmt ηc₁ ηc₂ g hc₁ hc₂ hm₁ hm₂ hag₁ hag₂ hg, hDiff]
      with ω e1 e2 e3 hord φ
    by_cases hdis : Disjoint (η₁ ω '' Icc 0 d.u) (η₂ ω '' Icc 0 d.r)
    · have hpw : (disjSet d').piecewise βd βt ω = βd ω := Set.piecewise_eq_of_mem _ _ _ ((e3 hord).2 hdis)
      rw [hpw]
      exact e1 ⟨hord, hdis⟩ φ
    · have hpw : (disjSet d').piecewise βd βt ω = βt ω :=
        Set.piecewise_eq_of_notMem _ _ _ fun h' => hdis ((e3 hord).1 h')
      rw [hpw]
      exact e2 ⟨hord, hdis⟩ φ
  · filter_upwards [hwd, hwt, hDiff, hseed] with ω h1 h2 h3 h4 hord
    rw [h4 hord]
    by_cases hdis : Disjoint (η₁ ω '' Icc 0 d.u) (η₂ ω '' Icc 0 d.r)
    · rw [Set.piecewise_eq_of_mem _ _ _ ((h3 hord).2 hdis)]
      obtain ⟨hs, hpos, hret, hunt⟩ := h1 hord hdis
      exact ⟨hs, rfl, hpos, hret, hunt⟩
    · rw [Set.piecewise_eq_of_notMem _ _ _ fun h' => hdis ((h3 hord).1 h')]
      obtain ⟨hs, hpos, hret, hunt⟩ := h2 hord hdis
      exact ⟨hs, rfl, hpos, hret, hunt⟩

/-- **G7's conditional law given the retained histories from Lemma 7.5, the meeting-prefix word and (Det).** -/
theorem retainedCanonCondDetHistStatement_of_touch_det (hL75 : Theorem15.Lemma75Statement.{u})
    (hT : RetTouchMeanWordStatement.{u}) (hDet : RetOrdDetStatement.{u}) : RetainedCanonCondDetHistStatement.{u} :=
  retainedCanonCondDetHistStatement_of_meanWord_det hL75 (retOrdMeanWordStatement_of_touch hL75 hT) hDet

end Stop

end RLC

end InteractingSLE
