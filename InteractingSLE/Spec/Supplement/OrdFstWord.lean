/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.OrdFstTouch
import InteractingSLE.Spec.Restart.RetPlumbProofInputsWord

/-!
# Leaf 3, the first continuation: the sided initial word of an ordinary pair, and its transfer to every mean word

Packet PROVE-T15-ORDDET3 (Theorem 1.5's leaf 3, `RLC.RetOrdDetFstStatement`; Aux. lemmas 85–86, Lemma 7.6's zone word).

* `exists_disjWord_fst`: the proof of `RLC.exists_disjWord` (Lemma 7.6's zone word at the disjoint ordinary pairs)
  with the sided first-path clause (`isRetainedWordFst_zoneWord`);
* **`RetOrdMeanWordFstStatement`** (a statement shape) and **`retOrdMeanWordFstStatement_of_lemma75`**: the explicit
  initial word of an ordinary retained pair (`RetOrdMeanWordStatement`) with the sided first-path clause, from Lemma 7.5
  alone (disjoint prefixes: `exists_disjWord_fst`; meeting prefixes: `retTouchChartBoundaryFstStatement_of_lemma75`);
* **`ae_isRetainedWordFst_of_meanIdent`**: EVERY sorted word with the mean identification and the outer word
  `IsRetainedWord` at the ordinary pairs is almost surely sided there (two mean-identified words agree off their jumps,
  `RetAux79.word_fn_eq_of_mean_integrals`, and the outer word excludes jumps at the side points).

For Theorem 1.5; uses Lemma 7.5 only (R43/R48).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE

namespace RLC

open Supp7 Supp9D Restart LQGMetric Sec7.Lemma76F Sec7.Lemma76G

section Disj

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {η₁ η₂ : Ω → ℝ≥0 → ℂ}
  {ζ₁ ζ₂ : Ω → ℝ≥0∞}

/-- **Lemma 7.6's zone word at the disjoint ordinary pairs, with the sided first-path clause** (the proof of
`RLC.exists_disjWord` with `isRetainedWordFst_zoneWord` added; the zone point `M₁` is `tipPos`). -/
theorem exists_disjWord_fst (hL75 : Theorem15.Lemma75Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
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
        IsUntouchedWord b jumps (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) (d.inv ω) (βd ω) ∧
        IsRetainedWordFst κ θ₁ (η₁ ω) d.u (η₂ ω) d.r (d.inv ω) (tipPos d η₁ ω) (βd ω) := by
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
    have htp : tipPos d η₁ ω = (zoneData (d'.fwd ω) (η₁ ω) d.u (η₂ ω) d.r).M₁ := by
      show (limUnder (𝓝[d.D ω] (η₁ ω d.u)) (d.fwd ω)).re = _
      rw [hDact, ← hfwd]
      rfl
    rw [hβω, ← hinv]
    refine ⟨(ZW.word_isSorted hs.zoneData_good hc₀).trunc, hpos, isRetainedWord_zoneWord hs hc₀ κ θ₁ θ₂,
      isUntouchedWord_zoneWord hs hc₀ hc₀J hc₀b g₁ g₂ g₃ g₄, ?_⟩
    rw [htp]
    exact isRetainedWordFst_zoneWord hs hc₀ κ θ₁ g₁ g₂

/-- **The explicit initial word of an ordinary retained pair, with the sided first-path clause**:
`RetOrdMeanWordStatement` with the additional conclusion `IsRetainedWordFst` relative to the seed `tipPos` (the first
tip's chart point). Proved from Lemma 7.5 (`retOrdMeanWordFstStatement_of_lemma75`). -/
def RetOrdMeanWordFstStatement : Prop :=
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
    ∃ β : Ω → BoundaryWord × ℝ, Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] β ∧
      IsRetMeanIdentOn κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd
        {ω | IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r} (fun ω => (β ω).1) ∧
      ∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r →
        (β ω).1.IsSorted ∧ (β ω).2 = tipPos d η₁ ω ∧ 0 < (β ω).2 ∧
        IsRetainedWord κ θ₁ θ₂ (η₁ ω) d.u (η₂ ω) d.r (d.inv ω) (β ω).1 ∧
        IsUntouchedWord b jumps (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) (d.inv ω) (β ω).1 ∧
        IsRetainedWordFst κ θ₁ (η₁ ω) d.u (η₂ ω) d.r (d.inv ω) (tipPos d η₁ ω) (β ω).1

/-- **The sided initial word from Lemma 7.5** (the proof of `retOrdMeanWordStatement_of_touch` with the sided words of
both cases; the touching word's mean identification from its chart boundary values,
`isRetMeanIdentOn_of_chartBoundaryLimitOn`). -/
theorem retOrdMeanWordFstStatement_of_lemma75 (hL75 : Theorem15.Lemma75Statement.{u}) :
    RetOrdMeanWordFstStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω mΩ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hag u₀ hu₀
  classical
  obtain ⟨βd, hβd, hmd, hwd⟩ := exists_disjWord_fst (θ₁ := θ₁) (θ₂ := θ₂) hL75 hκ hκ4 hb hx hh hη₁ hη₂ hd hag hu₀
  obtain ⟨βt, hβt, hbdt, hwt⟩ := retTouchChartBoundaryFstStatement_of_lemma75 hL75 κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂
    hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hag u₀ hu₀
  have hmt : IsRetMeanIdentOn κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd {ω | IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r ∧
      ¬ Disjoint (η₁ ω '' Icc 0 d.u) (η₂ ω '' Icc 0 d.r)} βt := by
    refine isRetMeanIdentOn_of_chartBoundaryLimitOn hL75 hκ hκ4 hb hh hη₁ hη₂ hd hag hu₀ ?_ ?_ hbdt
    · filter_upwards [hag] with ω hω hp
      obtain ⟨hG, a₁, a₂⟩ := hω hp.1.1 hp.1.2.1
      exact ⟨hp.1.1, hp.1.2.1, hd.mem_E_of_ordinary hG a₁ a₂ hp.1⟩
    · filter_upwards [hwt] with ω hω hp
      exact (hω hp.1 hp.2).1
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
      obtain ⟨hs, hpos, hret, hunt, hfst⟩ := h1 hord hdis
      exact ⟨hs, rfl, hpos, hret, hunt, hfst⟩
    · rw [Set.piecewise_eq_of_notMem _ _ _ fun h' => hdis ((h3 hord).1 h')]
      obtain ⟨hs, hpos, hret, hunt, hfst⟩ := h2 hord hdis
      exact ⟨hs, rfl, hpos, hret, hunt, hfst⟩

/-- **Every mean-identified word is sided** (see the module docstring): a sorted word `β` with the mean identification
and the outer word `IsRetainedWord` at the ordinary pairs has, almost surely at an ordinary pair, the sided first-path
heights relative to `tipPos`. -/
theorem ae_isRetainedWordFst_of_meanIdent (hL75 : Theorem15.Lemma75Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hx : x₂ ≤ x₁) (hθ : θ₁ < θ₂)
    (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    {d : RetData Ω} (hd : d.IsMeasGood)
    (hag : ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
      (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) {β : Ω → BoundaryWord}
    (hm : IsRetMeanIdentOn κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd
      {ω | IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r} β)
    (hw : ∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r →
      (β ω).IsSorted ∧ IsRetainedWord κ θ₁ θ₂ (η₁ ω) d.u (η₂ ω) d.r (d.inv ω) (β ω)) :
    ∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r →
      IsRetainedWordFst κ θ₁ (η₁ ω) d.u (η₂ ω) d.r (d.inv ω) (tipPos d η₁ ω) (β ω) := by
  obtain ⟨β', -, hm', hw'⟩ := retOrdMeanWordFstStatement_of_lemma75 hL75 κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P
    h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hag u₀ hu₀
  obtain ⟨ηa₁, ηa₂, hca₁, hca₂, hma₁, hma₂, -, -, haga₁, haga₂, g₀, hg₀, -⟩ :=
    exists_cstUnion_marked_of_isFlowLine hL75 WholeField.retainedRangeEntranceStatement hκ hκ4 hb hh hη₁ hη₂ hu₀
      (capR d.u d.r) d.u d.r
  have hi := hm ηa₁ ηa₂ g₀ hca₁ hca₂ hma₁ hma₂ haga₁ haga₂ hg₀
  have hi' := hm' ηa₁ ηa₂ g₀ hca₁ hca₂ hma₁ hma₂ haga₁ haga₂ hg₀
  filter_upwards [hi, hi', hw, hw'] with ω e e' hwω hw'ω hord
  obtain ⟨hs, hret⟩ := hwω hord
  obtain ⟨hs', -, -, hret', -, hfst'⟩ := hw'ω hord
  have hfn := RetAux79.word_fn_eq_of_mean_integrals hs' hs fun φ => (e' hord φ).symm.trans (e hord φ)
  intro y hyH hyα hα hβ
  have hyβb : d.inv ω y ≠ η₂ ω d.r := fun he => hβ (he ▸ ⟨d.r, ⟨zero_le, le_rfl⟩, rfl⟩)
  have hyαβ : d.inv ω y ∉ η₁ ω '' Icc 0 d.u ∩ η₂ ω '' Icc 0 d.r := fun h' => hβ h'.2
  have hj := (hret y hyH hyβb hyα hyαβ).2.1
  have hj' := (hret' y hyH hyβb hyα hyαβ).2.1
  have he := hfn y fun h' => (Finset.mem_union.1 h').elim hj' hj
  rw [← he]
  exact hfst' y hyH hyα hα hβ

end Disj

end RLC

end InteractingSLE
