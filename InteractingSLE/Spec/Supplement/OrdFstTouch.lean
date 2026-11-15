/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.Aux85Wire
import InteractingSLE.Spec.Supplement.OrdFstSided

/-!
# Leaf 3, the first continuation: the sided touching word

Packet PROVE-T15-ORDDET3 (Theorem 1.5's leaf 3; Aux. lemmas 82–86, supplement pp. 296–301).

`RLC.RetTouchChartBoundaryStatement` (PROVE-T15-RET5, proved from Lemma 7.5 by `retTouchChartBoundaryStatement_of_zones`
with Aux. lemma 85, PROVE-T15-AUX85) produces the touching word with the UNSIDED first-path clause of
`Supp7.IsRetainedWord`. Its witness is the truncated touching word of Aux. lemma 85's zones, whose first-path sides
are `(J, M₁)` (height `−λ − θ₁χ`) and `(M₁, R₁)` (height `λ − θ₁χ`), with `M₁ = tipPos`. Since the witness is internal
to that proof, the proof of `RetChart.retTouchChartBoundaryStatement_of_parts` is repeated here verbatim with the four
proved inputs (`Aux85.retTouchZonesStatement`, `RetChart.retTouchSidesStatement`, `RetChart.retTouchClearStatement`,
`retCollarMeanStatement_of_lemma75`) and one more conclusion, the sided clause `IsRetainedWordFst`
(`isRetainedWordFst_touchWord`):

* `RetTouchChartBoundaryFstStatement` (a statement shape, not an input) and
  **`retTouchChartBoundaryFstStatement_of_lemma75`** (from Lemma 7.5 alone).

For Theorem 1.5; uses Lemma 7.5 only (R43/R48).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

universe u

namespace InteractingSLE

namespace RLC

open Supp7 Restart Sec6 LocalSets LQGMetric Sec7 Sec7.Lemma76F Sec7.Lemma76G Sec7.SideHeightBox RetTouch RetChart

/-- **The touching-pair chart boundary values with the sided first-path word**: `RetTouchChartBoundaryStatement` with
the additional conclusion `IsRetainedWordFst` relative to the first tip's chart point `tipPos`. Proved from Lemma 7.5
(`retTouchChartBoundaryFstStatement_of_lemma75`). -/
def RetTouchChartBoundaryFstStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ ≤ x₁ → θ₁ < θ₂ →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
    ∀ (d : RetData Ω), d.IsMeasGood →
      (∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
        (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t) →
    ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension b jumps u₀ →
    ∃ β : Ω → BoundaryWord, Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] β ∧
      IsRetChartBoundaryLimitOn κ P h η₁ η₂ ζ₁ ζ₂ u₀ d
        {ω | IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r ∧
          ¬ Disjoint (η₁ ω '' Icc 0 d.u) (η₂ ω '' Icc 0 d.r)} β ∧
      ∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r →
        ¬ Disjoint (η₁ ω '' Icc 0 d.u) (η₂ ω '' Icc 0 d.r) →
        (β ω).IsSorted ∧ 0 < tipPos d η₁ ω ∧ IsRetainedWord κ θ₁ θ₂ (η₁ ω) d.u (η₂ ω) d.r (d.inv ω) (β ω) ∧
        IsUntouchedWord b jumps (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) (d.inv ω) (β ω) ∧
        IsRetainedWordFst κ θ₁ (η₁ ω) d.u (η₂ ω) d.r (d.inv ω) (tipPos d η₁ ω) (β ω)

/-- **The sided touching word from Lemma 7.5** (the proof of `retTouchChartBoundaryStatement_of_parts`, with the four
proved inputs and the sided clause). -/
theorem retTouchChartBoundaryFstStatement_of_lemma75 (hL75 : Theorem15.Lemma75Statement.{u}) :
    RetTouchChartBoundaryFstStatement.{u} := by
  have hZ := Aux85.retTouchZonesStatement
  have hS := RetChart.retTouchSidesStatement
  have hCl := RetChart.retTouchClearStatement
  have hM := retCollarMeanStatement_of_lemma75 hL75
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω mΩ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hag u₀ hu₀
  set χ := QuantumZipper.chiC κ with hχ
  set g₁ := -sleLambda κ - θ₂ * χ with hg₁
  set g₂ := sleLambda κ - θ₂ * χ with hg₂
  set g₃ := -sleLambda κ - θ₁ * χ with hg₃
  set g₄ := sleLambda κ - θ₁ * χ with hg₄
  obtain ⟨c₀, hc₀, hc₀J, hc₀b⟩ := Restart.BoundaryWord.exists_fn_eq_strictMonoOn hb
  set m := capR d.u d.r with hm
  have hum : d.u < m := lt_capR_left d.u d.r
  have hrm : d.r < m := lt_capR_right d.u d.r
  obtain ⟨ηs₁, hsc₁, hsm₁, hs0₁, -, hsag₁, -, -⟩ := exists_capped_version hL75 hκ hκ4 hb hh hη₁ u₀ m
  obtain ⟨ηs₂, hsc₂, hsm₂, hs0₂, -, hsag₂, -, -⟩ := exists_capped_version hL75 hκ hκ4 hb hh hη₂ u₀ m
  have hζm₁ := measurable_lifetime_of_isFlowLine hη₁
  have hζm₂ := measurable_lifetime_of_isFlowLine hη₂
  set F := cstHist ηs₁ ηs₂ (fun ω => cutLife (ζ₁ ω) m) (fun ω => cutLife (ζ₂ ω) m) d.u d.r with hF
  have hFm : Measurable F := measurable_cstHist hsm₁ hsm₂ ((measurable_cutLife m).comp hζm₁)
    ((measurable_cutLife m).comp hζm₂) d.u d.r
  set d' := stopRet ηs₁ ηs₂ d.u d.r with hd'def
  have hd'F : @RetData.IsMeasGood Ω (MeasurableSpace.comap F inferInstance) d' :=
    isMeasGood_stopRet (ζ₁ := fun ω => cutLife (ζ₁ ω) m) (ζ₂ := fun ω => cutLife (ζ₂ ω) m) le_rfl hsc₁ hsc₂
      hs0₁ hs0₂
  have hd' : d'.IsMeasGood := RetData.IsMeasGood.mono_sigma hd'F hFm.comap_le
  set β := wordT d' c₀ g₁ g₂ g₃ g₄ with hβdef
  have hβF : Measurable[MeasurableSpace.comap F inferInstance] β :=
    @measurable_wordT Ω (MeasurableSpace.comap F inferInstance) d' hd'F c₀ g₁ g₂ g₃ g₄
  -- the retained σ-algebra
  have hFret : ∀ᵐ ω ∂P, F ω = retHist76 η₁ η₂ ζ₁ ζ₂ d.u d.r ω := by
    filter_upwards [hsag₁, hsag₂] with ω h1 h2
    have e1 : ηs₁ ω = cappedPath η₁ ζ₁ m ω := funext h1
    have e2 : ηs₂ ω = cappedPath η₂ ζ₂ m ω := funext h2
    simp only [hF, retHist76, cstHist, e1, e2]
    rfl
  have hβR : Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] β := by
    intro S hS
    obtain ⟨T, hT, hTS⟩ := hβF hS
    refine ⟨?_, ⟨retHist76 η₁ η₂ ζ₁ ζ₂ d.u d.r ⁻¹' T, ⟨T, hT, rfl⟩, ?_⟩⟩
    · rw [← hTS]; exact hFm hT
    · rw [← hTS]
      filter_upwards [hFret] with ω hω
      simp only [mem_preimage, hω]
  -- the pathwise facts at a touching ordinary pair
  have hpg₁ := ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₁
  have hpg₂ := ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₂
  have hword : ∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r →
      ¬ Disjoint (η₁ ω '' Icc 0 d.u) (η₂ ω '' Icc 0 d.r) →
      β ω = ((zoneDataT (d.fwd ω) (activeDomain (η₁ ω) d.u (η₂ ω) d.r) (d.inv ω) (η₁ ω) d.u (η₂ ω) d.r).word
        c₀ g₁ g₂ g₃ g₄).trunc ∧
      IsTouchZones (η₁ ω) d.u (η₂ ω) d.r (d.inv ω)
        (zoneDataT (d.fwd ω) (activeDomain (η₁ ω) d.u (η₂ ω) d.r) (d.inv ω) (η₁ ω) d.u (η₂ ω) d.r) ∧
      IsRetChart (η₁ ω) d.u (η₂ ω) d.r (d.fwd ω) (d.inv ω) (d.lift ω) ∧ ω ∈ d.E ∧
      d.K ω = prefixSet (η₁ ω) d.u (η₂ ω) d.r ∧ d.D ω = activeDomain (η₁ ω) d.u (η₂ ω) d.r ∧
      IsPathGood (η₁ ω) (ζ₁ ω) x₁ ∧ IsPathGood (η₂ ω) (ζ₂ ω) x₂ := by
    filter_upwards [hag, hsag₁, hsag₂, ae_im_nonneg_of_isFlowLine' hη₁, ae_im_nonneg_of_isFlowLine' hη₂, hpg₁, hpg₂]
      with ω hagω e₁ e₂ hi₁ hi₂ hp₁ hp₂ hp hnd
    obtain ⟨hG, a₁, a₂⟩ := hagω hp.1 hp.2.1
    have b₁ : ∀ s ≤ d.u, d'.η₁ ω s = η₁ ω s := fun s hs => by
      show hproj (ηs₁ ω (min s d.u)) = _
      rw [min_eq_left hs, e₁ s, capTime_eq_of_lt hp.1 hum hs, hproj_of_im_nonneg]
      exact hi₁ s ((ENNReal.coe_le_coe.2 hs).trans hp.1.le)
    have b₂ : ∀ t ≤ d.r, d'.η₂ ω t = η₂ ω t := fun t ht => by
      show hproj (ηs₂ ω (min t d.r)) = _
      rw [min_eq_left ht, e₂ t, capTime_eq_of_lt hp.2.1 hrm ht, hproj_of_im_nonneg]
      exact hi₂ t ((ENNReal.coe_le_coe.2 ht).trans hp.2.1.le)
    have hG' : ω ∈ d'.G := by
      intro t ht he
      have he' : d'.η₂ ω t = d'.η₂ ω d.r := he
      rw [b₂ t ht.le, b₂ d.r le_rfl] at he'
      have := (Sec7.IsPathGood.injOn_Icc hp₂ hp.2.1.le) ⟨zero_le, ht.le⟩ ⟨zero_le, le_rfl⟩ he'
      exact (ne_of_lt ht) this
    have hE : ω ∈ d.E := hd.mem_E_of_ordinary hG a₁ a₂ hp
    obtain ⟨hEiff, -, hch⟩ := RetData.chart_eq_of_agree (d := d) (G' := d'.G) (η₁' := d'.η₁) (η₂' := d'.η₂)
      hG hG' (fun s hs => (b₁ s hs).trans (a₁ s hs).symm) (fun t ht => (b₂ t ht).trans (a₂ t ht).symm)
    have hE' : ω ∈ d'.E := hEiff.2 hE
    have hcheq : d'.chart ω = d.chart ω := hch
    rw [RetData.chart_of_mem hE', RetData.chart_of_mem hE] at hcheq
    have hfwd : d'.fwd ω = d.fwd ω := (Prod.ext_iff.1 hcheq).1
    have hinv : d'.inv ω = d.inv ω := (Prod.ext_iff.1 (Prod.ext_iff.1 hcheq).2).1
    have hC : IsRetChart (η₁ ω) d.u (η₂ ω) d.r (d.fwd ω) (d.inv ω) (d.lift ω) :=
      (isRetChart_congr a₁ a₂).1 (hd.isRetChart hE).2
    have hDeq : d.D ω = activeDomain (η₁ ω) d.u (η₂ ω) d.r := by
      rw [hd.D_of_mem hE]
      exact activeDomain_congr_Icc (fun s hs => a₁ s hs.2) (fun t ht => a₂ t ht.2)
    have ht := hZ (η₁ ω) (η₂ ω) (ζ₁ ω) (ζ₂ ω) x₁ x₂ d.u d.r (d.fwd ω) (d.inv ω) (d.lift ω) hp₁ hp₂ hx hp hnd hC
    have htip₃ : ∀ s < d.u, η₁ ω s ≠ η₁ ω d.u := fun s hs he =>
      (ne_of_lt hs) ((Sec7.IsPathGood.injOn_Icc hp₁ hp.1.le) ⟨zero_le, hs.le⟩ ⟨zero_le, le_rfl⟩ he)
    refine ⟨?_, ht, hC, hE, ?_, hDeq, hp₁, hp₂⟩
    · have ht' : IsTouchZones (η₁ ω) d'.u (η₂ ω) d'.r (d'.inv ω)
          (zoneDataT (d'.fwd ω) (activeDomain (η₁ ω) d'.u (η₂ ω) d'.r) (d'.inv ω) (η₁ ω) d'.u (η₂ ω) d'.r) := by
        rw [hfwd, hinv]; exact ht
      rw [hβdef, wordT_eq hd' hE' b₁ b₂ ht' hp.2.2.2.2.2.2.1 hp.2.2.2.2.2.1 htip₃ hc₀ g₁ g₂ g₃ g₄, hfwd, hinv]
      rfl
    · rw [RetData.K_of_mem hE]; exact prefixSet_congr' a₁ a₂
  refine ⟨β, hβR, ?_, ?_⟩
  · intro ηc₁ ηc₂ g hc₁ hc₂ hm₁ hm₂ hag₁ hag₂ hg
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
    have hdrv₁ : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W₁ t ω) (ζ₁ ω) (fun t => η₁ ω t - x₁) ∧
        ContinuousOn (fun t => W₁ t ω) {s | (s : ℝ≥0∞) < ζ₁ ω} ∧ W₁ 0 ω = 0 := by
      filter_upwards [htr₁, hcoup₁.1.2.2.2.2] with ω h1 h2 using ⟨h1, h2.2.2.2.1, h2.1⟩
    have hdrv₂ : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W₂ t ω) (ζ₂ ω) (fun t => η₂ ω t - x₂) ∧
        ContinuousOn (fun t => W₂ t ω) {s | (s : ℝ≥0∞) < ζ₂ ω} ∧ W₂ 0 ω = 0 := by
      filter_upwards [htr₂, hcoup₂.1.2.2.2.2] with ω h1 h2 using ⟨h1, h2.2.2.2.1, h2.1⟩
    have hcol := hM κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d.u d.r u₀ hu₀ W₁ W₂ hdrv₁
      hdrv₂ ηc₁ ηc₂ g G₁ G₂ hc₁ hc₂ hm₁ hm₂ hag₁ hag₂ hg hG₁ hG₂
    filter_upwards [hword, hag₁, hag₂, hdrv₁, hdrv₂, hC₁, hC₂, hS₁, hS₂, hdec, hG₁.2.1, hG₂.2.1, hcol]
      with ω hwordω e₁ e₂ hdrv₁ω hdrv₂ω hC₁ω hC₂ω hS₁ω hS₂ω hdecω hR₁ω hR₂ω hcolω hp v hv hvrep
    obtain ⟨hp, hnd⟩ := hp
    obtain ⟨hβω, ht, hC, hE, hK, hDeq, hp₁, hp₂⟩ := hwordω hp hnd
    obtain ⟨htr₁ω, hWc₁ω, hW0₁ω⟩ := hdrv₁ω
    obtain ⟨htr₂ω, hWc₂ω, hW0₂ω⟩ := hdrv₂ω
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
    obtain ⟨hcm₁, hcm₂⟩ := hcolω hp hnd v vA₁ vA₂ hv hvrep hvA₁ hvA₁r hvA₂ hvA₂r
    have hdec' := hdecω v hv hvrep
    have hcmp₁ := hC₁ω v vA₁ hv hvrep hvA₁ hvA₁r
    have hcmp₂ := hC₂ω v vA₂ hv hvrep hvA₂ hvA₂r
    rw [hU] at hdec' hcmp₁ hcmp₂
    rw [hA₁] at hcmp₁
    rw [hA₂] at hcmp₂
    have hsh₁ := hS₁ω hp.1 vA₁ hvA₁ hvA₁r
    have hsh₂ := hS₂ω hp.2.1 vA₂ hvA₂ hvA₂r
    -- positivity of the cutoffs
    have hu0 : 0 < d.u := by
      refine pos_iff_ne_zero.2 fun h0 => ?_
      have h1 : (0 : ℝ) < (η₁ ω d.u).im := hp.2.2.1
      rw [h0, Sec7.IsPathGood.zero hp₁] at h1
      simp at h1
    have hr0 : 0 < d.r := by
      refine pos_iff_ne_zero.2 fun h0 => ?_
      have h1 : (0 : ℝ) < (η₂ ω d.r).im := hp.2.2.2.1
      rw [h0, Sec7.IsPathGood.zero hp₂] at h1
      simp at h1
    -- the inputs in the retained chart
    obtain ⟨hfun₁, hfun₂⟩ := hS (η₁ ω) (η₂ ω) (ζ₁ ω) (ζ₂ ω) x₁ x₂ d.u d.r (d.fwd ω) (d.inv ω) (d.lift ω)
      (fun t => W₁ t ω) (fun t => W₂ t ω) hp₁ hp₂ hx hp hnd hC ht htr₁ω hWc₁ω hW0₁ω htr₂ω hWc₂ω hW0₂ω
    obtain ⟨hcl₁, hcl₂⟩ := hCl (η₁ ω) (η₂ ω) (ζ₁ ω) (ζ₂ ω) x₁ x₂ d.u d.r (d.fwd ω) (d.inv ω) (d.lift ω)
      (fun t => W₁ t ω) (fun t => W₂ t ω) hp₁ hp₂ hx hp hnd hC ht htr₁ω hWc₁ω hW0₁ω htr₂ω hWc₂ω hW0₂ω
    rw [← hDeq] at hcm₁ hcm₂
    obtain ⟨E, hEf, hlim⟩ := exists_finite_tendsto_touchWord_of_clear (χ := χ) (g₁ := g₁) (g₂ := g₂) (g₃ := g₃)
      (g₄ := g₄) hd hE ht hC hp₁ hp₂ hp.1 hp.2.1 hu0 hr0 hK htr₁ω hWc₁ω hW0₁ω htr₂ω hWc₂ω hW0₂ω hfun₁ hfun₂
      hu₀.2.2 hdec' hcmp₁ hcmp₂ (fun p F hF hFle y hy => hsh₁ p F hF hFle y hy)
      (fun p F hF hFle y hy => hsh₂ p F hF hFle y hy) hcl₁ hcl₂ hcm₁ hcm₂ hc₀ hc₀J hc₀b
    refine ⟨E, hEf, fun w hw => ?_⟩
    rw [hβω, BoundaryWord.trunc_fn]
    exact hlim w hw
  · filter_upwards [hword] with ω hω hp hnd
    obtain ⟨hβω, ht, -, -, -, hDeq, -, -⟩ := hω hp hnd
    rw [hβω]
    have e : tipPos d η₁ ω =
        (zoneDataT (d.fwd ω) (activeDomain (η₁ ω) d.u (η₂ ω) d.r) (d.inv ω) (η₁ ω) d.u (η₂ ω) d.r).M₁ := by
      simp only [tipPos, zoneDataT, chartPt, hDeq]
    refine ⟨(GoodT.word_isSorted ht.good hc₀).trunc, ?_, isRetainedWord_touchWord ht hc₀ κ θ₁ θ₂,
      isUntouchedWord_touchWord ht hc₀ hc₀J hc₀b g₁ g₂ g₃ g₄, ?_⟩
    · rw [e]
      exact ht.zero_lt_M₁
    · rw [e]
      exact isRetainedWordFst_touchWord ht hc₀ κ θ₁ g₁ g₂

end RLC

end InteractingSLE
