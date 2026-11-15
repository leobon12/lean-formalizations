/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma76GLimit
import InteractingSLE.Spec.Sec7.Lemma76GMeas

/-!
# Lemma 7.6's chart boundary values: `Lemma76ChartBoundaryStatement`

Packet PROVE-LEMMA76G (specification §7.2, proof of Lemma 7.6, pp. 268–269). The named input
`Sec7.Lemma76ChartBoundaryStatement` of PROVE-T15-CLOSE1 is proved from Lemma 7.5:

* the datum is the measurable word `wordM` of the stopped retained data of capped versions of the two flow lines
  (`Lemma76GMeas`), measurable for the retained σ-algebra `retSigma76`;
* at a disjoint pair it is the truncated zone word (`wordM_eq_of_setting`): the original data on the untouched real
  boundary, `−λ − θ₂χ` and `λ − θ₂χ` on the two sides of the second prefix, `−λ − θ₁χ` and `λ − θ₁χ` on the two sides
  of the first prefix, the original data again right of the junction;
* its datum is the boundary value of the conditional mean in the retained chart outside finitely many chart points
  (`isRetChartBoundaryLimit_wordM`, from `Lemma76GLimit`);
* it is sorted and has the right-side heights (`isRightSideHeights_word`; at the junction `R₁ = T(b₁⁺)` the right
  limit is the original right limit at `b₁`, the rightmost real point of the first prefix).

## Main results

* **`lemma76ChartBoundaryStatement_of_lemma75`**: `Lemma75Statement → Lemma76ChartBoundaryStatement`;
* **`lemma76CondDetHeightsStatement_of_det`**, **`lemma76Statement_of_det`**: Lemma 7.6's conditional-law input and
  Lemma 7.6 from Lemma 7.5 and (Det) alone.
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

/-! ### The measurable word at a disjoint pair -/

section Pathwise

variable {Ω : Type*} [MeasurableSpace Ω] {d : RetData Ω}

theorem realSet_congr {α α' : ℝ≥0 → ℂ} {a : ℝ≥0} (h : ∀ s ≤ a, α' s = α s) : realSet α' a = realSet α a := by
  ext x
  simp only [realSet, mem_ofPred_eq]
  rw [image_congr fun s hs => h s hs.2]

/-- **At a disjoint pair the measurable word is the truncated zone word.** -/
theorem wordM_eq_of_setting (hd : d.IsMeasGood) {ω : Ω} (hE : ω ∈ d.E) {α β : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞}
    {x₁ x₂ : ℝ} {ψ' : ℂ → ℂ} {lift' : ℂ → ℝ} (hs : IsSetting α ζ₁ x₁ d.u β ζ₂ x₂ d.r (d.fwd ω) ψ' lift')
    (h₁ : ∀ s ≤ d.u, d.η₁ ω s = α s) (h₂ : ∀ t ≤ d.r, d.η₂ ω t = β t) {c₀ : BoundaryWord}
    (hc₀ : StrictMonoOn c₀.2.1 (Iio c₀.1)) (g₁ g₂ g₃ g₄ : ℝ) :
    wordM d c₀ g₁ g₂ g₃ g₄ ω = ((zoneData (d.fwd ω) α d.u β d.r).word c₀ g₁ g₂ g₃ g₄).trunc := by
  set z := zoneData (d.fwd ω) α d.u β d.r with hzdef
  have hz := hs.zoneData_good
  have hDeq : d.D ω = activeDomain α d.u β d.r := by
    rw [hd.D_of_mem hE]
    exact activeDomain_congr_Icc (fun s hs => h₁ s hs.2) (fun t ht => h₂ t ht.2)
  have hi₁ : d.η₁ ω '' Icc 0 d.u = α '' Icc 0 d.u := image_congr fun s hs => h₁ s hs.2
  have hi₂ : d.η₂ ω '' Icc 0 d.r = β '' Icc 0 d.r := image_congr fun t ht => h₂ t ht.2
  have hA₂ : A₂ d ω = z.a₂ := by
    simp only [A₂, indicator_of_mem hE, baseL, realSet_congr h₂, hzdef, zoneData]
  have hB₂ : B₂ d ω = z.b₂ := by
    simp only [B₂, indicator_of_mem hE, baseR, realSet_congr h₂, hzdef, zoneData]
  have hA₁ : A₁ d ω = z.a₁ := by
    simp only [A₁, indicator_of_mem hE, baseL, realSet_congr h₁, hzdef, zoneData]
  have hB₁ : B₁ d ω = z.b₁ := by
    simp only [B₁, indicator_of_mem hE, baseR, realSet_congr h₁, hzdef, zoneData]
  -- chart points of untouched points
  have hTpt : ∀ (xf : Ω → ℝ) (x : ℝ), xf ω = x → IsUntouched α d.u β d.r x → Tpt d xf ω = z.T x := by
    intro xf x hxf hx
    have hmem : ω ∈ ptEv d xf := by
      refine ⟨⟨hE, ?_⟩, ?_, ?_⟩
      · show ((xf ω : ℝ) : ℂ) ∈ closure (d.D ω)
        rw [hxf, hDeq]; exact hx.2
      · show ((xf ω : ℝ) : ℂ) ∉ d.η₁ ω '' Icc 0 d.u
        rw [hxf, hi₁]; exact fun h => hx.1 (Or.inl h)
      · show ((xf ω : ℝ) : ℂ) ∉ d.η₂ ω '' Icc 0 d.r
        rw [hxf, hi₂]; exact fun h => hx.1 (Or.inr h)
    simp only [Tpt, indicator_of_mem hmem, hxf, hDeq, hzdef, zoneData]
  have hzone := fun x hx => hs.untouched_of_zone (φ := d.fwd ω) (x := x) hx
  -- the five chart points of the zones
  have hL₂ : (⨆ n : ℕ, Tpt d (fun ω => A₂ d ω - 1 / ((n : ℝ) + 1)) ω) = z.L₂ := by
    have := congrArg ZW.L₂ hs.zoneDataM_eq
    simp only [zoneDataM] at this
    rw [hzdef, ← this]
    refine iSup_congr fun n => hTpt _ _ (by rw [hA₂]; rfl) (hzone _ (Or.inl ?_))
    exact sub_lt_self _ (one_div_succ_pos n)
  have hc : 0 < z.a₁ - z.b₂ := sub_pos.2 hz.b₂_lt_a₁
  have hR₂ : (⨅ n : ℕ, Tpt d (fun ω => B₂ d ω + (A₁ d ω - B₂ d ω) / ((n : ℝ) + 2)) ω) = z.R₂ := by
    have := congrArg ZW.R₂ hs.zoneDataM_eq
    simp only [zoneDataM] at this
    rw [hzdef, ← this]
    refine iInf_congr fun n => hTpt _ _ (by rw [hA₁, hB₂]; rfl) (hzone _ (Or.inr (Or.inl ?_)))
    exact ⟨lt_add_of_pos_right _ (div_succ_succ_pos hc n), lt_sub_iff_add_lt'.1 (div_succ_succ_lt hc n)⟩
  have hL₁ : (⨆ n : ℕ, Tpt d (fun ω => A₁ d ω - (A₁ d ω - B₂ d ω) / ((n : ℝ) + 2)) ω) = z.L₁ := by
    have := congrArg ZW.L₁ hs.zoneDataM_eq
    simp only [zoneDataM] at this
    rw [hzdef, ← this]
    refine iSup_congr fun n => hTpt _ _ (by rw [hA₁, hB₂]; rfl) (hzone _ (Or.inr (Or.inl ?_)))
    exact ⟨lt_sub_comm.2 (div_succ_succ_lt hc n), sub_lt_self _ (div_succ_succ_pos hc n)⟩
  have hR₁ : (⨅ n : ℕ, Tpt d (fun ω => B₁ d ω + 1 / ((n : ℝ) + 1)) ω) = z.R₁ := by
    have := congrArg ZW.R₁ hs.zoneDataM_eq
    simp only [zoneDataM] at this
    rw [hzdef, ← this]
    refine iInf_congr fun n => hTpt _ _ (by rw [hB₁]; rfl) (hzone _ (Or.inr (Or.inr ?_)))
    exact lt_add_of_pos_right _ (one_div_succ_pos n)
  have hM₁ : (tipEv d).indicator (fun ω => chartPt (d.fwd ω) (d.D ω) (d.η₁ ω d.u)) ω = z.M₁ := by
    have hαa : d.η₁ ω d.u = α d.u := h₁ d.u le_rfl
    have hmem : ω ∈ tipEv d := by
      refine ⟨⟨hE, ?_⟩, ?_, ?_⟩
      · show d.η₁ ω d.u ∈ closure (d.D ω)
        rw [hαa, hDeq]; exact hs.hpair.2.2.2.2.2
      · show d.η₁ ω d.u ∉ d.η₂ ω '' Icc 0 d.r
        rw [hαa, hi₂]; exact fun h => Set.disjoint_left.1 hs.disj ⟨d.u, ⟨zero_le, le_rfl⟩, rfl⟩ h
      · intro s hs' he
        rw [h₁ s hs'.le, hαa] at he
        exact (ne_of_lt hs') (hs.hi₁ ⟨zero_le, hs'.le⟩ ⟨zero_le, le_rfl⟩ he)
    simp only [indicator_of_mem hmem, hαa, hDeq, hzdef, zoneData]
  -- assemble
  rw [trunc_word_eq_zbuild z c₀ g₁ g₂ g₃ g₄ rfl]
  simp only [wordM, hA₂, hB₂, hA₁, hB₁, hL₂, hR₂, hL₁, hR₁, hM₁]
  refine zbuild_congr (ZW.k₄_le (z := z) (c₀ := c₀)) fun i hi => ?_
  have hiN : i < c₀.1 := by
    rcases hi with hi | ⟨-, hi⟩ | ⟨-, hi⟩
    · exact lt_of_lt_of_le hi (card_filter_le_range _)
    · exact lt_of_lt_of_le hi (card_filter_le_range _)
    · exact hi
  refine hTpt _ _ rfl (hzone _ ?_)
  rcases hi with hi | ⟨hi2, hi3⟩ | ⟨hi4, -⟩
  · exact Or.inl ((ZW.lt_k₁_iff (z := z) hc₀ hiN).1 hi)
  · refine Or.inr (Or.inl ⟨not_le.1 fun h => ?_, (ZW.lt_k₃_iff (z := z) hc₀ hiN).1 hi3⟩)
    have := (ZW.lt_k₂_iff (z := z) hc₀ hiN).2 h
    have e2 : z.k₂ c₀ = cntLe c₀ z.b₂ := rfl
    omega
  · refine Or.inr (Or.inr (not_le.1 fun h => ?_))
    have := (ZW.lt_k₄_iff (z := z) hc₀ hiN).2 h
    have e4 : z.k₄ c₀ = cntLe c₀ z.b₁ := rfl
    omega

/-- **The right-side heights of the zone word** (in the setting of a disjoint pair): right of the first tip, on the
first prefix, the datum is `λ − θ₁χ` off the junction `R₁ = T(b₁⁺)`, where the right limit is the original right
limit at `b₁`, the rightmost real point of the first prefix. -/
theorem isRightSideHeights_word {α β : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞} {x₁ x₂ : ℝ} {a b : ℝ≥0} {φ ψ : ℂ → ℂ}
    {lift : ℂ → ℝ} (hs : IsSetting α ζ₁ x₁ a β ζ₂ x₂ b φ ψ lift) {c₀ : BoundaryWord}
    (hc₀ : StrictMonoOn c₀.2.1 (Iio c₀.1)) {b' : ℝ → ℝ} {J : Finset ℝ} (hc₀b : ∀ y ∉ J, c₀.fn y = b' y)
    (κ θ₁ θ₂ : ℝ) :
    IsRightSideHeights κ θ₁ b' α a ψ (((zoneData φ α a β b).word c₀ (-sleLambda κ - θ₂ * QuantumZipper.chiC κ)
      (sleLambda κ - θ₂ * QuantumZipper.chiC κ) (-sleLambda κ - θ₁ * QuantumZipper.chiC κ)
      (sleLambda κ - θ₁ * QuantumZipper.chiC κ)).trunc) := by
  set z := zoneData φ α a β b with hzdef
  have hz := hs.zoneData_good
  intro y w hw _ hwy u' hu' hy
  have hwM : w = z.M₁ := ofReal_injective (hs.chartPt_tip₁.2.2 w (ofReal_mem_Hbar w) hw)
  rw [hwM] at hwy
  have hyα : ψ y ∈ α '' Icc 0 a := ⟨u', ⟨zero_le, hu'.le⟩, hy.symm⟩
  have hyR : y ≤ z.R₁ := hs.le_R₁_of_mem₁ hyα
  rw [BoundaryWord.trunc_jumps]
  have hfn : (z.word c₀ (-sleLambda κ - θ₂ * QuantumZipper.chiC κ) (sleLambda κ - θ₂ * QuantumZipper.chiC κ)
      (-sleLambda κ - θ₁ * QuantumZipper.chiC κ) (sleLambda κ - θ₁ * QuantumZipper.chiC κ)).trunc.fn =
      (z.word c₀ (-sleLambda κ - θ₂ * QuantumZipper.chiC κ) (sleLambda κ - θ₂ * QuantumZipper.chiC κ)
      (-sleLambda κ - θ₁ * QuantumZipper.chiC κ) (sleLambda κ - θ₁ * QuantumZipper.chiC κ)).fn :=
    funext fun t => BoundaryWord.trunc_fn _ t
  rw [hfn]
  rcases hyR.lt_or_eq with hlt | heq
  · exact Or.inl ⟨ZW.notMem_jumps_side₄ hz hc₀ hwy hlt, ZW.fn_side₄ hz hc₀ hwy hlt⟩
  · subst heq
    refine Or.inr ⟨ZW.R₁_mem_jumps, Or.inr ?_⟩
    have hR := hs.inv_R₁
    rw [hy] at hR
    refine ⟨by rw [hR]; simp, fun s hs' hs0 => ?_, ?_⟩
    · rw [hR, ofReal_re]
      exact (re_mem_Icc_base hs.hp₁ hs.ha ⟨s, ⟨zero_le, hs'⟩, rfl⟩ hs0).2
    · rw [hR, ofReal_re]
      exact ZW.rightLim_fn_R₁ hz hc₀ hc₀b

end Pathwise

/-! ### The statement -/

/-- **`Lemma76ChartBoundaryStatement` from Lemma 7.5** (proof of Lemma 7.6, pp. 268–269). The datum is the measurable
word of the stopped retained data of capped versions of the two flow lines. -/
theorem lemma76ChartBoundaryStatement_of_lemma75 (hL75 : Theorem15.Lemma75Statement.{u}) :
    Lemma76ChartBoundaryStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx _ Ω mΩ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hag u₀ hu₀
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
  set β := wordM d' c₀ g₁ g₂ g₃ g₄ with hβdef
  have hβF : Measurable[MeasurableSpace.comap F inferInstance] β :=
    @measurable_wordM Ω (MeasurableSpace.comap F inferInstance) d' hd'F c₀ g₁ g₂ g₃ g₄
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
  -- the pathwise facts at a disjoint pair
  have hpg₁ := ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₁
  have hpg₂ := ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₂
  have hword : ∀ᵐ ω ∂P, Lemma76Exit.IsDisjointPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r →
      β ω = ((zoneData (d.fwd ω) (η₁ ω) d.u (η₂ ω) d.r).word c₀ g₁ g₂ g₃ g₄).trunc ∧
      IsSetting (η₁ ω) (ζ₁ ω) x₁ d.u (η₂ ω) (ζ₂ ω) x₂ d.r (d.fwd ω) (d.inv ω) (d.lift ω) ∧ ω ∈ d.E ∧
      d.K ω = prefixSet (η₁ ω) d.u (η₂ ω) d.r := by
    filter_upwards [hag, hsag₁, hsag₂, ae_im_nonneg_of_isFlowLine' hη₁, ae_im_nonneg_of_isFlowLine' hη₂, hpg₁, hpg₂]
      with ω hagω e₁ e₂ hi₁ hi₂ hp₁ hp₂ hp
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
    have hE : ω ∈ d.E := mem_E_of_isDisjointPair hd hG a₁ a₂ hp
    obtain ⟨hEiff, -, hch⟩ := RetData.chart_eq_of_agree (d := d) (G' := d'.G) (η₁' := d'.η₁) (η₂' := d'.η₂)
      hG hG' (fun s hs => (b₁ s hs).trans (a₁ s hs).symm) (fun t ht => (b₂ t ht).trans (a₂ t ht).symm)
    have hE' : ω ∈ d'.E := hEiff.2 hE
    have hfwd : d'.fwd ω = d.fwd ω := by
      have h' : d'.chart ω = d.chart ω := hch
      rw [RetData.chart_of_mem hE', RetData.chart_of_mem hE] at h'
      exact (Prod.ext_iff.1 h').1
    have hC : IsRetChart (η₁ ω) d.u (η₂ ω) d.r (d.fwd ω) (d.inv ω) (d.lift ω) :=
      (isRetChart_congr a₁ a₂).1 (hd.isRetChart hE).2
    have hs : IsSetting (η₁ ω) (ζ₁ ω) x₁ d.u (η₂ ω) (ζ₂ ω) x₂ d.r (d.fwd ω) (d.inv ω) (d.lift ω) :=
      ⟨hp₁, hp₂, hx, hp, hC⟩
    have hs' : IsSetting (η₁ ω) (ζ₁ ω) x₁ d.u (η₂ ω) (ζ₂ ω) x₂ d.r (d'.fwd ω) (d.inv ω) (d.lift ω) := by
      rw [hfwd]; exact hs
    refine ⟨?_, hs, hE, ?_⟩
    · rw [hβdef, wordM_eq_of_setting hd' hE' hs' b₁ b₂ hc₀, hfwd]
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
  · filter_upwards [hword] with ω hω hp
    obtain ⟨hβω, hs, -, -⟩ := hω hp
    rw [hβω]
    exact ⟨(ZW.word_isSorted hs.zoneData_good hc₀).trunc, isRightSideHeights_word hs hc₀ hc₀b κ θ₁ θ₂⟩

/-- **The mean identification of Lemma 7.6 from Lemma 7.5** (`Lemma76MeanIdentStatement`). -/
theorem lemma76MeanIdentStatement_of_lemma75 (hL75 : Theorem15.Lemma75Statement.{u}) :
    Lemma76MeanIdentStatement.{u} :=
  lemma76MeanIdentStatement_of_chartBoundary hL75 (lemma76ChartBoundaryStatement_of_lemma75 hL75)

/-- **Lemma 7.6's conditional-law input from Lemma 7.5 and (Det)** (`Lemma76CondDetHeightsStatement`). -/
theorem lemma76CondDetHeightsStatement_of_det (hL75 : Theorem15.Lemma75Statement.{u})
    (hDet : Lemma76DetStatement.{u}) : Lemma76CondDetHeightsStatement.{u} :=
  lemma76CondDetHeightsStatement_of_chartBoundary hL75 (lemma76ChartBoundaryStatement_of_lemma75 hL75) hDet

/-- **Lemma 7.6** from Theorem 1.2 (word-measurable form), Theorem 1.3, Lemma 7.5 and (Det). -/
theorem lemma76Statement_of_det (h12p : Exist.Staged.Theorem12ParamStatement.{0})
    (h13 : Exist.Theorem13Statement.{0}) (hL75 : Theorem15.Lemma75Statement.{u})
    (hDet : Lemma76DetStatement.{u}) : Lemma76Statement.{u} :=
  lemma76Statement_of_chartBoundary h12p h13 hL75 (lemma76ChartBoundaryStatement_of_lemma75 hL75) hDet

end Lemma76G

end Sec7

end InteractingSLE
