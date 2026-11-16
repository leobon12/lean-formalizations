/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.RealContact.TermFrozen

/-!
# The relative chain and configuration of an explorer against a completed path (builder frame)

Packet PROVE-RC-TERM, second run (ruling R124). SB2(1)'s configuration builder
`Theorem14.SB.Bq.exists_relConfig_bridgePath_noTip`, applied to a generating-trace explorer `β` from `0` and a
completed retained path with entry data (`Term.IsEntryData`), with the side input from W5 (`exists_side_completion`):

* `image_inv_diff_eq`: in a domain chart of `ℍ ∖ fill F₁`, if a relative hull `K̃` contains the chart image of the
  physical hull `fill F₂` off `fill F₁` and its frontier comes from `fill F₂`, the chart inverse maps `ℍ ∖ K̃` onto
  `ℍ ∖ (fill F₁ ∪ fill F₂)` (the image is open and relatively closed in the complement of the union, which is
  connected by Janiszewski's theorem in `ℍ`);
* `eq_fwd_of_entryInv_eq`: a point of `ℍ̄` over a free point of the retained path is its forward chart value (the
  forward map is continuous at alive points);
* **`exists_relChain_config`**: for a prefix time `a` before the explorer's lifetime and before its first positive
  contact with the retained path, and every stop `S₀ < a`: a proper completion `β'`, the proper lift `γ` with
  `γ s = entryChart.1 (β s)` on `(0, a]`, the relative chain `IsSB2RelChain`, the hull identity at every `s ≤ S₀`,
  and SB2(1)'s configuration `IsRelConfigJK` at every explored time `s ∈ (0, S₀]` with tip in `ℍ`.

Deterministic; R48-neutral.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex Bornology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull logDerivFwd IsForwardSol)

namespace InteractingSLE.RealContact

namespace Term

open Supp9B HalfPlaneSep Theorem14 Theorem14.SB Theorem14.SB.FinRel
open Sec7.Lemma71C (capClock)
open Supp8.Q3Chain (flowedData flowedJumps initJumps)

/-! ### The hull identity -/

/-- **The chart inverse maps the complement of the relative hull onto the complement of the union.** -/
theorem image_inv_diff_eq {c : Chart} {F₁ F₂ Kt : Set ℂ} (hD : IsDomainChart (H \ fillH F₁) c)
    (hF₁ : IsCompact F₁) (hF₂ : IsCompact F₂)
    (hC : ∀ w ∈ F₁ ∩ F₂, ∃ P ⊆ F₁ ∩ F₂, IsPreconnected P ∧ w ∈ P ∧ ∃ x ∈ P, x.im = 0)
    (hKt : Kt ⊆ H) (hKto : IsOpen (H \ Kt)) (hKtn : (H \ Kt).Nonempty)
    (hin : ∀ z ∈ fillH F₂, z ∉ fillH F₁ → c.1 z ∈ Kt)
    (hfr : ∀ z ∈ H \ fillH F₁, c.1 z ∈ frontier Kt → z ∈ fillH F₂) :
    c.2.1 '' (H \ Kt) = H \ (fillH F₁ ∪ fillH F₂) := by
  set O := H \ (fillH F₁ ∪ fillH F₂) with hO
  have hF : IsCompact (F₁ ∪ F₂) := hF₁.union hF₂
  have hOeq : O = H \ fillH (F₁ ∪ F₂) := by
    ext z
    constructor
    · rintro ⟨hzH, hz⟩
      exact H_diff_fillH_inter_subset hF₁ hF₂ hC
        ⟨⟨hzH, fun h => hz (Or.inl h)⟩, ⟨hzH, fun h => hz (Or.inr h)⟩⟩
    · rintro ⟨hzH, hz⟩
      exact ⟨hzH, fun h => h.elim (fun h1 => hz (fillH_mono subset_union_left h1))
        (fun h2 => hz (fillH_mono subset_union_right h2))⟩
  have hOpre : IsPreconnected O := hOeq ▸ isPreconnected_H_diff_fillH hF.isClosed hF.isBounded
  have hOo : IsOpen O := hOeq ▸ isOpen_H_diff_fillH hF.isBounded
  have hinj : InjOn c.2.1 H := hD.1.injOn
  -- the image lies in the complement of the union
  have hCO : c.2.1 '' (H \ Kt) ⊆ O := by
    rintro _ ⟨v, hv, rfl⟩
    have hz : c.2.1 v ∈ H \ fillH F₁ := hD.inv_mem hv.1
    refine ⟨hz.1, fun h => h.elim hz.2 fun h2 => hv.2 ?_⟩
    have := hin _ h2 hz.2
    rwa [hD.fwd_inv hv.1] at this
  have hCo : IsOpen (c.2.1 '' (H \ Kt)) := hD.1.isOpen_image_of_subset hKto sdiff_subset
  -- the rest of the complement is open
  have hIo : IsOpen (c.2.1 '' interior Kt) :=
    hD.1.isOpen_image_of_subset isOpen_interior (interior_subset.trans hKt)
  have hrest : O ⊆ c.2.1 '' (H \ Kt) ∪ c.2.1 '' interior Kt := by
    intro z hz
    have hzD : z ∈ H \ fillH F₁ := ⟨hz.1, fun h => hz.2 (Or.inl h)⟩
    have hv : c.1 z ∈ H := hD.fwd_mem hzD
    have he : c.2.1 (c.1 z) = z := hD.inv_fwd hzD
    by_cases hvK : c.1 z ∈ Kt
    · refine Or.inr ⟨c.1 z, ?_, he⟩
      by_contra hni
      have hfrz : c.1 z ∈ frontier Kt := ⟨subset_closure hvK, hni⟩
      exact hz.2 (Or.inr (hfr z hzD hfrz))
    · exact Or.inl ⟨c.1 z, ⟨hv, hvK⟩, he⟩
  have hdisj : Disjoint (c.2.1 '' (H \ Kt)) (c.2.1 '' interior Kt) := by
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨v, hv, rfl⟩ ⟨v', hv', hvv'⟩
    have hv'K : v' ∈ Kt := interior_subset hv'
    have : v' = v := hinj (hKt hv'K) hv.1 hvv'
    exact hv.2 (this ▸ hv'K)
  have hne : (O ∩ c.2.1 '' (H \ Kt)).Nonempty := by
    obtain ⟨v, hv⟩ := hKtn
    exact ⟨c.2.1 v, hCO ⟨v, hv, rfl⟩, ⟨v, hv, rfl⟩⟩
  exact Subset.antisymm hCO (hOpre.subset_left_of_subset_union hCo hIo hdisj hrest hne)

/-! ### The lift over a free point -/

variable {V : ℝ → ℝ} {ξ : ℝ → ℂ} {p d : ℝ}

/-- A free point of the translated completed path, translated back, is alive at the horizon. -/
theorem IsEntryData.alive_of_isFreeAt {T : ℝ} (h : IsEntryData V T ξ p d) {z : ℂ} (hz : 0 ≤ z.im)
    (hzd : z ≠ d) (hf : IsFreeAt (entryPath ξ T d '' Icc 0 1) z) :
    ∃ u, IsForwardSol V (z - (d : ℂ)) T u := by
  have hncl := notMem_closure_of_isFreeAt hf
  rw [h.fillH_entryPath] at hncl
  have hncl' : z - (d : ℂ) ∉ closure (fwdHull V T) := by
    intro hmem
    refine hncl ?_
    have hcont : Continuous fun w : ℂ => w + (d : ℂ) := continuous_id.add continuous_const
    have := image_closure_subset_closure_image hcont ⟨z - (d : ℂ), hmem, rfl⟩
    simpa only [sub_add_cancel] using this
  rcases hz.lt_or_eq with hpos | hzero
  · -- an interior point off the hull
    have hH : z - (d : ℂ) ∈ H := by
      show 0 < (z - (d : ℂ)).im
      simpa only [sub_im, ofReal_im, sub_zero] using hpos
    exact QuantumZipper.exists_isForwardSol_of_not_mem_fwdHull h.tip.pos.le hH fun hK => hncl' (subset_closure hK)
  · -- a real point off the closed hull
    have hzr : z - (d : ℂ) = ((z.re - d : ℝ) : ℂ) :=
      Complex.ext (by simp) (by simp [← hzero])
    rw [hzr] at hncl' ⊢
    refine Aux10.exists_isForwardSol_of_notMem_closure h.tip.cont h.tip.zero h.tip.pos.le (fun h0 => hzd ?_) hncl'
    exact Complex.ext (by rw [ofReal_re]; linarith) (by rw [ofReal_im]; exact hzero.symm)

/-- **The lift over a free point is the forward chart value.** -/
theorem IsEntryData.eq_fwd_of_entryInv_eq {T : ℝ} (h : IsEntryData V T ξ p d) {v z : ℂ} (hv : 0 ≤ v.im)
    (hvz : entryInv V T d v = z) (hz : 0 ≤ z.im) (hzd : z ≠ d)
    (hf : IsFreeAt (entryPath ξ T d '' Icc 0 1) z) : v = (entryChart V T d).1 z := by
  have hV := h.tip.cont
  have hV0 := h.tip.zero
  have hT := h.tip.pos.le
  obtain ⟨u, hu⟩ := h.alive_of_isFreeAt hz hzd hf
  have hc : ContinuousAt (entryChart V T d).1 z := by
    have h1 := continuousAt_fwdMap_of_alive hV hT hu
    have h2 : ContinuousAt (fun w : ℂ => w - (d : ℂ)) z := (continuous_id.sub continuous_const).continuousAt
    have h12 : ContinuousAt (fun w : ℂ => fwdMap V T (w - (d : ℂ))) z :=
      ContinuousAt.comp (f := fun w : ℂ => w - (d : ℂ)) (g := fwdMap V T) h1 h2
    exact h12.sub continuousAt_const
  -- approach `v` from `ℍ`
  set vn : ℕ → ℂ := fun n => v + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * I with hvn
  have hvnH : ∀ n, vn n ∈ H := fun n => by
    show 0 < (v + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * I).im
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    simp only [add_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
    linarith
  have hlim : Tendsto vn atTop (𝓝 v) := by
    have h0 : Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * I) atTop (𝓝 ((0 : ℝ) * I)) :=
      ((Complex.continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat).mul_const I
    have := (tendsto_const_nhds (x := v)).add h0
    simpa only [ofReal_zero, zero_mul, add_zero] using this
  have hgc := h.continuousOn_entryInv
  have hg : Tendsto (fun n => entryInv V T d (vn n)) atTop (𝓝 (entryInv V T d v)) := by
    have hcw : ContinuousWithinAt (entryInv V T d) {w | 0 ≤ w.im} v := hgc v hv
    exact hcw.tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall fun n =>
      show 0 ≤ (vn n).im from le_of_lt (hvnH n)⟩)
  rw [hvz] at hg
  have hfw : Tendsto (fun n => (entryChart V T d).1 (entryInv V T d (vn n))) atTop
      (𝓝 ((entryChart V T d).1 z)) := hc.tendsto.comp hg
  have heq : ∀ n, (entryChart V T d).1 (entryInv V T d (vn n)) = vn n := fun n => by
    rw [entryInv_eqOn hV hV0 hT d (hvnH n)]
    exact (isConformal_entryChart hV hV0 hT d).2.2 _ (hvnH n)
  simp only [heq] at hfw
  exact tendsto_nhds_unique hlim hfw

/-! ### The builder -/

section Builder

variable {nL nR nL' nR' : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
  {ρL' : Fin nL' → ℝ} {ρR' : Fin nR' → ℝ} {xL' : Fin nL' → ℝ} {xR' : Fin nR' → ℝ}

/-- **The relative chain and configuration of an explorer prefix against a completed path** (see the module
docstring). -/
theorem exists_relChain_config (κ χ : ℝ)
    (hxL : ∀ i, xL i ≤ 0) (hxR : ∀ j, 0 ≤ xR j) (hxL' : ∀ i, xL' i ≤ 0) (hxR' : ∀ j, 0 ≤ xR' j)
    {T : ℝ≥0} (hE : IsEntryData V (T : ℝ) ξ p d) (hp : 0 < p)
    (hne : ∀ s : ℝ, 0 < s → s ≤ T → ξ s + (d : ℂ) ≠ 0)
    {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {β : ℝ≥0 → ℂ} (hβ : IsGeneratingTrace w ζ β)
    (hw : ContinuousOn w {s : ℝ≥0 | (s : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0) {a : ℝ≥0} (ha : (a : ℝ≥0∞) < ζ)
    (hinj : InjOn β (Icc 0 a)) (hH : ∀ t ≤ a, 0 ≤ (β t).im)
    (hoff : ∀ t ≤ a, 0 < t → β t ∉ (fun t : ℝ≥0 => ξ (t : ℝ) + (d : ℂ)) '' Icc 0 T)
    (hW : ∀ c : ℝ≥0, c < T → HasOrderedProperCompletions (fun t : ℝ≥0 => ξ (t : ℝ) + (d : ℂ)) c β a)
    {S₀ : ℝ} (hS₀ : 0 ≤ S₀) (hS₀a : S₀ < a) :
    ∃ (β' γ : ℝ≥0 → ℂ) (Wr : ℝ → ℝ) (ηr : ℝ → ℂ),
      IsProperCompletion β a β' ∧ IsProperCurve γ ∧ γ 0 = 0 ∧
      (∀ s : ℝ≥0, 0 < s → s ≤ a → γ s = (entryChart V T d).1 (β s)) ∧
      IsSB2RelChain (entryPath ξ T d '' Icc 0 1) (entryChart V T d) β' γ 0 S₀ Wr ηr ∧
      (∀ s ∈ Icc (0 : ℝ) S₀, (entryChart V T d).2.1 ''
          (H \ fwdHull Wr (capClock (fun r : ℝ => γ r.toNNReal) s)) =
        H \ (fillH (entryPath ξ T d '' Icc 0 1) ∪ fillH (β '' Icc 0 s.toNNReal))) ∧
      ∀ (wg : ℝ → ℝ) (ηg : ℝ → ℂ) (s : ℝ), s ∈ Ioc 0 S₀ → Continuous wg → wg 0 = 0 → IsLoewnerTrace wg ηg →
        fwdHull wg s = fillH (β '' Icc 0 s.toNNReal) → (∀ r ∈ Icc (0 : ℝ) s, ηg r = β r.toNNReal) →
        ηg s ∈ H →
        ∃ (LΨ : ℂ → ℂ) (G₀ GE G : ℂ → ℝ),
          EqOn (entryChart V T d).2.2 (fun z => (LΨ z).im) (H \ fillH (entryPath ξ T d '' Icc 0 1)) ∧
          IsRelConfigJK (fillH (entryPath ξ T d '' Icc 0 1)) (entryChart V T d).1 (entryChart V T d).2.1 LΨ ∅
            wg Wr ηg ηr s (capClock (fun r : ℝ => γ r.toNNReal) s) χ (Real.pi / Real.sqrt κ)
            (forceBoundaryData κ ρL ρR xL xR) (flowedData κ ρL' ρR' xL' xR' wg s)
            (flowedData κ ρL ρR xL xR Wr (capClock (fun r : ℝ => γ r.toNNReal) s)) (initJumps xL xR)
            (flowedJumps xL' xR' wg s) (flowedJumps xL xR Wr (capClock (fun r : ℝ => γ r.toNNReal) s))
            G₀ GE G
            (fun z => G (fwdMap Wr (capClock (fun r : ℝ => γ r.toNNReal) s) ((entryChart V T d).1 z)) -
              χ * ((logDerivFwd Wr (capClock (fun r : ℝ => γ r.toNNReal) s) ((entryChart V T d).1 z)).im +
                (LΨ z).im)) := by
  have hV := hE.tip.cont
  have hV0 := hE.tip.zero
  have hT := hE.tip.pos.le
  have ha0 : (0 : ℝ) < a := lt_of_le_of_lt hS₀ hS₀a
  have ha0' : 0 < a := NNReal.coe_pos.1 ha0
  set q := entryPath ξ (T : ℝ) d with hq
  set c := entryChart V (T : ℝ) d with hc
  set g := entryInv V (T : ℝ) d with hg
  obtain ⟨β', hβ', hA⟩ := exists_side_completion hE hp hne hβ hw hw0 ha hinj hH hoff hW
  have hPβ' := isProperCurve_of_isProperCompletion hβ'
  have hagree : ∀ t ≤ a, β' t = β t := hβ'.2.2.2.2
  have hβ'0 : β' 0 = 0 := by rw [hagree 0 zero_le, hβ.1]
  have hQim : q '' Icc 0 1 = (fun t : ℝ≥0 => ξ (t : ℝ) + (d : ℂ)) '' Icc 0 T := image_entryPath_eq hE.tip.pos ξ d
  -- no open time interval on the retained path or on the real line
  have hnA : interior {r ∈ Ioo (0 : ℝ) a | β' r.toNNReal ∈ q '' Icc 0 1} = ∅ := by
    have hemp : {r ∈ Ioo (0 : ℝ) a | β' r.toNNReal ∈ q '' Icc 0 1} = ∅ := by
      refine eq_empty_iff_forall_notMem.2 fun r hr => ?_
      have hra : r.toNNReal ≤ a := Real.toNNReal_le_iff_le_coe.2 hr.1.2.le
      have hr0 : 0 < r.toNNReal := Real.toNNReal_pos.2 hr.1.1
      have hmem := hr.2
      rw [hagree _ hra, hQim] at hmem
      exact hoff _ hra hr0 hmem
    rw [hemp, interior_empty]
  have hnR : interior {r ∈ Ioo (0 : ℝ) a | β' r.toNNReal ∈ {z : ℂ | z.im = 0}} = ∅ := by
    have hLT := hβ.isLoewnerTraceLT (t₂ := (a : ℝ)) (by rw [ENNReal.ofReal_coe_nnreal]; exact ha)
    have hwc : ContinuousOn w (Iic ((a : ℝ)).toNNReal) := by
      rw [Real.toNNReal_coe]
      exact hw.mono fun s hs => show (s : ℝ≥0∞) < ζ from lt_of_le_of_lt (ENNReal.coe_le_coe.2 hs) ha
    have hI := interior_real_times_eq_empty hLT (continuous_frozenDrive hwc)
      (by rw [frozenDrive_zero ha0.le, hw0])
    have hset : {r ∈ Ioo (0 : ℝ) a | β' r.toNNReal ∈ {z : ℂ | z.im = 0}} =
        {r ∈ Ioo (0 : ℝ) a | (β r.toNNReal).im = 0} := by
      ext r
      constructor
      · rintro ⟨hr, hm⟩
        refine ⟨hr, ?_⟩
        rw [← hagree _ (Real.toNNReal_le_iff_le_coe.2 hr.2.le)]
        exact hm
      · rintro ⟨hr, hm⟩
        refine ⟨hr, ?_⟩
        show (β' r.toNNReal).im = 0
        rw [hagree _ (Real.toNNReal_le_iff_le_coe.2 hr.2.le)]
        exact hm
    rw [hset]
    exact hI
  obtain ⟨γ, hγ, hγ0, hlift, Wr, ηr, hch, hcfg⟩ := Bq.exists_relConfig_bridgePath_noTip (κ := κ) (χ := χ)
    (ρL := ρL) (ρR := ρR) (ρL' := ρL') (ρR' := ρR') hxL hxR hxL' hxR' hE.continuousOn_entryPath
    hE.entryPath_zero hE.seed (fun s hs => hE.im_entryPath_nonneg hs) (fun y hy => hE.real_entryPath_nonneg hy)
    rfl hE.isLeftEntryChart hE.continuousOn_entryInv (entryInv_eqOn hV hV0 hT d) hE.finite_fibre
    (liftRealOn_entryChart hV hV0 hT d) hPβ' hβ'0 hA hS₀ hS₀a hnA hnR
  -- the lift on the prefix
  have hQ := hE.isRetPath hp hne
  have hc' : ContinuousOn β (Icc 0 a) := hβ.2.1.mono fun t ht =>
    show (t : ℝ≥0∞) ≤ ζ from (ENNReal.coe_le_coe.2 ht.2).trans ha.le
  have hPre : IsExpPrefix β a (fun t : ℝ≥0 => ξ (t : ℝ) + (d : ℂ)) T := ⟨hc', hH, hβ.1, hoff⟩
  have hγeq : ∀ s : ℝ≥0, 0 < s → s ≤ a → γ s = c.1 (β s) := by
    intro s hs0 hsa
    have hfree := isFreeAt_explorer hQ hPre hW hsa hs0
    rw [← hQim] at hfree
    have hzd : β s ≠ (d : ℂ) := fun h => by
      refine hoff s hsa hs0 ⟨0, ⟨le_rfl, zero_le⟩, ?_⟩
      show ξ ((0 : ℝ≥0) : ℝ) + (d : ℂ) = β s
      rw [NNReal.coe_zero, hE.tip.trace.1, zero_add, h]
    exact hE.eq_fwd_of_entryInv_eq (hγ.2.2.1 s) ((hlift s).trans (hagree s hsa)) (hH s hsa) hzd hfree
  -- the hull identity
  have hch' := hch
  obtain ⟨hWr, hWr0, hηr, -, -, -, hchain⟩ := hch'
  have hhull : ∀ s ∈ Icc (0 : ℝ) S₀, c.2.1 '' (H \ fwdHull Wr (capClock (fun r : ℝ => γ r.toNNReal) s)) =
      H \ (fillH (q '' Icc 0 1) ∪ fillH (β '' Icc 0 s.toNNReal)) := by
    intro s hs
    obtain ⟨hu0, -, -, hin, hfr⟩ := hchain s hs
    have hsa : s.toNNReal ≤ a := Real.toNNReal_le_iff_le_coe.2 (hs.2.trans hS₀a.le)
    have himg : β' '' Icc 0 (0 + s.toNNReal) = β '' Icc 0 s.toNNReal := by
      rw [zero_add]
      exact image_congr fun t ht => hagree t (ht.2.trans hsa)
    rw [himg] at hin hfr
    have hF₁ : IsCompact (q '' Icc 0 1) := isCompact_Icc.image_of_continuousOn hE.continuousOn_entryPath
    have hF₂ : IsCompact (β '' Icc 0 s.toNNReal) :=
      isCompact_Icc.image_of_continuousOn (hc'.mono (Icc_subset_Icc_right hsa))
    have hC : ∀ z ∈ q '' Icc 0 1 ∩ β '' Icc 0 s.toNNReal, ∃ P ⊆ q '' Icc 0 1 ∩ β '' Icc 0 s.toNNReal,
        IsPreconnected P ∧ z ∈ P ∧ ∃ x ∈ P, x.im = 0 := by
      rintro z ⟨hzq, ⟨t, ht, rfl⟩⟩
      have ht0 : t = 0 := by
        by_contra hne0
        rw [hQim] at hzq
        exact hoff t (ht.2.trans hsa) (pos_iff_ne_zero.2 hne0) hzq
      subst ht0
      refine ⟨{β 0}, ?_, isPreconnected_singleton, rfl, β 0, rfl, by rw [hβ.1, zero_im]⟩
      rintro _ rfl
      exact ⟨hzq, ⟨0, ⟨le_rfl, zero_le⟩, rfl⟩⟩
    have hKtH : fwdHull Wr (capClock (fun r : ℝ => γ r.toNNReal) s) ⊆ H := fun _ hz => hz.1
    have hKto : IsOpen (H \ fwdHull Wr (capClock (fun r : ℝ => γ r.toNNReal) s)) := by
      rw [← QuantumZipper.RS.image_fwdMapInv_H hWr hWr0 hu0]
      exact (Chart.isConformal_id.loewner hWr hWr0 hu0).isOpen_image
    have hKtn : (H \ fwdHull Wr (capClock (fun r : ℝ => γ r.toNNReal) s)).Nonempty := by
      rw [← QuantumZipper.RS.image_fwdMapInv_H hWr hWr0 hu0]
      exact ⟨_, ⟨I, by show (0 : ℝ) < I.im; simp, rfl⟩⟩
    exact image_inv_diff_eq hE.isDomainChart hF₁ hF₂ hC hKtH hKto hKtn hin hfr
  refine ⟨β', γ, Wr, ηr, hβ', hγ, hγ0, hγeq, hch, hhull, ?_⟩
  intro wg ηg s hs hwg hwg0 hηg hKg hag hηH
  have hsa : s.toNNReal ≤ a := Real.toNNReal_le_iff_le_coe.2 (hs.2.trans hS₀a.le)
  have himg : β' '' Icc 0 s.toNNReal = β '' Icc 0 s.toNNReal :=
    image_congr fun t ht => hagree t (ht.2.trans hsa)
  refine hcfg wg ηg s hs hwg hwg0 hηg (by rw [himg]; exact hKg) (fun r hr => ?_) hηH
  rw [hag r hr, hagree _ (Real.toNNReal_le_iff_le_coe.2 (hr.2.trans (hs.2.trans hS₀a.le)))]

end Builder

end Term

end InteractingSLE.RealContact
