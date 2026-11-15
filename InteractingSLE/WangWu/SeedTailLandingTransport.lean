/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.SeedTailLandingSlit

/-!
# The lower arc's initial segment in the reverse slit chart

PROVE-WW-B27. Reparametrize the initial segment by `a * discTime t`; its image
is a proper arc because the original endpoint maps to the chart's infinity.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology Metric Complex Bornology
open QuantumZipper (H Hbar fwdMap fwdHull)
open scoped NNReal ENNReal

namespace InteractingSLE.WangWu.SeedTail

open ImgWord

theorem tendsto_discTime_atTop : Tendsto discTime atTop (𝓝 (1 : ℝ)) := by
  have hi : Tendsto (fun t : ℝ => (1 + t)⁻¹) atTop (𝓝 0) :=
    (tendsto_atTop_add_const_left _ 1 tendsto_id).inv_tendsto_atTop
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub hi
  rw [sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  dsimp only [discTime]
  field_simp
  ring

/-- The initial segment stops exactly at the root of the given tail. -/
theorem preContact_initial_eq {β : ℝ → ℂ} {G : Set ℂ} (hβ : IsProperArc β)
    {a : ℝ} (ha : 0 < a) (hG : G = β '' Ici a) : preContact β G = Ico 0 a := by
  apply preContact_eq_Ico_of_first ha
  · rw [hG]
    exact ⟨a, self_mem_Ici, rfl⟩
  · intro t ht
    rw [hG]
    rintro ⟨b, hb, he⟩
    have h := hβ.inj (ha.le.trans hb) ht.1 he
    rw [h] at hb
    exact (not_le.2 ht.2) hb

/-- The reverse chart sends approach to the tail's root along the initial
segment to infinity. -/
theorem norm_imgCurve_initial_tendsto {w : ℝ → ℝ} {η β : ℝ → ℂ} {s a : ℝ}
    (hw : Continuous w) (hw0 : w 0 = 0) (hη : IsLoewnerTrace w η) (hηp : IsProperArc η)
    (hβ : IsProperArc β) (hs : 0 < s) (ha : 0 < a)
    (htail : negInv '' fwdHull w s = β '' Ici a) (htip : negInv (η s) = β a) :
    Tendsto (fun t => ‖imgCurve w s β t‖) (𝓝[<] a) atTop := by
  have hP := preContact_initial_eq hβ ha htail
  have hmem : ∀ᶠ t in 𝓝[<] a, negInv (β t) ∈ H \ fwdHull w s := by
    filter_upwards [Ioo_mem_nhdsLT ha] with t ht
    apply negInv_notMem_fwdHull
    refine ⟨hβ.mem_H t ht.1, ?_⟩
    have hp : t ∈ preContact β (negInv '' fwdHull w s) := hP ▸ ⟨ht.1.le, ht.2⟩
    exact hp.2 t ⟨ht.1.le, le_rfl⟩
  have hβa : negInv (β a) = η s := by rw [← htip, negInv_negInv]
  have hβlim : Tendsto (fun t => negInv (β t)) (𝓝[<] a) (𝓝[H \ fwdHull w s] (η s)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, hmem⟩
    rw [← hβa]
    exact ((continuousAt_negInv (ne_zero_of_mem_H (hβ.mem_H a ha))).tendsto.comp
      ((hβ.cont.continuousAt (Ici_mem_nhds ha)).tendsto)).mono_left nhdsWithin_le_nhds
  have hf := (tendsto_fwdMap_tip hη hηp hw hw0 hs).comp hβlim
  have hfn : Tendsto (fun t => ‖fwdMap w s (negInv (β t))‖) (𝓝[<] a) (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨by simpa only [norm_zero, Function.comp_def] using hf.norm, ?_⟩
    filter_upwards [hmem] with t ht
    exact norm_pos_iff.2 (ne_zero_of_mem_H (QuantumZipper.FwdHolo.mapsTo_fwdMap hw hs.le ht))
  apply (tendsto_inv_nhdsGT_zero.comp hfn).congr'
  filter_upwards [Ioo_mem_nhdsLT ha] with t ht
  rw [imgCurve_of_pos ht.1, revChart, norm_negInv]
  rfl

/-- The mapped initial segment, parametrized on the whole positive half-line,
is a proper arc. -/
theorem isProperArc_initialImage {w : ℝ → ℝ} {η β : ℝ → ℂ} {s a : ℝ}
    (hw : Continuous w) (hw0 : w 0 = 0) (hη : IsLoewnerTrace w η) (hηp : IsProperArc η)
    (hβ : IsProperArc β) (hs : 0 < s) (ha : 0 < a)
    (htail : negInv '' fwdHull w s = β '' Ici a) (htip : negInv (η s) = β a) :
    IsProperArc (fun t => imgCurve w s β (a * discTime t)) := by
  have hG : IsClosed (negInv '' fwdHull w s) := by rw [htail]; exact Descent.isClosed_image_Ici hβ ha.le
  have hK := isKilledArc_imgCurve hw hw0 hs.le hG hβ
  rw [preContact_initial_eq hβ ha htail] at hK
  have hr : ∀ t, 0 ≤ t → a * discTime t ∈ Ico 0 a := by
    intro t ht
    exact ⟨mul_nonneg ha.le (discTime_mem_Ico ht).1,
      by simpa only [mul_one] using mul_lt_mul_of_pos_left (discTime_mem_Ico ht).2 ha⟩
  have hc : ContinuousOn (fun t : ℝ => a * discTime t) (Ici 0) := by
    apply continuousOn_const.mul
    exact continuousOn_id.div (continuousOn_const.add continuousOn_id) fun t ht => by
      change 1 + t ≠ 0
      linarith only [show 0 ≤ t from ht]
  have hrend : Tendsto (fun t : ℝ => a * discTime t) atTop (𝓝[<] a) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · simpa only [mul_one] using (tendsto_const_nhds (x := a)).mul tendsto_discTime_atTop
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      exact (hr t ht).2
  refine ⟨hK.cont.comp hc hr, ?_, ?_, ?_,
    (norm_imgCurve_initial_tendsto hw hw0 hη hηp hβ hs ha htail htip).comp hrend⟩
  · intro u hu v hv he
    have he' := hK.inj (hr u hu) (hr v hv) he
    have hm : StrictMonoOn (fun t => a * discTime t) (Ici (0 : ℝ)) :=
      fun t ht t' _ htt' => mul_lt_mul_of_pos_left (discTime_lt_discTime ht htt') ha
    exact hm.injOn hu hv he'
  · simpa only [discTime, zero_div, mul_zero] using hK.zero
  · intro t ht
    apply hK.mem_H _ (hr t ht.le)
    exact mul_pos ha (div_pos ht (by linarith))

/-- The chart has a positive real boundary value at the positive real anchor
`1`; this fixes which component is the right side of the mapped arc. -/
theorem exists_pos_revChart_limit_one {w : ℝ → ℝ} {η : ℝ → ℂ} {s : ℝ}
    (hw : Continuous w) (hw0 : w 0 = 0) (hη : IsLoewnerTrace w η) (hηp : IsProperArc η)
    (hs : 0 ≤ s) : ∃ r : ℝ, 0 < r ∧ Tendsto (revChart w s) (𝓝[H] (1 : ℂ)) (𝓝 (r : ℂ)) := by
  obtain ⟨v, hv⟩ := exists_isForwardSol_of_isProperArc hη hηp hw hw0 (x := -1) (by norm_num) hs
  have hvF : fwdMap w s ((-1 : ℝ) : ℂ) = v s := fwdMap_eq_of_isForwardSol hw hv ⟨hs, le_rfl⟩
  have hvneg : (v s).re < 0 := by
    rw [← hvF]
    exact re_fwdMap_neg hw hw0 hs (by norm_num : (-1 : ℝ) < 0) hv
  have hvreal : v s = ((v s).re : ℂ) := eq_ofReal_re_of_im_eq_zero
    (im_eq_zero_of_isForwardSol_real hw hv ⟨hs, le_rfl⟩)
  have hInv : Tendsto negInv (𝓝[H] (1 : ℂ)) (𝓝[H] ((-1 : ℝ) : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun z hz => negInv_mem_H hz⟩
    simpa only [negInv, inv_one, ofReal_neg, ofReal_one] using
      (continuousAt_negInv one_ne_zero).tendsto.mono_left nhdsWithin_le_nhds
  have hf := (tendsto_fwdMap_of_isForwardSol_real hw hw0 hs hv).comp hInv
  have h := (continuousAt_negInv (hv.2 s ⟨hs, le_rfl⟩).1).tendsto.comp hf
  have hval : negInv (v s) = ((-((v s).re)⁻¹ : ℝ) : ℂ) := by
    rw [hvreal]
    simp only [negInv, ofReal_inv, ofReal_neg, ofReal_re]
  refine ⟨-((v s).re)⁻¹, neg_pos.2 (inv_lt_zero.2 hvneg), ?_⟩
  have heq : revChart w s = negInv ∘ (fwdMap w s ∘ negInv) := rfl
  rw [heq]
  simpa only [hval, Function.comp_def] using h

/-- The planar side transport for a proper arc whose reversed tail is the
frozen slit. Connectedness and the positive anchor select the right component. -/
theorem reversedTailSideTransportStatement : ReversedTailSideTransportStatement := by
  intro w η β s a hw hw0 hη hηp hβ hs ha htail htip
  let χ := fun t => imgCurve w s β (a * discTime t)
  have hχ : IsProperArc χ := isProperArc_initialImage hw hw0 hη hηp hβ hs ha htail htip
  have hD : rightSideOf (arcRange β) ⊆ H \ negInv '' fwdHull w s := by
    intro z hz
    refine ⟨hz.1.1, ?_⟩
    rw [htail]
    rintro ⟨t, ht, he⟩
    exact hz.1.2 ⟨t, ha.le.trans ht, he⟩
  have hχD : revChart w s '' rightSideOf (arcRange β) ⊆ H \ arcRange χ := by
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨revChart_mem_H hw hs.le (hD hz), ?_⟩
    rintro ⟨t, ht, he⟩
    rcases (show 0 ≤ t from ht).eq_or_lt with ht0 | ht0
    · subst t
      rw [hχ.zero] at he
      have hh := revChart_mem_H hw hs.le (hD hz)
      rw [← he] at hh
      exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from hh)
    · have hr0 : 0 < a * discTime t := mul_pos ha (div_pos ht0 (by linarith))
      have hra : a * discTime t < a := by
        simpa only [mul_one] using mul_lt_mul_of_pos_left (discTime_mem_Ico ht0.le).2 ha
      have hrD : β (a * discTime t) ∈ H \ negInv '' fwdHull w s := by
        refine ⟨hβ.mem_H _ hr0, ?_⟩
        have hp := preContact_initial_eq hβ ha htail
        have hrP : a * discTime t ∈ preContact β (negInv '' fwdHull w s) := hp ▸ ⟨hr0.le, hra⟩
        exact hrP.2 _ ⟨hr0.le, le_rfl⟩
      have hχt : χ t = revChart w s (β (a * discTime t)) := imgCurve_of_pos hr0
      rw [hχt] at he
      have hβz := injOn_revChart hw hw0 hs.le hrD (hD hz) he
      exact hz.1.2 ⟨a * discTime t, hr0.le, hβz⟩
  have hcont := (continuousOn_revChart hw hs.le).mono hD
  obtain ⟨r, hr, hlim⟩ := exists_pos_revChart_limit_one hw hw0 hη hηp hs.le
  obtain ⟨ε, hε, hεR⟩ := hβ.exists_ball_inter_H_subset_rightSideOf (by norm_num : (0 : ℝ) < 1)
  have hR : ∀ᶠ z in 𝓝[H] (1 : ℂ), z ∈ rightSideOf (arcRange β) := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (ball_mem_nhds (1 : ℂ) hε), self_mem_nhdsWithin] with z hz hzH
    exact hεR ⟨hz, hzH⟩
  have : (𝓝[H] (1 : ℂ)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (by
    rw [closure_H]
    exact (show (0 : ℝ) ≤ (1 : ℂ).im from le_refl _))
  have hrcl : (r : ℂ) ∈ closure (revChart w s '' rightSideOf (arcRange β)) :=
    mem_closure_of_tendsto hlim (hR.mono fun z hz => mem_image_of_mem _ hz)
  refine ⟨χ, hχ, fun z hz => ?_⟩
  have hcpt : revChart w s '' rightSideOf (arcRange β) ⊆
      connectedComponentIn (H \ arcRange χ) (revChart w s z) :=
    (hβ.isPreconnected_rightSideOf.image _ hcont).subset_connectedComponentIn
      (mem_image_of_mem _ hz) hχD
  exact ⟨hχD (mem_image_of_mem _ hz), r, hr, hχ.ofReal_notMem_arcRange hr.ne', closure_mono hcpt hrcl⟩

end InteractingSLE.WangWu.SeedTail
