/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.PocketMirrorDisc

/-!
# Marked intervals and negative boundary preimages of a contact-gap pocket

PROVE-POCKETSHAPE. Increasing contact order identifies the closure interval on
each complete crosscut. A negatively oriented boundary arc covers the negative
real half-line by the intermediate value theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Filter Topology Bornology Metric Function
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.PocketMirror

open WangWu Sec7.PocketCoord Sec7.PocketJordan

/-- The right crosscut meets the closure of its gap pocket at exactly the gap times. -/
theorem right_closure_interval_of_contactGap {α β : ℝ → ℂ}
    (hα : IsDiscCrosscut α) (hβ : IsDiscCrosscut β)
    (hjm : StrictMonoOn (contactMap α β) (Sec7.pocketContactSet α β))
    {a b : ℝ} (hg : IsContactGap α β a b) :
    {s ∈ Icc (0 : ℝ) 1 | α s ∈ closure (jordanIn (pocketCurve α β a b))} = Icc a b := by
  obtain ⟨hJ, -, hd, hfr, -⟩ := pocket_props_of_strictMono hα hβ hjm hg
  have hDo := isOpen_jordanIn hJ
  obtain ⟨hja, hjb⟩ := contactMap_mem_Icc hβ hg
  apply Subset.antisymm
  · rintro s ⟨hs01, hscl⟩
    have hsfr : α s ∈ frontier (jordanIn (pocketCurve α β a b)) := by
      rw [hDo.frontier_eq]
      exact ⟨hscl, fun h => disjoint_left.1 hd h (Or.inl ⟨s, hs01, rfl⟩)⟩
    rw [hfr] at hsfr
    rcases hsfr with ⟨r, hr, he⟩ | ⟨r, hr, he⟩
    · exact hα.inj ⟨hg.1.1.1.trans hr.1, hr.2.trans hg.2.1.1.2⟩ hs01 he ▸ hr
    · have hr01 : r ∈ Icc (0 : ℝ) 1 := ⟨hja.1.trans hr.1, hr.2.trans hjb.2⟩
      have hsC : s ∈ Sec7.pocketContactSet α β := ⟨hs01, r, hr01, he⟩
      have hj : contactMap α β s = r := contactMap_eq hβ hr01 he.symm
      refine ⟨le_of_not_gt (fun h => ?_), le_of_not_gt (fun h => ?_)⟩
      · have hh := hjm hsC hg.1 h
        rw [hj] at hh
        exact not_lt_of_ge hr.1 hh
      · have hh := hjm hg.2.1 hsC h
        rw [hj] at hh
        exact not_lt_of_ge hr.2 hh
  · intro s hs
    refine ⟨⟨hg.1.1.1.trans hs.1, hs.2.trans hg.2.1.1.2⟩, ?_⟩
    exact frontier_subset_closure (image_subset_frontier_pocket_left hα hβ hjm hg ⟨s, hs, rfl⟩)

/-- The left crosscut meets the closure of the pocket at precisely the matching contact times. -/
theorem left_closure_interval_of_contactGap {α β : ℝ → ℂ}
    (hα : IsDiscCrosscut α) (hβ : IsDiscCrosscut β)
    (hjm : StrictMonoOn (contactMap α β) (Sec7.pocketContactSet α β))
    {a b : ℝ} (hg : IsContactGap α β a b) :
    {s ∈ Icc (0 : ℝ) 1 | β s ∈ closure (jordanIn (pocketCurve α β a b))} =
      Icc (contactMap α β a) (contactMap α β b) := by
  obtain ⟨hJ, -, hd, hfr, -⟩ := pocket_props_of_strictMono hα hβ hjm hg
  have hDo := isOpen_jordanIn hJ
  obtain ⟨hja, hjb⟩ := contactMap_mem_Icc hβ hg
  apply Subset.antisymm
  · rintro s ⟨hs01, hscl⟩
    have hsfr : β s ∈ frontier (jordanIn (pocketCurve α β a b)) := by
      rw [hDo.frontier_eq]
      exact ⟨hscl, fun h => disjoint_left.1 hd h (Or.inr ⟨s, hs01, rfl⟩)⟩
    rw [hfr] at hsfr
    rcases hsfr with ⟨r, hr, he⟩ | ⟨r, hr, he⟩
    · have hr01 : r ∈ Icc (0 : ℝ) 1 := ⟨hg.1.1.1.trans hr.1, hr.2.trans hg.2.1.1.2⟩
      have hrC : r ∈ Sec7.pocketContactSet α β := ⟨hr01, s, hs01, he.symm⟩
      have hj : contactMap α β r = s := contactMap_eq hβ hs01 he
      exact ⟨hj ▸ hjm.monotoneOn hg.1 hrC hr.1, hj ▸ hjm.monotoneOn hrC hg.2.1 hr.2⟩
    · exact hβ.inj ⟨hja.1.trans hr.1, hr.2.trans hjb.2⟩ hs01 he ▸ hr
  · intro s hs
    refine ⟨⟨hja.1.trans hs.1, hs.2.trans hjb.2⟩, ?_⟩
    exact frontier_subset_closure (image_subset_frontier_pocket hα hβ hjm hg ⟨s, hs, rfl⟩)

/-- A negatively oriented marked boundary arc covers every negative real value. -/
theorem exists_negative_boundary_preimage {α : ℝ → ℂ} (hα : IsDiscCrosscut α)
    {D : Set ℂ} (hDo : IsOpen D) (hDα : Disjoint D (crossRange α))
    {a b : ℝ} (ha0 : 0 ≤ a) (hab : a < b) (hb1 : b ≤ 1)
    (hI : {s ∈ Icc (0 : ℝ) 1 | α s ∈ closure D} = Icc a b)
    {Ψ : ℂ → ℂ} (hU : IsBdryUniformizer D (α a) (α b) Ψ)
    (hneg : ∀ s ∈ Ioo a b, (Ψ (α s)).re < 0) {x : ℝ} (hx : x < 0) :
    ∃ s ∈ Ioo a b, Ψ (α s) = x := by
  let E := closure D \ {α b}
  have hE : ∀ s ∈ Ico a b, α s ∈ E := by
    intro s hs
    refine ⟨?_, fun he => hs.2.ne (hα.inj ⟨ha0.trans hs.1, hs.2.le.trans hb1⟩
      ⟨ha0.trans hab.le, hb1⟩ he)⟩
    have hm : s ∈ {s ∈ Icc (0 : ℝ) 1 | α s ∈ closure D} := by rw [hI]; exact Ico_subset_Icc_self hs
    exact hm.2
  have hreal : ∀ s ∈ Ico a b, (Ψ (α s)).im = 0 := by
    intro s hs
    apply hU.im_eq_zero hDo (fun h => disjoint_left.1 hDα h ⟨b, ⟨ha0.trans hab.le, hb1⟩, rfl⟩)
    · rw [hDo.frontier_eq]
      exact ⟨(hE s hs).1, fun h => disjoint_left.1 hDα h ⟨s, ⟨ha0.trans hs.1, hs.2.le.trans hb1⟩, rfl⟩⟩
    · exact (hE s hs).2
  have hcont : ContinuousOn (fun s => Ψ (α s)) (Ico a b) :=
    hU.cont.comp (hα.cont.mono fun s hs => ⟨ha0.trans hs.1, hs.2.le.trans hb1⟩) hE
  have hlim : Tendsto α (𝓝[Ioo a b] b) (𝓝[E] (α b)) := tendsto_nhdsWithin_iff.2
    ⟨((hα.cont b ⟨ha0.trans hab.le, hb1⟩).tendsto).mono_left
      (nhdsWithin_mono b fun s hs => ⟨ha0.trans hs.1.le, hs.2.le.trans hb1⟩),
      eventually_nhdsWithin_of_forall fun s hs => hE s (Ioo_subset_Ico_self hs)⟩
  have ht := hU.tendsto.comp hlim
  have := right_nhdsWithin_Ioo_neBot hab
  obtain ⟨s₁, hs₁x, hs₁⟩ := ((ht.eventually_gt_atTop (-x)).and self_mem_nhdsWithin).exists
  change -x < ‖Ψ (α s₁)‖ at hs₁x
  have hnorm : ‖Ψ (α s₁)‖ = -(Ψ (α s₁)).re := by
    have h := Sec7.Prop74B.norm_eq_re_of_im_eq_zero (z := -Ψ (α s₁))
      (by rw [neg_im, hreal s₁ (Ioo_subset_Ico_self hs₁), neg_zero])
      (by rw [neg_re]; linarith [hneg s₁ hs₁])
    simpa only [norm_neg, neg_re] using h
  obtain ⟨s, hs, he⟩ := intermediate_value_Icc' hs₁.1.le
    ((Complex.continuous_re.comp_continuousOn hcont).mono (Icc_subset_Ico_right hs₁.2))
    ⟨show (Ψ (α s₁)).re ≤ x by rw [hnorm] at hs₁x; linarith,
      show x ≤ (Ψ (α a)).re by rw [hU.zero, zero_re]; exact hx.le⟩
  have hsa : a < s := lt_of_le_of_ne hs.1 fun heq => by
    have he' : (Ψ (α s)).re = x := he
    rw [← heq, hU.zero, zero_re] at he'
    exact hx.ne he'.symm
  refine ⟨s, ⟨hsa, hs.2.trans_lt hs₁.2⟩, Complex.ext ?_ ?_⟩
  · simpa only [Function.comp_apply, ofReal_re] using he
  · rw [hreal s ⟨hs.1, hs.2.trans_lt hs₁.2⟩, ofReal_im]

end InteractingSLE.Theorem14.PocketMirror
