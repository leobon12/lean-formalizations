/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.PocketCompassSign

/-!
# A component chart retaining its normalized boundary map

PROVE-POCKETSHAPE. The existing extended inverse `pocketInv` and the intermediate
value theorem give boundary labels without a global side condition on the left
wall. The chart retains the right-arc preimages for the subsequent order proof.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Bornology Metric Function
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley cayleyInv)
open SupercriticalConformalCovariance (IsConformalBijection)

namespace InteractingSLE.Theorem14.PocketCompass

open GW4Reg WangWu Sec7.Lemma71I Sec7.Lemma71K

/-- Every positive real value occurs on the open right boundary arc. -/
theorem exists_marked_right_preimage {R : ℝ≥0 → ℂ} (hR : IsSimpleProper R)
    {C : Set ℂ} (hCo : IsOpen C) (hCH : C ⊆ H) (hCR : Disjoint C (range R))
    {a b : ℝ} (hM : IsMarkedPocket R C a b) {Ψ : ℂ → ℂ}
    (hU : Sec7.PocketJordan.IsBdryUniformizer (cayley '' C) (wallPt R a) (wallPt R b) Ψ)
    (hpos : ∀ s ∈ Ioo a b, 0 < (Ψ (wallPt R s)).re) {x : ℝ} (hx : 0 < x) :
    ∃ s ∈ Ioo a b, Ψ (wallPt R s) = x := by
  have hα : IsDiscCrosscut (wallPt R) := hR.isProperArc.isDiscCrosscut_toDisc
  obtain ⟨ha0, hab, hb1, hI, -, -, -, -⟩ := id hM
  let E := closure (cayley '' C) \ {wallPt R b}
  have hE : ∀ s ∈ Ico a b, wallPt R s ∈ E := by
    intro s hs
    refine ⟨?_, fun he => hs.2.ne (hα.inj ⟨ha0.trans hs.1, hs.2.le.trans hb1⟩
      ⟨ha0.trans hab.le, hb1⟩ he)⟩
    have : s ∈ {q ∈ Icc (0 : ℝ) 1 | wallPt R q ∈ closure (cayley '' C)} := by
      rw [hI]
      exact Ico_subset_Icc_self hs
    exact this.2
  have hcont : ContinuousOn (fun s => Ψ (wallPt R s)) (Ico a b) := hU.cont.comp
    (hα.cont.mono fun s hs => ⟨ha0.trans hs.1, hs.2.le.trans hb1⟩) hE
  have hlim : Tendsto (wallPt R) (𝓝[Ioo a b] b) (𝓝[E] (wallPt R b)) :=
    tendsto_nhdsWithin_iff.2 ⟨((hα.cont b ⟨ha0.trans hab.le, hb1⟩).tendsto).mono_left
      (nhdsWithin_mono b fun s hs => ⟨ha0.trans hs.1.le, hs.2.le.trans hb1⟩),
      eventually_nhdsWithin_of_forall fun s hs => hE s (Ioo_subset_Ico_self hs)⟩
  have ht := hU.tendsto.comp hlim
  have := right_nhdsWithin_Ioo_neBot hab
  obtain ⟨s₁, hs₁x, hs₁⟩ := ((ht.eventually_gt_atTop x).and self_mem_nhdsWithin).exists
  have hr := im_eq_zero_on_marked_right hR hCo hCH hCR hM hU
  have hnorm : (Ψ (wallPt R s₁)).re = ‖Ψ (wallPt R s₁)‖ :=
    (Sec7.Prop74B.norm_eq_re_of_im_eq_zero (hr s₁ (Ioo_subset_Ico_self hs₁)) (hpos s₁ hs₁)).symm
  obtain ⟨s, hs, he⟩ := intermediate_value_Icc hs₁.1.le
    ((Complex.continuous_re.comp_continuousOn hcont).mono (Icc_subset_Ico_right hs₁.2))
    ⟨show (Ψ (wallPt R a)).re ≤ x by rw [hU.zero, Complex.zero_re]; exact hx.le,
      show x ≤ (Ψ (wallPt R s₁)).re by rw [hnorm]; exact hs₁x.le⟩
  have hsa : a < s := lt_of_le_of_ne hs.1 fun heq => by
    have he' : (Ψ (wallPt R s)).re = x := he
    rw [← heq, hU.zero, Complex.zero_re] at he'
    exact hx.ne he'
  refine ⟨s, ⟨hsa, hs.2.trans_lt hs₁.2⟩, Complex.ext ?_ ?_⟩
  · simpa only [Function.comp_apply, Complex.ofReal_re] using he
  · rw [hr s ⟨hs.1, hs.2.trans_lt hs₁.2⟩, Complex.ofReal_im]

/-- A signed two-point uniformizer supplies a component chart and its right-arc preimages. -/
theorem exists_chart_of_marked_uniformizer {R : ℝ≥0 → ℂ} (hR : IsSimpleProper R)
    {L C : Set ℂ} (hLH : L ⊆ Hbar) (hCo : IsOpen C) (hCH : C ⊆ H)
    (hCR : Disjoint C (range R)) {a b : ℝ} (hM : IsMarkedPocket R C a b)
    (hfr : frontier (cayley '' C) ⊆ wallPt R '' Icc a b ∪ cayley '' L)
    {Ψ : ℂ → ℂ} (hU : Sec7.PocketJordan.IsBdryUniformizer
      (cayley '' C) (wallPt R a) (wallPt R b) Ψ)
    (hpos : ∀ s ∈ Ioo a b, 0 < (Ψ (wallPt R s)).re) :
    ∃ c : Chart, IsComponentChart (range R) L C c ∧
      ∀ x : ℝ, 0 < x → ∃ s ∈ Ioo a b,
        Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 (cayleyInv (wallPt R s))) ∧ Ψ (wallPt R s) = x := by
  have hα : IsDiscCrosscut (wallPt R) := hR.isProperArc.isDiscCrosscut_toDisc
  obtain ⟨ha0, hab, hb1, hI, -, -, -, -⟩ := id hM
  let f := Ψ ∘ cayley
  let E := closure (cayley '' C) \ {wallPt R b}
  let G := Sec7.Prop74B.pocketInv Ψ E
  have hf : IsConformalBijection f C H :=
    isConformalBijection_comp hU.conf (Sec7.Lemma71F.isConformalBijection_cayley_image hCH)
  have hqC : ∀ z ∈ C, cayley z ≠ wallPt R b := fun z hz he =>
    disjoint_left.1 hCR hz (GW3.mem_range_of_cayley_mem_wallPt_image hR.isProperCurve
      (Sec7.Prop74B.mem_Hbar_of_mem_H (hCH hz)) ⟨b, ⟨ha0.trans hab.le, hb1⟩, he.symm⟩)
  have hq1 : (1 : ℂ) ∈ closure (cayley '' C) → wallPt R b = 1 := by
    intro h1
    have hm : (1 : ℝ) ∈ {s ∈ Icc (0 : ℝ) 1 | wallPt R s ∈ closure (cayley '' C)} :=
      ⟨⟨zero_le_one, le_rfl⟩, by rw [show wallPt R 1 = 1 from hα.one]; exact h1⟩
    rw [hI] at hm
    rw [le_antisymm hb1 hm.2, hα.one]
  obtain ⟨hGc, -, hGinv, hGcl⟩ := Sec7.Prop74B.pocketInv_props hCH hf hqC
    hU.cont hU.inj hU.mapsTo hU.tendsto (fun _ _ => rfl) hq1
  have hxH : ∀ x : ℝ, (x : ℂ) ∈ Hbar := fun x => by change 0 ≤ (x : ℂ).im; simp
  have hGE : ∀ x : ℝ, cayley (G x) ∈ E ∧ Ψ (cayley (G x)) = x := by
    intro x
    have hs := Sec7.Prop74B.invFunOn_boundaryMap_spec hCH hf hqC hU.cont hU.mapsTo hU.tendsto
      (fun _ _ => rfl) (hxH x)
    obtain ⟨-, h1, h2⟩ := hGcl x (hxH x)
    exact ⟨h1 ▸ hs.1, h2⟩
  have hright : ∀ x : ℝ, 0 < x → ∃ s ∈ Ioo a b,
      G x = cayleyInv (wallPt R s) ∧ Ψ (wallPt R s) = x := by
    intro x hx
    obtain ⟨s, hs, he⟩ := exists_marked_right_preimage hR hCo hCH hCR hM hU hpos hx
    have hsE : wallPt R s ∈ E := by
      refine ⟨?_, fun h => hs.2.ne (hα.inj ⟨ha0.trans hs.1.le, hs.2.le.trans hb1⟩
        ⟨ha0.trans hab.le, hb1⟩ h)⟩
      have hm : s ∈ {s ∈ Icc (0 : ℝ) 1 | wallPt R s ∈ closure (cayley '' C)} := by
        rw [hI]; exact Ioo_subset_Icc_self hs
      exact hm.2
    have hEq : invFunOn Ψ E x = wallPt R s := by
      rw [← he]
      exact hU.inj.leftInvOn_invFunOn hsE
    exact ⟨s, hs, congrArg cayleyInv hEq, he⟩
  have hlim := fun x : ℝ => GW3.tendsto_invFunOn_of_pocketInv hf hGc hGinv x
  obtain ⟨c, -, hcInv, hc⟩ := exists_isDomainChart_of_isConformalBijection hCo hCH hf
  refine ⟨c, GW3.isComponentChart_of_isDomainChart hc (fun x => ⟨G x, hcInv.symm ▸ hlim x,
    ?_, ?_⟩), ?_⟩
  · intro hx
    obtain ⟨s, hs, he, -⟩ := hright x hx
    rw [he, wallPt, toDisc_of_lt (hs.2.trans_le hb1), realPath,
      cayleyInv_cayley_of_mem_Hbar (hR.isProperCurve.2.2.1 _)]
    exact mem_range_self _
  · intro hx
    have hnot : cayley (G x) ∉ cayley '' C := by
      rintro ⟨z, hz, he⟩
      have hh := hU.conf.2.mapsTo ⟨z, hz, rfl⟩
      rw [he, (hGE x).2] at hh
      exact lt_irrefl (0 : ℝ) (by simpa using (show (0 : ℝ) < (x : ℂ).im from hh))
    have hboundary : cayley (G x) ∈ frontier (cayley '' C) := by
      rw [(Sec7.Lemma71F.isOpen_cayley_image hCo hCH).frontier_eq]
      exact ⟨(hGE x).1.1, hnot⟩
    have hGH : G x ∈ Hbar := Sec7.Lemma71F.im_nonneg_of_mem_closure hCH (hGcl x (hxH x)).1
    rcases hfr hboundary with ⟨s, hs, he⟩ | ⟨l, hl, he⟩
    · exfalso
      have hv : Ψ (wallPt R s) = x := he ▸ (hGE x).2
      rcases eq_or_lt_of_le hs.1 with hsa | hsa
      · rw [← hsa, hU.zero] at hv
        exact hx.ne (by exact_mod_cast hv.symm)
      rcases eq_or_lt_of_le hs.2 with hsb | hsb
      · exact (hGE x).1.2 (by rw [← he, hsb]; exact mem_singleton _)
      · have hp := hpos s ⟨hsa, hsb⟩
        rw [hv, Complex.ofReal_re] at hp
        exact (not_lt_of_ge hp.le hx).elim
    · exact (cayley_injOn_Hbar (hLH hl) hGH he) ▸ hl
  · intro x hx
    obtain ⟨s, hs, he, hv⟩ := hright x hx
    exact ⟨s, hs, hcInv.symm ▸ (he ▸ hlim x), hv⟩

end InteractingSLE.Theorem14.PocketCompass
