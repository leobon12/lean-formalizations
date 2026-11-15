/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.PocketRimCayley

/-!
# A compactified contact-gap component has a pocket shape

PROVE-POCKETSHAPE continuation. Once the Cayley image of a between-component is
identified with a contact-gap pocket, all finite and infinite endpoint extraction
is proved here. This does not assume a shape or a chart endpoint convention.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Bornology Metric Function
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley)

namespace InteractingSLE.Theorem14.PocketRim

open GW4Reg WangWu Sec7.Lemma71I

/-- A component equal to the Cayley preimage of a contact-gap pocket has a full shape. -/
theorem exists_isPocketShape_of_cayley_contactGap {αR αL : ℝ≥0 → ℂ}
    (hR : IsSimpleProper αR) (hL : IsSimpleProper αL)
    (hord : ∀ s s' t t' : ℝ≥0, αR s = αL t → αR s' = αL t' → (s < s' ↔ t < t'))
    {C : Set ℂ} (hC : C ∈ betweenComponents (range αR) (range αL))
    {a b : ℝ} (hg : IsContactGap (toDisc (realPath αR)) (toDisc (realPath αL)) a b)
    (hEq : cayley '' C = jordanIn (pocketCurve (toDisc (realPath αR)) (toDisc (realPath αL)) a b)) :
    ∃ (s t : ℝ≥0) (u v : ℝ≥0∞), IsPocketShape αR αL C s t u v := by
  let α := toDisc (realPath αR)
  let β := toDisc (realPath αL)
  have hα : IsDiscCrosscut α := hR.isProperArc.isDiscCrosscut_toDisc
  have hβ : IsDiscCrosscut β := hL.isProperArc.isDiscCrosscut_toDisc
  have hRb := PocketSector.isCompleteSimpleFlow_of_isSimpleProper hR
  have hLb := PocketSector.isCompleteSimpleFlow_of_isSimpleProper hL
  have hCo := isOpen_of_mem_betweenComponents
    (isClosed_range_of_isCompleteSimpleFlow hRb) (isClosed_range_of_isCompleteSimpleFlow hLb) hC
  have hCH : C ⊆ H := fun z hz => (Sec7.Prop74B.subset_of_mem_betweenComponents hC hz).1
  have hHb : closure C ⊆ Hbar := closure_minimal
    (fun z hz => (show 0 < z.im from hCH hz).le) QuantumZipper.isClosed_Hbar
  obtain ⟨hJ, -, -, hfr, -⟩ := Sec7.PocketCoord.pocket_props_of_strictMono hα hβ
    (PocketSector.strictMonoOn_disc_contactMap hR hL hord) hg
  have hfrC : frontier (cayley '' C) = pocketCurve α β a b := by rw [hEq]; exact hfr
  have ha01 := hg.1.1
  have hb01 := hg.2.1.1
  have hab := hg.2.2.1
  have ha1 : a < 1 := hab.trans_le hb01.2
  obtain ⟨hja, hjae⟩ := contactMap_mem hβ hg.1
  obtain ⟨hjb, hjbe⟩ := contactMap_mem hβ hg.2.1
  obtain ⟨hja1, hcontact⟩ := finite_contact_of_disc_contact hRb hLb ha1 hja.2 hjae.symm
  let s := (arcTime a).toNNReal
  let t := (arcTime (contactMap α β a)).toNNReal
  have hscl : αR s ∈ closure C := by
    apply mem_closure_of_cayley_mem_closure hCH (hRb.2.2.2.1 s)
    apply frontier_subset_closure
    rw [hfrC]
    exact Or.inl ⟨a, ⟨le_rfl, hab.le⟩, toDisc_of_lt ha1⟩
  rcases lt_or_eq_of_le hb01.2 with hb1 | hb1
  · obtain ⟨hjb1, hentry⟩ := finite_contact_of_disc_contact hRb hLb hb1 hjb.2 hjbe.symm
    let u := (arcTime b).toNNReal
    let v := (arcTime (contactMap α β b)).toNNReal
    have hsu : s < u := by
      change ((arcTime a).toNNReal : ℝ) < ((arcTime b).toNNReal : ℝ)
      rw [Real.coe_toNNReal _ (arcTime_nonneg ⟨ha01.1, ha1⟩),
        Real.coe_toNNReal _ (arcTime_nonneg ⟨hb01.1, hb1⟩)]
      exact strictMonoOn_arcTime ⟨ha01.1, ha1⟩ ⟨hb01.1, hb1⟩ hab
    have hucl : αR u ∈ closure C := by
      apply mem_closure_of_cayley_mem_closure hCH (hRb.2.2.2.1 u)
      apply frontier_subset_closure
      rw [hfrC]
      exact Or.inl ⟨b, ⟨hab.le, le_rfl⟩, toDisc_of_lt hb1⟩
    have hCb : IsBounded C := by
      apply (isBounded_iff_one_not_mem_frontier_cayley hCo hCH).2
      intro h1
      rw [hfrC] at h1
      rcases h1 with ⟨q, hq, he⟩ | ⟨q, hq, he⟩
      · have hq1 : q = 1 := hα.inj ⟨ha01.1.trans hq.1, hq.2.trans hb01.2⟩ (by simp)
          (he.trans hα.one.symm)
        exact (hq.2.trans_lt hb1).ne hq1
      · have hq1 : q = 1 := hβ.inj ⟨hja.1.trans hq.1, hq.2.trans hjb.2⟩ (by simp)
          (he.trans hβ.one.symm)
        exact (hq.2.trans_lt hjb1).ne hq1
    refine ⟨s, t, (u : ℝ≥0∞), (v : ℝ≥0∞), hcontact, hscl, ENNReal.coe_lt_coe.2 hsu,
      by simp only [ENNReal.coe_ne_top, iff_self], fun hu => (ENNReal.coe_ne_top hu).elim, ?_, ?_⟩
    · intro _
      simpa only [ENNReal.toNNReal_coe] using
        (show αR u = αL v ∧ αR u ∈ closure C ∧ IsBounded C from ⟨hentry, hucl, hCb⟩)
    · intro z hz
      have hz' := Sec7.Lemma71F.cayley_mem_frontier hCo hCH hz
      rw [hfrC] at hz'
      rcases hz' with hz' | hz'
      · obtain ⟨r, hr, hru, he⟩ := mem_wall_interval_of_cayley_mem hRb
          (hHb (frontier_subset_closure hz)) ha01.1 hb01.2 hz'
        exact Or.inl ⟨r, ⟨hr, ENNReal.coe_le_coe.2 (hru hb1)⟩, he⟩
      · obtain ⟨r, hr, hrv, he⟩ := mem_wall_interval_of_cayley_mem hLb
          (hHb (frontier_subset_closure hz)) hja.1 hjb.2 hz'
        exact Or.inr ⟨r, ⟨hr, ENNReal.coe_le_coe.2 (hrv hjb1)⟩, he⟩
  · have hCu : ¬ IsBounded C := by
      intro hb
      apply one_not_mem_closure_cayley_of_isBounded hCH hb
      apply frontier_subset_closure
      rw [hfrC]
      exact Or.inl ⟨b, ⟨hab.le, le_rfl⟩, by rw [hb1, hα.one]⟩
    refine ⟨s, t, ⊤, ⊤, hcontact, hscl, ENNReal.coe_lt_top,
      Iff.rfl, fun _ => hCu, fun hu => (hu rfl).elim, ?_⟩
    intro z hz
    have hz' := Sec7.Lemma71F.cayley_mem_frontier hCo hCH hz
    rw [hfrC] at hz'
    rcases hz' with hz' | hz'
    · obtain ⟨r, hr, -, he⟩ := mem_wall_interval_of_cayley_mem hRb
        (hHb (frontier_subset_closure hz)) ha01.1 hb01.2 hz'
      exact Or.inl ⟨r, ⟨hr, le_top⟩, he⟩
    · obtain ⟨r, hr, -, he⟩ := mem_wall_interval_of_cayley_mem hLb
        (hHb (frontier_subset_closure hz)) hja.1 hjb.2 hz'
      exact Or.inr ⟨r, ⟨hr, le_top⟩, he⟩

end InteractingSLE.Theorem14.PocketRim
