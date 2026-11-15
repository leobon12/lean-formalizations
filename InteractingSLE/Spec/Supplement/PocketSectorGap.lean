/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.PocketSectorBoundary
import InteractingSLE.Spec.Sec7.PocketCoordJordan

/-!
# Contact gaps from the original ordered-contact hypothesis

PROVE-POCKETSHAPE continuation. The finite-time contact order gives the existing
disc contact-map order, including the added endpoint at infinity. The existing
Auxiliary Lemma 33 API then gives a Jordan pocket around any non-contact wall
point. Identifying that pocket with a given between-component remains separate.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Function Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley)

namespace InteractingSLE.Theorem14.PocketSector

open GW4Reg WangWu Sec7.Lemma71I

/-- Increasing contact order survives the disc compactification of two proper walls. -/
theorem strictMonoOn_disc_contactMap {αR αL : ℝ≥0 → ℂ}
    (hR : IsSimpleProper αR) (hL : IsSimpleProper αL)
    (hord : ∀ s s' t t' : ℝ≥0, αR s = αL t → αR s' = αL t' → (s < s' ↔ t < t')) :
    StrictMonoOn (contactMap (toDisc (realPath αR)) (toDisc (realPath αL)))
      (Sec7.pocketContactSet (toDisc (realPath αR)) (toDisc (realPath αL))) := by
  let α := toDisc (realPath αR)
  let β := toDisc (realPath αL)
  have hα : IsDiscCrosscut α := hR.isProperArc.isDiscCrosscut_toDisc
  have hβ : IsDiscCrosscut β := hL.isProperArc.isDiscCrosscut_toDisc
  have hRb := isCompleteSimpleFlow_of_isSimpleProper hR
  have hLb := isCompleteSimpleFlow_of_isSimpleProper hL
  have hfinite : ∀ {s t : ℝ}, s ∈ Icc (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 → s < 1 →
      α s = β t → t < 1 ∧
        αR (arcTime s).toNNReal = αL (arcTime t).toNNReal := by
    intro s t hs ht hs1 he
    have ht1 : t < 1 := lt_of_le_of_ne ht.2 fun ht1 => by
      have htβ : β t = 1 := by rw [ht1, hβ.one]
      have hsEq : s = 1 := hα.inj hs (by simp) (he.trans (htβ.trans hα.one.symm))
      exact hs1.ne hsEq
    refine ⟨ht1, ?_⟩
    change toDisc (realPath αR) s = toDisc (realPath αL) t at he
    rw [toDisc_of_lt hs1, toDisc_of_lt ht1] at he
    exact cayley_injOn_Hbar (hRb.2.2.2.1 _) (hLb.2.2.2.1 _) he
  intro s hs s' hs' hss
  obtain ⟨hj, hjs⟩ := contactMap_mem hβ hs
  obtain ⟨hj', hjs'⟩ := contactMap_mem hβ hs'
  have hs1 : s < 1 := hss.trans_le hs'.1.2
  obtain ⟨hj1, he⟩ := hfinite hs.1 hj hs1 hjs.symm
  by_cases hs'1 : s' = 1
  · have hj'1 : contactMap α β s' = 1 := contactMap_eq hβ (by simp)
      (by rw [hs'1, hα.one, hβ.one])
    exact hj'1 ▸ hj1
  have hs'lt : s' < 1 := lt_of_le_of_ne hs'.1.2 hs'1
  obtain ⟨hj'1, he'⟩ := hfinite hs'.1 hj' hs'lt hjs'.symm
  have hNN : (arcTime s).toNNReal < (arcTime s').toNNReal := by
    change ((arcTime s).toNNReal : ℝ) < ((arcTime s').toNNReal : ℝ)
    rw [Real.coe_toNNReal _ (arcTime_nonneg ⟨hs.1.1, hs1⟩),
      Real.coe_toNNReal _ (arcTime_nonneg ⟨hs'.1.1, hs'lt⟩)]
    exact strictMonoOn_arcTime ⟨hs.1.1, hs1⟩ ⟨hs'.1.1, hs'lt⟩ hss
  have hqNN := (hord _ _ _ _ he he').1 hNN
  have hq : arcTime (contactMap α β s) < arcTime (contactMap α β s') := by
    rw [← Real.coe_toNNReal _ (arcTime_nonneg ⟨hj.1, hj1⟩),
      ← Real.coe_toNNReal _ (arcTime_nonneg ⟨hj'.1, hj'1⟩)]
    exact hqNN
  have hq' := WangWu.discTime_lt_discTime (arcTime_nonneg ⟨hj.1, hj1⟩) hq
  rw [WangWu.discTime_arcTime hj1, WangWu.discTime_arcTime hj'1] at hq'
  exact hq'

/-- Every non-contact point of the right wall has a contact gap in the disc picture. -/
theorem exists_disc_contactGap_at_right {αR αL : ℝ≥0 → ℂ}
    (hR : IsSimpleProper αR) (hL : IsSimpleProper αL)
    {r : ℝ≥0} (hoff : αR r ∉ range αL) :
    ∃ a b : ℝ, IsContactGap (toDisc (realPath αR)) (toDisc (realPath αL)) a b ∧
      discTime (r : ℝ) ∈ Ioo a b := by
  have hrH : αR r ∈ Hbar := (isCompleteSimpleFlow_of_isSimpleProper hR).2.2.2.1 r
  have hoff' : toDisc (realPath αR) (discTime (r : ℝ)) ∉ crossRange (toDisc (realPath αL)) := by
    rw [WangWu.toDisc_discTime (realPath αR) (t := (r : ℝ)) r.2, realPath_coe]
    intro h
    have hmem := (hL.isProperArc.cayley_mem_crossRange_iff hrH).1 h
    rw [arcRange_realPath] at hmem
    exact hoff hmem
  exact Sec7.Aux130.exists_isContactGap_of_notMem hR.isProperArc.isDiscCrosscut_toDisc
    hL.isProperArc.isDiscCrosscut_toDisc (Ico_subset_Icc_self (discTime_mem_Ico r.2))
    (fun h => hoff' h.2)

/-- Ordered contacts give an actual Jordan pocket around any non-contact right-wall point. -/
theorem exists_disc_jordanPocket_at_right {αR αL : ℝ≥0 → ℂ}
    (hR : IsSimpleProper αR) (hL : IsSimpleProper αL)
    (hord : ∀ s s' t t' : ℝ≥0, αR s = αL t → αR s' = αL t' → (s < s' ↔ t < t'))
    {r : ℝ≥0} (hoff : αR r ∉ range αL) :
    ∃ a b : ℝ, IsContactGap (toDisc (realPath αR)) (toDisc (realPath αL)) a b ∧
      discTime (r : ℝ) ∈ Ioo a b ∧
      LQGMetric.JordanMap.IsJordanCurve
        (pocketCurve (toDisc (realPath αR)) (toDisc (realPath αL)) a b) ∧
      frontier (jordanIn (pocketCurve (toDisc (realPath αR)) (toDisc (realPath αL)) a b)) =
        pocketCurve (toDisc (realPath αR)) (toDisc (realPath αL)) a b := by
  obtain ⟨a, b, hg, hr⟩ := exists_disc_contactGap_at_right hR hL hoff
  obtain ⟨hJ, -, -, hfr, -⟩ := Sec7.PocketCoord.pocket_props_of_strictMono
    hR.isProperArc.isDiscCrosscut_toDisc hL.isProperArc.isDiscCrosscut_toDisc
    (strictMonoOn_disc_contactMap hR hL hord) hg
  exact ⟨a, b, hg, hr, hJ, hfr⟩

end InteractingSLE.Theorem14.PocketSector
