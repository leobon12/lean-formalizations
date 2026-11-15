/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCG8DetClosedPocket

/-!
# G8: disjointness of the actual image hulls inside the upper half-plane

Packet PROVE-G8-DET. The R63 exclusion applies to every retained beta point.
Together with final joint activity it gives the exact intersection of the
completed own hull and the old joint hull, hence disjoint open image hulls.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

namespace InteractingSLE.RLC.G8Det.Closed

/-- At a cut after the final contact with beta, joint activity excludes
new trace points from old joint pockets. The old joint hull meets the
completed own hull only in their common old own hull. -/
theorem own_joint_inter_eq {α β : ℝ≥0 → ℂ}
    (hcop : Sec7.Prop74Order.IsCompleteOrderedPair α β) (hα0 : α 0 = 0)
    {a σ r : ℝ≥0} {q : ℝ} (haσ : a ≤ σ) (hq : 1 < q) (hασ : α σ = q)
    (hNH : ∀ t < σ, (α t).im = 0 → 0 ≤ (α t).re)
    (hoff : ∀ t ∈ Ioc a σ, α t ∉ β '' Icc 0 r)
    (hact : ∀ t ∈ Ioo a σ, α t ∈ closure (activeDomain α t β r)) :
    ownHull α σ ∩ jointHull α β a r = ownHull α a := by
  have hcα := hcop.1
  have hcβ := hcop.2.2.2.2.1
  have hF : IsCompact (α '' Icc 0 a) := isCompact_Icc.image hcα
  have hB : IsCompact (β '' Icc 0 r) := isCompact_Icc.image hcβ
  have hT : IsCompact (α '' Icc 0 σ) := isCompact_Icc.image hcα
  have hnew : Disjoint ((α '' Icc 0 σ) \ (α '' Icc 0 a)) (jointHull α β a r) := by
    refine Set.disjoint_left.2 ?_
    rintro z ⟨⟨t, ht, rfl⟩, htF⟩ htJ
    have hat : a < t := by
      by_contra h
      exact htF ⟨t, ⟨zero_le, not_lt.1 h⟩, rfl⟩
    rcases ht.2.eq_or_lt with he | he
    · have hh : α t ∈ H := fillH_subset_H _ htJ
      rw [he, hασ] at hh
      exact lt_irrefl 0 (show 0 < (q : ℂ).im from hh)
    · have hcl := closure_mono (domain_anti hcα hcβ hat.le) (hact t ⟨hat, he⟩)
      rw [domain_eq hcα hcβ] at hcl
      have hnot : α t ∉ Restart.prefixSet α a β r := fun h =>
        h.elim htF (hoff t ⟨hat, ht.2⟩)
      have hf := Sec7.isFreeAt_of_mem_closure (hF.union hB).isClosed hnot hcl
      exact (Sec7.mem_H_diff_fillH_of_isFreeAt hf (fillH_subset_H _ htJ)).2 htJ
  have hret := Late.disjoint_own_increment_beta hcop hα0 hq hασ hNH hoff
  have hsub := fillH_inter_subset hF hB hT (isHPHull_ownHull hcα hα0 σ) hnew hret
  apply Subset.antisymm
  · exact fun z hz => hsub ⟨hz.2, hz.1⟩
  · exact fun z hz => ⟨fillH_mono (image_mono (Icc_subset_Icc_right haσ)) hz,
      ownHull_subset le_rfl hz⟩

/-- The actual image hulls are disjoint as subsets of `H`; only real
boundary contacts remain when their full complex closures are taken. -/
theorem disjoint_images {α β : ℝ≥0 → ℂ} {w : ℝ≥0 → ℝ}
    (hcop : Sec7.Prop74Order.IsCompleteOrderedPair α β) (hα0 : α 0 = 0)
    (hw : Continuous w) (hw0 : w 0 = 0) (hgen : IsGeneratingTrace w ⊤ α)
    {a σ r : ℝ≥0} {q : ℝ} (haσ : a ≤ σ) (hq : 1 < q) (hασ : α σ = q)
    (hNH : ∀ t < σ, (α t).im = 0 → 0 ≤ (α t).re)
    (hoff : ∀ t ∈ Ioc a σ, α t ∉ β '' Icc 0 r)
    (hact : ∀ t ∈ Ioo a σ, α t ∈ closure (activeDomain α t β r)) :
    Disjoint (cutObstacle α β a r) (fwdHull (cutDrive w a) ((σ : ℝ) - a)) := by
  have heq := own_joint_inter_eq hcop hα0 haσ hq hασ hNH hoff hact
  have hi := Late.cutMap_image_ownHull hcop.1 hw hw0 hgen haσ
  rw [← hi]
  have hg := ConformalImage.isMapOut_mapOut (isHPHull_ownHull hcop.1 hα0 a)
  refine Set.disjoint_left.2 ?_
  rintro z ⟨x, hx, hxz⟩ ⟨y, hy, hyz⟩
  have hxy : x = y := hg.1.2.injOn ⟨fillH_subset_H _ hx.1, hx.2⟩
    ⟨fillH_subset_H _ hy.1, hy.2⟩ (hxz.trans hyz.symm)
  have hxP : x ∈ ownHull α a := heq ▸ ⟨hxy ▸ hy.1, hx.1⟩
  exact hx.2 hxP

end InteractingSLE.RLC.G8Det.Closed
