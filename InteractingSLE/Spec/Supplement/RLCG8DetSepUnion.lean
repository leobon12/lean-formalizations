/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCG8DetSepBoundary

/-!
# G8: the joint hull union directly from physical trace separation

Packet PROVE-G8-DET. Janiszewski applies before taking any chart image:
the common trace of the later own prefix and the earlier joint prefix is
exactly the earlier own prefix, a connected set meeting the real line.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

namespace InteractingSLE.RLC.G8Det.Late

/-- A common compact trace connected to the real line is enough for the
filled-union identity. No separation of filled hulls is assumed. -/
theorem fillH_union_of_common_connected {F G C : Set ℂ}
    (hF : IsCompact F) (hG : IsCompact G) (hC : IsPreconnected C)
    (hinter : F ∩ G = C) {p : ℂ} (hp : p ∈ C) (hpR : p.im = 0) :
    fillH (F ∪ G) = fillH F ∪ fillH G := by
  apply Subset.antisymm
  · intro z hz
    by_contra h
    have hn : z ∉ fillH F ∧ z ∉ fillH G := by
      simpa only [mem_union, not_or] using h
    have hmem := HalfPlaneSep.H_diff_fillH_inter_subset hF hG (fun w hw =>
      ⟨C, hinter ▸ Subset.rfl, hC, hinter ▸ hw, p, hp, hpR⟩)
      ⟨⟨fillH_subset_H _ hz, hn.1⟩, ⟨fillH_subset_H _ hz, hn.2⟩⟩
    exact hmem.2 hz
  · exact union_subset (fillH_mono subset_union_left) (fillH_mono subset_union_right)

/-- If the new part of alpha misses the retained beta trace, no extra
joint pocket is added to the union of the current own and old joint hulls. -/
theorem jointHull_union_of_no_new_contact {α β : ℝ≥0 → ℂ}
    (hcα : Continuous α) (hcβ : Continuous β) (hα0 : α 0 = 0) {a u r : ℝ≥0} (hau : a ≤ u)
    (hoff : ∀ t ∈ Ioc a u, α t ∉ β '' Icc 0 r) :
    jointHull α β u r = ownHull α u ∪ jointHull α β a r := by
  have hinter : (α '' Icc 0 u) ∩ Restart.prefixSet α a β r = α '' Icc 0 a := by
    apply Subset.antisymm
    · rintro z ⟨⟨t, ht, rfl⟩, hz⟩
      rcases hz with h | h
      · exact h
      · by_cases hta : t ≤ a
        · exact ⟨t, ⟨zero_le, hta⟩, rfl⟩
        · exact (hoff t ⟨lt_of_not_ge hta, ht.2⟩ h).elim
    · exact fun z hz => ⟨image_mono (Icc_subset_Icc_right hau) hz, Or.inl hz⟩
  have he : α '' Icc 0 u ∪ Restart.prefixSet α a β r = Restart.prefixSet α u β r := by
    apply Subset.antisymm
    · exact union_subset subset_union_left
        (union_subset (fun z hz => Or.inl (image_mono (Icc_subset_Icc_right hau) hz)) subset_union_right)
    · exact union_subset subset_union_left (fun z hz => Or.inr (Or.inr hz))
  have h := fillH_union_of_common_connected (isCompact_Icc.image hcα)
    ((isCompact_Icc.image hcα).union (isCompact_Icc.image hcβ))
    (isPreconnected_Icc.image _ hcα.continuousOn) hinter
    (p := 0) ⟨0, ⟨le_rfl, zero_le⟩, hα0⟩ (by rfl)
  change fillH (α '' Icc 0 u ∪ Restart.prefixSet α a β r) = ownHull α u ∪ jointHull α β a r at h
  rw [he] at h
  exact h

/-- The exact relative hull union follows from physical trace separation,
without closed restriction clearance. -/
theorem hull_union_of_no_new_contact {α β : ℝ≥0 → ℂ} {w : ℝ≥0 → ℝ}
    (hcα : Continuous α) (hcβ : Continuous β) (hα0 : α 0 = 0)
    (hw : Continuous w) (hw0 : w 0 = 0) (hgen : IsGeneratingTrace w ⊤ α)
    {a σ r : ℝ≥0} (hoff : ∀ t ∈ Ioc a σ, α t ∉ β '' Icc 0 r) :
    ∀ u ∈ Icc a σ, cutMap α a '' (jointHull α β u r \ ownHull α a) =
      cutObstacle α β a r ∪ fwdHull (cutDrive w a) ((u : ℝ) - a) := by
  intro u hu
  rw [jointHull_union_of_no_new_contact hcα hcβ hα0 hu.1
    (fun t ht => hoff t ⟨ht.1, ht.2.trans hu.2⟩), union_sdiff_distrib, image_union,
    cutMap_image_ownHull hcα hw hw0 hgen hu.1, union_comm]
  rfl

end InteractingSLE.RLC.G8Det.Late
