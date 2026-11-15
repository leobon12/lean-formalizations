/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCG8DetSepUnion

/-!
# G8: the retained trace misses the filled own increment

Packet PROVE-G8-DET. The R63 side lemma applies at every retained beta
point, not just the tip. This excludes the entire retained trace from the
new own filling after a cut with no further alpha-beta contacts.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

namespace InteractingSLE.RLC.G8Det.Late

/-- Under R63 nonhitting, a new own-hull point cannot lie on the retained
beta trace once the later alpha trace avoids that retained trace. -/
theorem disjoint_own_increment_beta {α β : ℝ≥0 → ℂ}
    (hcop : Sec7.Prop74Order.IsCompleteOrderedPair α β) (hα0 : α 0 = 0)
    {a σ r : ℝ≥0} {q : ℝ} (hq : 1 < q) (hασ : α σ = q)
    (hNH : ∀ s < σ, (α s).im = 0 → 0 ≤ (α s).re)
    (hoff : ∀ s ∈ Ioc a σ, α s ∉ β '' Icc 0 r) :
    Disjoint (ownHull α σ \ ownHull α a) (β '' Icc 0 r) := by
  refine Set.disjoint_left.2 ?_
  rintro z ⟨hz, hza⟩ ⟨t, ht, rfl⟩
  have htH : β t ∈ H := fillH_subset_H _ hz
  by_cases htrace : β t ∈ α '' Icc 0 σ
  · obtain ⟨s, hs, he⟩ := htrace
    have hsa : s ≤ a := by
      by_contra h
      exact hoff s ⟨lt_of_not_ge h, hs.2⟩ ⟨t, ht, he.symm⟩
    exact hza (mem_fillH_of_mem_closure htH (subset_closure ⟨s, ⟨zero_le, hsa⟩, he⟩))
  · exact beta_notMem_closure_ownHull hcop hα0 hq hασ hNH htH htrace (subset_closure hz)

/-- Arbitrarily late cuts have no further contacts with the small beta
prefix, including at the real terminal contact. -/
theorem exists_late_no_new_contact {α β : ℝ≥0 → ℂ} (hcα : Continuous α)
    {σ r a₀ : ℝ≥0} {q : ℝ} (ha₀ : a₀ < σ) (hq : 1 < q) (hασ : α σ = q)
    (hsmall : ∀ t ≤ r, ‖β t‖ < 1 / 2) :
    ∃ a ∈ Ioo a₀ σ, ∀ t ∈ Ioc a σ, α t ∉ β '' Icc 0 r := by
  obtain ⟨b, hb, hball⟩ := exists_final_ball hcα (zero_le.trans_lt ha₀) hασ
    (show (0 : ℝ) < 1 / 4 by norm_num)
  obtain ⟨a, ha, haσ⟩ := exists_between (max_lt ha₀ hb)
  have hdis : Disjoint (ball (q : ℂ) (1 / 4 : ℝ)) (closedBall 0 (1 / 2 : ℝ)) := by
    apply ball_disjoint_closedBall
    rw [dist_zero_right, norm_real, Real.norm_eq_abs, abs_of_pos (zero_lt_one.trans hq)]
    linarith only [hq]
  refine ⟨a, ⟨(le_max_left _ _).trans_lt ha, haσ⟩, ?_⟩
  rintro t ht ⟨s, hs, he⟩
  have htball := hball ⟨t, ⟨((le_max_right _ _).trans ha.le).trans ht.1.le, ht.2⟩, rfl⟩
  have hsball : α t ∈ closedBall 0 (1 / 2 : ℝ) := by
    rw [← he]
    exact mem_closedBall_zero_iff.2 (hsmall s hs.2).le
  exact Set.disjoint_left.1 hdis htball hsball

/-- The physical filled-increment exclusion and the full relative hull
union hold at arbitrarily late cuts without a separation input. -/
theorem exists_late_union_and_disjoint {α β : ℝ≥0 → ℂ} {w : ℝ≥0 → ℝ}
    (hcop : Sec7.Prop74Order.IsCompleteOrderedPair α β) (hα0 : α 0 = 0)
    (hw : Continuous w) (hw0 : w 0 = 0) (hgen : IsGeneratingTrace w ⊤ α)
    {σ r a₀ : ℝ≥0} {q : ℝ} (ha₀ : a₀ < σ) (hq : 1 < q) (hασ : α σ = q)
    (hsmall : ∀ t ≤ r, ‖β t‖ < 1 / 2)
    (hNH : ∀ s < σ, (α s).im = 0 → 0 ≤ (α s).re) :
    ∃ a ∈ Ioo a₀ σ,
      Disjoint (ownHull α σ \ ownHull α a) (β '' Icc 0 r) ∧
      ∀ u ∈ Icc a σ, cutMap α a '' (jointHull α β u r \ ownHull α a) =
        cutObstacle α β a r ∪ fwdHull (cutDrive w a) ((u : ℝ) - a) := by
  obtain ⟨a, ha, hoff⟩ := exists_late_no_new_contact hcop.1 ha₀ hq hασ hsmall
  exact ⟨a, ha, disjoint_own_increment_beta hcop hα0 hq hασ hNH hoff,
    hull_union_of_no_new_contact hcop.1 hcop.2.2.2.2.1 hα0 hw hw0 hgen hoff⟩

end InteractingSLE.RLC.G8Det.Late
