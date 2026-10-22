import HigherDimLQGMetric.Routing.Lemma41Assembly
import HigherDimLQGMetric.Routing.Lemma41Crossing

/-! A marked arc is a bridge between its two closed attachment sets. -/

set_option autoImplicit false

noncomputable section

open Set Topology

namespace HigherDimLQGMetric

theorem lemma41_bridge_arc_in_path {X : Type*} [MetricSpace X]
    {x y : X} (P : Path x y) (L R : Set X) (σ : ℝ → X)
    (hL : IsClosed L) (hR : IsClosed R)
    (hLR : Disjoint L R)
    (hσc : ContinuousOn σ (Icc 0 1)) (hσi : InjOn σ (Icc 0 1))
    (hLσ : ∀ z ∈ L, z ∈ σ '' Icc (0 : ℝ) 1 → z = σ 0)
    (hRσ : ∀ z ∈ R, z ∈ σ '' Icc (0 : ℝ) 1 → z = σ 1)
    (hPK : Set.range P ⊆ L ∪ σ '' Icc (0 : ℝ) 1 ∪ R)
    (hx : x ∈ L) (hy : y ∈ R) :
    σ '' Icc (0 : ℝ) 1 ⊆ Set.range P := by
  rintro z ⟨r, hr, rfl⟩
  let A : Set X := L ∪ σ '' Icc 0 r
  let B : Set X := R ∪ σ '' Icc r 1
  have hrc : ContinuousOn σ (Icc 0 r) := hσc.mono (Icc_subset_Icc le_rfl hr.2)
  have hrc' : ContinuousOn σ (Icc r 1) := hσc.mono (Icc_subset_Icc hr.1 le_rfl)
  have hAc : IsClosed A := hL.union (isCompact_Icc.image_of_continuousOn hrc).isClosed
  have hBc : IsClosed B := hR.union (isCompact_Icc.image_of_continuousOn hrc').isClosed
  have hcover : L ∪ σ '' Icc (0 : ℝ) 1 ∪ R ⊆ A ∪ B := by
    intro z hz
    rcases hz with (hzL | hzσ) | hzR
    · exact Or.inl (Or.inl hzL)
    · obtain ⟨u, hu, rfl⟩ := hzσ
      rcases le_total u r with hur | hru
      · exact Or.inl (Or.inr ⟨u, ⟨hu.1, hur⟩, rfl⟩)
      · exact Or.inr (Or.inr ⟨u, ⟨hru, hu.2⟩, rfl⟩)
    · exact Or.inr (Or.inl hzR)
  obtain ⟨q, hq⟩ := lemma41_path_hits_overlap P A B (A ∪ B) hAc hBc
    (Subset.rfl) (hPK.trans hcover) (Or.inl hx) (Or.inl hy)
  have hqr : P q = σ r := by
    rcases hq.1 with hqL | hqA <;> rcases hq.2 with hqR | hqB
    · exact False.elim (Set.disjoint_left.mp hLR hqL hqR)
    · obtain ⟨u, hu, heq⟩ := hqB
      have huI : u ∈ Icc (0 : ℝ) 1 := Icc_subset_Icc hr.1 le_rfl hu
      have h0u : u = 0 := hσi huI (by norm_num)
        (heq.trans (hLσ (P q) hqL ⟨u, huI, heq⟩))
      have hr0 : r = 0 := by linarith [hu.1, hr.1]
      simpa only [hr0] using (hLσ (P q) hqL ⟨u, huI, heq⟩)
    · obtain ⟨u, hu, heq⟩ := hqA
      have huI : u ∈ Icc (0 : ℝ) 1 := Icc_subset_Icc le_rfl hr.2 hu
      have hu1 : u = 1 := hσi huI (by norm_num)
        (heq.trans (hRσ (P q) hqR ⟨u, huI, heq⟩))
      have hr1 : r = 1 := by linarith [hu.2, hr.2]
      simpa only [hr1] using (hRσ (P q) hqR ⟨u, huI, heq⟩)
    · obtain ⟨u, hu, heq⟩ := hqA
      obtain ⟨v, hv, heq'⟩ := hqB
      have huI : u ∈ Icc (0 : ℝ) 1 := Icc_subset_Icc le_rfl hr.2 hu
      have hvI : v ∈ Icc (0 : ℝ) 1 := Icc_subset_Icc hr.1 le_rfl hv
      have huv : u = v := hσi huI hvI (heq.trans heq'.symm)
      have hur : u = r := le_antisymm hu.2 (huv ▸ hv.1)
      simpa only [hur] using heq.symm
  exact ⟨q, hqr⟩

end HigherDimLQGMetric
