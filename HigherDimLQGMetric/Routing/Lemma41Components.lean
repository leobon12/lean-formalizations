import HigherDimLQGMetric.Routing.Lemma41ThreeArc

/-!
# Two attachment components for a routed edge

After deleting the relative interior of the marked middle, the three-arc edge graph splits
into its left and right compact connected attachment components.
-/

set_option autoImplicit false

noncomputable section

open Set Topology LQGMetric.MetricGeometry

namespace HigherDimLQGMetric

theorem lemma41_one_edge_components {X : Type*} [MetricSpace X]
    (βl γ βr : ℝ → X)
    (hβlc : ContinuousOn βl (Icc 0 1)) (hγc : ContinuousOn γ (Icc 0 1))
    (hβrc : ContinuousOn βr (Icc 0 1))
    (hγi : InjOn γ (Icc 0 1))
    {s t u q : ℝ} (hs : 0 < s) (hst : s < t) (ht : t < 1)
    (hu : 0 ≤ u) (hus : u < s) (htq : t < q) (hq : q ≤ 1)
    (hβl1 : βl 1 = γ u) (hβr1 : βr 1 = γ q)
    (hβlavoid : ∀ r ∈ Icc (0 : ℝ) 1, r < 1 → βl r ∉ γ '' Icc 0 1)
    (hβravoid : ∀ r ∈ Icc (0 : ℝ) 1, r < 1 → βr r ∉ γ '' Icc 0 1)
    (hβlr : Disjoint (βl '' Icc (0 : ℝ) 1) (βr '' Icc (0 : ℝ) 1)) :
    let L := βl '' Icc (0 : ℝ) 1 ∪ γ '' Icc 0 s
    let R := βr '' Icc (0 : ℝ) 1 ∪ γ '' Icc t 1
    let K := βl '' Icc (0 : ℝ) 1 ∪ γ '' Icc 0 1 ∪ βr '' Icc 0 1
    let M := γ '' Ioo s t
    IsCompact L ∧ IsConnected L ∧ IsCompact R ∧ IsConnected R ∧
      K \ M = L ∪ R ∧ Disjoint L R := by
  have hs₁ : s < 1 := hst.trans ht
  have ht₀ : 0 < t := hs.trans hst
  have huI : u ∈ Icc (0 : ℝ) 1 := ⟨hu, (hus.trans hs₁).le⟩
  have hqI : q ∈ Icc (0 : ℝ) 1 := ⟨(ht₀.trans htq).le, hq⟩
  let A := βl '' Icc (0 : ℝ) 1
  let B := γ '' Icc (0 : ℝ) s
  let C := βr '' Icc (0 : ℝ) 1
  let D := γ '' Icc t 1
  let M := γ '' Ioo s t
  have hBc : ContinuousOn γ (Icc 0 s) := hγc.mono (Icc_subset_Icc le_rfl hs₁.le)
  have hDc : ContinuousOn γ (Icc t 1) := hγc.mono (Icc_subset_Icc ht₀.le le_rfl)
  have hAcpt : IsCompact A := isCompact_Icc.image_of_continuousOn hβlc
  have hBcpt : IsCompact B := isCompact_Icc.image_of_continuousOn hBc
  have hCcpt : IsCompact C := isCompact_Icc.image_of_continuousOn hβrc
  have hDcpt : IsCompact D := isCompact_Icc.image_of_continuousOn hDc
  have hAconn : IsConnected A := (isConnected_Icc (by norm_num : (0 : ℝ) ≤ 1)).image βl hβlc
  have hBconn : IsConnected B := (isConnected_Icc hs.le).image γ hBc
  have hCconn : IsConnected C := (isConnected_Icc (by norm_num : (0 : ℝ) ≤ 1)).image βr hβrc
  have hDconn : IsConnected D := (isConnected_Icc ht.le).image γ hDc
  have hAB : (A ∩ B).Nonempty := by
    refine ⟨γ u, ⟨1, by norm_num, hβl1⟩, ⟨u, ⟨hu, hus.le⟩, rfl⟩⟩
  have hCD : (C ∩ D).Nonempty := by
    refine ⟨γ q, ⟨1, by norm_num, hβr1⟩, ⟨q, ⟨htq.le, hq⟩, rfl⟩⟩
  have hABcpt : IsCompact (A ∪ B) := hAcpt.union hBcpt
  have hCDcpt : IsCompact (C ∪ D) := hCcpt.union hDcpt
  have hABconn : IsConnected (A ∪ B) := IsConnected.union hAB hAconn hBconn
  have hCDconn : IsConnected (C ∪ D) := IsConnected.union hCD hCconn hDconn
  have hBM : Disjoint B M := by
    apply Set.disjoint_left.mpr
    rintro z ⟨a, ha, rfl⟩ ⟨b, hb, heq⟩
    have hab := hγi (Icc_subset_Icc le_rfl hs₁.le ha)
      ⟨hs.le.trans hb.1.le, hb.2.le.trans ht.le⟩ heq.symm
    exact (not_lt_of_ge (hab ▸ ha.2)) hb.1
  have hDM : Disjoint D M := by
    apply Set.disjoint_left.mpr
    rintro z ⟨a, ha, rfl⟩ ⟨b, hb, heq⟩
    have hab := hγi (Icc_subset_Icc ht₀.le le_rfl ha)
      ⟨hs.le.trans hb.1.le, hb.2.le.trans ht.le⟩ heq.symm
    exact (not_lt_of_ge ha.1) (hab ▸ hb.2)
  have hAM : Disjoint A M := by
    apply Set.disjoint_left.mpr
    rintro z ⟨r, hr, rfl⟩ hmem
    by_cases hr₁ : r < 1
    · apply hβlavoid r hr hr₁
      obtain ⟨a, ha, heq⟩ := hmem
      exact ⟨a, ⟨hs.le.trans ha.1.le, ha.2.le.trans ht.le⟩, heq⟩
    · have hr_eq : r = 1 := le_antisymm hr.2 (le_of_not_gt hr₁)
      rw [hr_eq, hβl1] at hmem
      obtain ⟨a, ha, heq⟩ := hmem
      have hua := hγi huI ⟨hs.le.trans ha.1.le, ha.2.le.trans ht.le⟩ heq.symm
      linarith [ha.1]
  have hCM : Disjoint C M := by
    apply Set.disjoint_left.mpr
    rintro z ⟨r, hr, rfl⟩ hmem
    by_cases hr₁ : r < 1
    · apply hβravoid r hr hr₁
      obtain ⟨a, ha, heq⟩ := hmem
      exact ⟨a, ⟨hs.le.trans ha.1.le, ha.2.le.trans ht.le⟩, heq⟩
    · have hr_eq : r = 1 := le_antisymm hr.2 (le_of_not_gt hr₁)
      rw [hr_eq, hβr1] at hmem
      obtain ⟨a, ha, heq⟩ := hmem
      have hqa := hγi hqI ⟨hs.le.trans ha.1.le, ha.2.le.trans ht.le⟩ heq.symm
      linarith [ha.2]
  have hBD : Disjoint B D := by
    apply Set.disjoint_left.mpr
    rintro z ⟨a, ha, rfl⟩ ⟨b, hb, heq⟩
    have hab := hγi (Icc_subset_Icc le_rfl hs₁.le ha)
      (Icc_subset_Icc ht₀.le le_rfl hb) heq.symm
    linarith [ha.2, hb.1]
  have hAD : Disjoint A D := by
    apply Set.disjoint_left.mpr
    rintro z ⟨r, hr, rfl⟩ ⟨a, ha, heq⟩
    by_cases hr₁ : r < 1
    · exact hβlavoid r hr hr₁ ⟨a, Icc_subset_Icc ht₀.le le_rfl ha, heq⟩
    · have hr_eq : r = 1 := le_antisymm hr.2 (le_of_not_gt hr₁)
      rw [hr_eq, hβl1] at heq
      have hua := hγi huI (Icc_subset_Icc ht₀.le le_rfl ha) heq.symm
      linarith [ha.1]
  have hBC : Disjoint B C := by
    apply Set.disjoint_left.mpr
    rintro z ⟨a, ha, rfl⟩ ⟨r, hr, heq⟩
    by_cases hr₁ : r < 1
    · exact hβravoid r hr hr₁ ⟨a, Icc_subset_Icc le_rfl hs₁.le ha, heq.symm⟩
    · have hr_eq : r = 1 := le_antisymm hr.2 (le_of_not_gt hr₁)
      rw [hr_eq, hβr1] at heq
      have haq := hγi (Icc_subset_Icc le_rfl hs₁.le ha) hqI heq.symm
      linarith [ha.2]
  have hABCD : Disjoint (A ∪ B) (C ∪ D) := by
    apply Set.disjoint_left.mpr
    intro z hzL hzR
    rcases hzL with hA | hB <;> rcases hzR with hC | hD
    · exact (Set.disjoint_left.mp hβlr) hA hC
    · exact (Set.disjoint_left.mp hAD) hA hD
    · exact (Set.disjoint_left.mp hBC) hB hC
    · exact (Set.disjoint_left.mp hBD) hB hD
  have hK : (A ∪ γ '' Icc (0 : ℝ) 1 ∪ C) \ M = (A ∪ B) ∪ (C ∪ D) := by
    ext z
    constructor
    · rintro ⟨hz, hzM⟩
      rcases hz with (hA | hG) | hC
      · exact Or.inl (Or.inl hA)
      · obtain ⟨a, ha, rfl⟩ := hG
        by_cases has : a ≤ s
        · exact Or.inl (Or.inr ⟨a, ⟨ha.1, has⟩, rfl⟩)
        · have hta : t ≤ a := by
            by_contra hnot
            exact hzM ⟨a, ⟨lt_of_not_ge has, lt_of_not_ge hnot⟩, rfl⟩
          exact Or.inr (Or.inr ⟨a, ⟨hta, ha.2⟩, rfl⟩)
      · exact Or.inr (Or.inl hC)
    · intro hz
      have hzK : z ∈ A ∪ γ '' Icc (0 : ℝ) 1 ∪ C := by
        rcases hz with (hA | hB) | (hC | hD)
        · exact Or.inl (Or.inl hA)
        · exact Or.inl (Or.inr ((image_mono (Icc_subset_Icc le_rfl hs₁.le)) hB))
        · exact Or.inr hC
        · exact Or.inl (Or.inr ((image_mono (Icc_subset_Icc ht₀.le le_rfl)) hD))
      refine ⟨hzK, ?_⟩
      rcases hz with (hA | hB) | (hC | hD)
      · exact (Set.disjoint_left.mp hAM) hA
      · exact (Set.disjoint_left.mp hBM) hB
      · exact (Set.disjoint_left.mp hCM) hC
      · exact (Set.disjoint_left.mp hDM) hD
  exact ⟨hABcpt, hABconn, hCDcpt, hCDconn, hK, hABCD⟩

end HigherDimLQGMetric
