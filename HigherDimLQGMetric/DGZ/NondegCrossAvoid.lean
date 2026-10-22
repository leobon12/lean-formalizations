import HigherDimLQGMetric.DGZ.NondegSeparatedCross

/-! A zero set avoids the other sphere precisely when the crossing is positive. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP HigherDimLFPP.Perc

variable {d : ℕ}

theorem nd_cross_pos_iff_zeroSet_disjoint_shell
    {rGrid r : ℝ} (hd : 0 < d) (hr : 0 < r)
    (s : nd_Joint d rGrid) (hs : s ∈ nd_pseudoSet rGrid) :
    0 < nd_crossPhi 0 (2 * r) r s.1 ↔
      Disjoint (nd_zeroSet r s) (lsph (0 : Rd d) (2 * r)) := by
  constructor
  · intro hcross
    exact ((nd_cross_pos_iff_disjoint_zeroSets hr hd hs).1 hcross).mono_right
      (nd_sphere_subset_zeroSet (2 * r) hs)
  · intro hdisj
    apply (nd_cross_pos_iff_disjoint_zeroSets hr hd hs).2
    rw [Set.disjoint_left] at hdisj ⊢
    intro x hx₁ hx₂
    obtain ⟨y₁, hy₁, hxy₁⟩ := (nd_zeroSet_mem_iff hr.le hd hs x).1 hx₁
    obtain ⟨y₂, hy₂, hxy₂⟩ :=
      (nd_zeroSet_mem_iff (by linarith : 0 ≤ 2 * r) hd hs x).1 hx₂
    have htri := hs.2.2.2 y₂ x y₁
    have hsym := hs.2.2.1 y₂ x
    rw [hsym, hxy₂, hxy₁] at htri
    have hzero : s.1 (y₂, y₁) = 0 :=
      le_antisymm (by linarith) (hs.2.1 y₂ y₁)
    have hy₂E : y₂ ∈ nd_zeroSet r s :=
      (nd_zeroSet_mem_iff hr.le hd hs y₂).2 ⟨y₁, hy₁, hzero⟩
    exact hdisj hy₂E hy₂

theorem nd_cross_pos_of_selected_avoids_shell
    {rGrid r : ℝ} (hd : 0 < d) (hrGrid : 0 < rGrid) (hr : 0 < r)
    (s : nd_Joint d rGrid) (hs : s ∈ nd_pseudoSet rGrid)
    (i : nd_DomainIndex d rGrid)
    (hsel : s ∈ nd_selectedEq rGrid r i.1.1 i.1.2)
    (havoid : Disjoint (nd_domain rGrid i) (lsph (0 : Rd d) (2 * r))) :
    0 < nd_crossPhi 0 (2 * r) r s.1 := by
  apply (nd_cross_pos_iff_zeroSet_disjoint_shell hd hr s hs).2
  exact havoid.mono_left (nd_zeroSet_subset_domain_of_selected hrGrid i s hsel)

theorem nd_cross_pos_iff_zeroSet_rev_disjoint_shell
    {rGrid r : ℝ} (hd : 0 < d) (hr : 0 < r)
    (s : nd_Joint d rGrid) (hs : s ∈ nd_pseudoSet rGrid) :
    0 < nd_crossPhi 0 (2 * r) r s.1 ↔
      Disjoint (nd_zeroSet (2 * r) s) (lsph (0 : Rd d) r) := by
  constructor
  · intro hcross
    exact ((nd_cross_pos_iff_disjoint_zeroSets hr hd hs).1 hcross).symm.mono_right
      (nd_sphere_subset_zeroSet r hs)
  · intro hdisj
    apply (nd_cross_pos_iff_disjoint_zeroSets hr hd hs).2
    rw [Set.disjoint_left] at hdisj ⊢
    intro x hx₁ hx₂
    obtain ⟨y₁, hy₁, hxy₁⟩ := (nd_zeroSet_mem_iff hr.le hd hs x).1 hx₁
    obtain ⟨y₂, hy₂, hxy₂⟩ :=
      (nd_zeroSet_mem_iff (by linarith : 0 ≤ 2 * r) hd hs x).1 hx₂
    have htri := hs.2.2.2 y₁ x y₂
    have hsym := hs.2.2.1 y₁ x
    rw [hsym, hxy₁, hxy₂] at htri
    have hzero : s.1 (y₁, y₂) = 0 :=
      le_antisymm (by linarith) (hs.2.1 y₁ y₂)
    have hy₁E : y₁ ∈ nd_zeroSet (2 * r) s :=
      (nd_zeroSet_mem_iff (by linarith : 0 ≤ 2 * r) hd hs y₁).2
        ⟨y₂, hy₂, hzero⟩
    exact hdisj hy₁E hy₁

theorem nd_cross_pos_of_selected_rev_avoids_shell
    {rGrid r : ℝ} (hd : 0 < d) (hrGrid : 0 < rGrid) (hr : 0 < r)
    (s : nd_Joint d rGrid) (hs : s ∈ nd_pseudoSet rGrid)
    (i : nd_DomainIndex d rGrid)
    (hsel : s ∈ nd_selectedEq rGrid (2 * r) i.1.1 i.1.2)
    (havoid : Disjoint (nd_domain rGrid i) (lsph (0 : Rd d) r)) :
    0 < nd_crossPhi 0 (2 * r) r s.1 := by
  apply (nd_cross_pos_iff_zeroSet_rev_disjoint_shell hd hr s hs).2
  exact havoid.mono_left (nd_zeroSet_subset_domain_of_selected hrGrid i s hsel)

end HigherDimLQGMetric.DGZ
