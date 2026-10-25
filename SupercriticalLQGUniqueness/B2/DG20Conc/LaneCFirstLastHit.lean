import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCSeparatorHit

 








set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set LQGMetric

namespace SupercriticalLQGUniqueness.B2.DG20Conc

theorem laneC_first_last_separator_hits
    {X E F Fr : Set ℂ} (hXclosed : IsClosed X)
    (hsep : Disconnects X E F) (hXFr : X ⊆ Fr)
    {γ : ℝ → ℂ} (hγ : ContinuousOn γ (Icc (0 : ℝ) 1))
    {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1)
    (hstart : γ 0 ∈ F) (hmid : γ m ∈ E) (hend : γ 1 ∈ F)
    (hbad : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∉ Fr → γ t ∈ E) :
    ∃ t₀ ∈ Icc (0 : ℝ) m, ∃ t₁ ∈ Icc m (1 : ℝ),
      γ t₀ ∈ X ∧ γ t₁ ∈ X ∧
      (∀ t ∈ Icc (0 : ℝ) t₀, γ t ∈ Fr) ∧
      (∀ t ∈ Icc t₁ (1 : ℝ), γ t ∈ Fr) := by
  have hsub₀ : Icc (0 : ℝ) m ⊆ Icc 0 1 := Icc_subset_Icc le_rfl hm.2
  have hsub₁ : Icc m (1 : ℝ) ⊆ Icc 0 1 := Icc_subset_Icc hm.1 le_rfl
  let T₀ : Set ℝ := Icc 0 m ∩ γ ⁻¹' X
  let T₁ : Set ℝ := Icc m 1 ∩ γ ⁻¹' X
  have hT₀c : IsCompact T₀ :=
    isCompact_Icc.of_isClosed_subset
      ((hγ.mono hsub₀).preimage_isClosed_of_isClosed isClosed_Icc hXclosed)
      (inter_subset_left)
  have hT₁c : IsCompact T₁ :=
    isCompact_Icc.of_isClosed_subset
      ((hγ.mono hsub₁).preimage_isClosed_of_isClosed isClosed_Icc hXclosed)
      (inter_subset_left)
  have hT₀ne : T₀.Nonempty := by
    obtain ⟨t, ht, hXt⟩ := laneC_separator_meets_subpath hsep.symm hm.1
      (hγ.mono hsub₀) hstart hmid
    exact ⟨t, ht, hXt⟩
  have hT₁ne : T₁.Nonempty := by
    obtain ⟨t, ht, hXt⟩ := laneC_separator_meets_subpath hsep hm.2
      (hγ.mono hsub₁) hmid hend
    exact ⟨t, ht, hXt⟩
  obtain ⟨t₀, ht₀, hmin⟩ := hT₀c.exists_isLeast hT₀ne
  obtain ⟨t₁, ht₁, hmax⟩ := hT₁c.exists_isGreatest hT₁ne
  refine ⟨t₀, ht₀.1, t₁, ht₁.1, ht₀.2, ht₁.2, ?_, ?_⟩
  · intro t ht
    by_cases hEq : t = t₀
    · rw [hEq]; exact hXFr ht₀.2
    by_contra hnot
    have htlt : t < t₀ := lt_of_le_of_ne ht.2 hEq
    have hE : γ t ∈ E := hbad t ⟨ht.1, (ht.2.trans ht₀.1.2).trans hm.2⟩ hnot
    obtain ⟨u, hu, hXu⟩ := laneC_separator_meets_subpath hsep.symm ht.1
      (hγ.mono (Icc_subset_Icc le_rfl ((ht.2.trans ht₀.1.2).trans hm.2))) hstart hE
    have htu : u ∈ T₀ := ⟨⟨hu.1, (hu.2.trans ht.2).trans ht₀.1.2⟩, hXu⟩
    exact (not_le_of_gt (hu.2.trans_lt htlt)) (hmin htu)
  · intro t ht
    by_cases hEq : t = t₁
    · rw [hEq]; exact hXFr ht₁.2
    by_contra hnot
    have htlt : t₁ < t := lt_of_le_of_ne ht.1 (Ne.symm hEq)
    have hE : γ t ∈ E := hbad t ⟨hm.1.trans (ht₁.1.1.trans ht.1), ht.2⟩ hnot
    obtain ⟨u, hu, hXu⟩ := laneC_separator_meets_subpath hsep ht.2
      (hγ.mono (Icc_subset_Icc (hm.1.trans (ht₁.1.1.trans ht.1)) le_rfl)) hE hend
    have htu : u ∈ T₁ := ⟨⟨ht₁.1.1.trans (ht.1.trans hu.1), hu.2⟩, hXu⟩
    exact (not_le_of_gt (htlt.trans_le hu.1)) (hmax htu)

end SupercriticalLQGUniqueness.B2.DG20Conc
