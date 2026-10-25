import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCFirstLastHit
import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCSideSeparatorHit

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set LQGMetric
namespace SupercriticalLQGUniqueness.B2.DG20Conc

 

theorem laneC_last_separator_hit
    {X E F Fr : Set ℂ} (hXclosed : IsClosed X)
    (hsep : LQGMetric.Disconnects X E F) (hXFr : X ⊆ Fr)
    {γ : ℝ → ℂ} (hγ : ContinuousOn γ (Icc (0 : ℝ) 1))
    {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1)
    (hmid : γ m ∈ E) (hend : γ 1 ∈ F)
    (hbad : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∉ Fr → γ t ∈ E) :
    ∃ t₁ ∈ Icc m (1 : ℝ), γ t₁ ∈ X ∧
      ∀ t ∈ Icc t₁ (1 : ℝ), γ t ∈ Fr := by
  let T : Set ℝ := Icc m 1 ∩ γ ⁻¹' X
  have hsub : Icc m (1 : ℝ) ⊆ Icc 0 1 :=
    Icc_subset_Icc hm.1 le_rfl
  have hTc : IsCompact T :=
    isCompact_Icc.of_isClosed_subset
      ((hγ.mono hsub).preimage_isClosed_of_isClosed isClosed_Icc hXclosed)
      inter_subset_left
  have hTne : T.Nonempty := by
    obtain ⟨t, ht, hXt⟩ := laneC_separator_meets_subpath hsep hm.2
      (hγ.mono hsub) hmid hend
    exact ⟨t, ht, hXt⟩
  obtain ⟨t₁, ht₁, hmax⟩ := hTc.exists_isGreatest hTne
  refine ⟨t₁, ht₁.1, ht₁.2, ?_⟩
  intro t ht
  by_cases heq : t = t₁
  · rw [heq]; exact hXFr ht₁.2
  by_contra hnot
  have hlt : t₁ < t := lt_of_le_of_ne ht.1 (Ne.symm heq)
  have hE : γ t ∈ E := hbad t ⟨hm.1.trans (ht₁.1.1.trans ht.1), ht.2⟩ hnot
  obtain ⟨u, hu, hXu⟩ := laneC_separator_meets_subpath hsep ht.2
    (hγ.mono (Icc_subset_Icc (hm.1.trans (ht₁.1.1.trans ht.1)) le_rfl))
    hE hend
  have huT : u ∈ T := ⟨⟨ht₁.1.1.trans (ht.1.trans hu.1), hu.2⟩, hXu⟩
  exact (not_le_of_gt (hlt.trans_le hu.1)) (hmax huT)

 

theorem laneC_first_separator_hit
    {X E F Fr : Set ℂ} (hXclosed : IsClosed X)
    (hsep : LQGMetric.Disconnects X E F) (hXFr : X ⊆ Fr)
    {γ : ℝ → ℂ} (hγ : ContinuousOn γ (Icc (0 : ℝ) 1))
    {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1)
    (hstart : γ 0 ∈ F) (hmid : γ m ∈ E)
    (hbad : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∉ Fr → γ t ∈ E) :
    ∃ t₀ ∈ Icc (0 : ℝ) m, γ t₀ ∈ X ∧
      ∀ t ∈ Icc (0 : ℝ) t₀, γ t ∈ Fr := by
  let T : Set ℝ := Icc 0 m ∩ γ ⁻¹' X
  have hsub : Icc (0 : ℝ) m ⊆ Icc 0 1 :=
    Icc_subset_Icc le_rfl hm.2
  have hTc : IsCompact T :=
    isCompact_Icc.of_isClosed_subset
      ((hγ.mono hsub).preimage_isClosed_of_isClosed isClosed_Icc hXclosed)
      inter_subset_left
  have hTne : T.Nonempty := by
    obtain ⟨t, ht, hXt⟩ := laneC_separator_meets_subpath hsep.symm hm.1
      (hγ.mono hsub) hstart hmid
    exact ⟨t, ht, hXt⟩
  obtain ⟨t₀, ht₀, hmin⟩ := hTc.exists_isLeast hTne
  refine ⟨t₀, ht₀.1, ht₀.2, ?_⟩
  intro t ht
  by_cases heq : t = t₀
  · rw [heq]; exact hXFr ht₀.2
  by_contra hnot
  have hlt : t < t₀ := lt_of_le_of_ne ht.2 heq
  have hE : γ t ∈ E := hbad t ⟨ht.1, (ht.2.trans ht₀.1.2).trans hm.2⟩ hnot
  obtain ⟨u, hu, hXu⟩ := laneC_separator_meets_subpath hsep.symm ht.1
    (hγ.mono (Icc_subset_Icc le_rfl ((ht.2.trans ht₀.1.2).trans hm.2)))
    hstart hE
  have huT : u ∈ T := ⟨⟨hu.1, (hu.2.trans ht.2).trans ht₀.1.2⟩, hXu⟩
  exact (not_le_of_gt (hu.2.trans_lt hlt)) (hmin huT)

end SupercriticalLQGUniqueness.B2.DG20Conc
