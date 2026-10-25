import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCNoRightSuffix

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set LQGMetric
namespace SupercriticalLQGUniqueness.B2.DG20Conc

 

theorem laneC_last_separator_hit_of_side_path
    {X E F Fr S : Set ℂ} (hXclosed : IsClosed X)
    (hsep : LQGMetric.Disconnects X E F) (hXFr : X ⊆ Fr)
    (hno : X ∩ S = ∅)
    {y : ℂ} (hyF : y ∈ F)
    {γ : ℝ → ℂ} (hside : Path (γ 1) y)
    (hsideS : ∀ t, hside t ∈ S)
    (hγ : ContinuousOn γ (Icc (0 : ℝ) 1))
    {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1)
    (hmid : γ m ∈ E)
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
    obtain ⟨t, ht, hXt⟩ := laneC_separator_hits_suffix_of_side_path
      hsep hno hyF hside hsideS hm hγ hmid
    exact ⟨t, ht, hXt⟩
  obtain ⟨t₁, ht₁, hmax⟩ := hTc.exists_isGreatest hTne
  refine ⟨t₁, ht₁.1, ht₁.2, ?_⟩
  intro t ht
  by_cases heq : t = t₁
  · rw [heq]
    exact hXFr ht₁.2
  by_contra hnot
  have hlt : t₁ < t := lt_of_le_of_ne ht.1 (Ne.symm heq)
  have htg : t ∈ Icc (0 : ℝ) 1 :=
    ⟨hm.1.trans (ht₁.1.1.trans ht.1), ht.2⟩
  have hE : γ t ∈ E := hbad t htg hnot
  obtain ⟨u, hu, hXu⟩ := laneC_separator_hits_suffix_of_side_path
    hsep hno hyF hside hsideS htg hγ hE
  have huT : u ∈ T :=
    ⟨⟨ht₁.1.1.trans (ht.1.trans hu.1), hu.2⟩, hXu⟩
  exact (not_le_of_gt (hlt.trans_le hu.1)) (hmax huT)

end SupercriticalLQGUniqueness.B2.DG20Conc
