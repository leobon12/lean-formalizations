import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCSideToInnerHit

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set LQGMetric
namespace SupercriticalLQGUniqueness.B2.DG20Conc

 

theorem laneC_first_separator_hit_of_side_path
    {X E F Fr S : Set ℂ} (hXclosed : IsClosed X)
    (hsep : LQGMetric.Disconnects X E F) (hXFr : X ⊆ Fr)
    (hno : X ∩ S = ∅)
    {y : ℂ} (hyF : y ∈ F)
    {γ : ℝ → ℂ} (hside : Path y (γ 0))
    (hsideS : ∀ t, hside t ∈ S)
    (hγ : ContinuousOn γ (Icc (0 : ℝ) 1))
    {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1)
    (hmid : γ m ∈ E)
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
    obtain ⟨t, ht, hXt⟩ := laneC_separator_hits_prefix_of_side_path
      hsep hno hyF hside hsideS hm hγ hmid
    exact ⟨t, ht, hXt⟩
  obtain ⟨t₀, ht₀, hmin⟩ := hTc.exists_isLeast hTne
  refine ⟨t₀, ht₀.1, ht₀.2, ?_⟩
  intro t ht
  by_cases heq : t = t₀
  · rw [heq]
    exact hXFr ht₀.2
  by_contra hnot
  have hlt : t < t₀ := lt_of_le_of_ne ht.2 heq
  have htg : t ∈ Icc (0 : ℝ) 1 :=
    ⟨ht.1, (ht.2.trans ht₀.1.2).trans hm.2⟩
  have hE : γ t ∈ E := hbad t htg hnot
  obtain ⟨u, hu, hXu⟩ := laneC_separator_hits_prefix_of_side_path
    hsep hno hyF hside hsideS htg hγ hE
  have huT : u ∈ T :=
    ⟨⟨hu.1, (hu.2.trans ht.2).trans ht₀.1.2⟩, hXu⟩
  exact (not_le_of_gt (hu.2.trans_lt hlt)) (hmin huT)

end SupercriticalLQGUniqueness.B2.DG20Conc
