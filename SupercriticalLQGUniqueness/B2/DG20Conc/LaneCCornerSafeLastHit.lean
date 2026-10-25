import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCCornerSuffixHit

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Metric
namespace SupercriticalLQGUniqueness.B2.DG20Conc
open LQGMetric LQGMetric.DDDF

theorem laneC_corner_crosscut_last_safe_hit
    {α γ : ℝ → ℂ} {c : ℂ} {r m : ℝ}
    (hα : ContinuousOn α (Icc (0 : ℝ) 1))
    (hγ : ContinuousOn γ (Icc (0 : ℝ) 1))
    (hαsq : ∀ t ∈ Icc (0 : ℝ) 1, α t ∈ (rectAB 1 1).toSet)
    (hγsq : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ (rectAB 1 1).toSet)
    (hαann : ∀ t ∈ Icc (0 : ℝ) 1, r < dist (α t) c)
    (hαleft : (α 0).re = 0) (hαtop : (α 1).im = 1)
    (hαbelow : (α 0).im < c.im)
    (hγright : (γ 1).re = 1)
    (hm : m ∈ Icc (0 : ℝ) 1) (hvisit : dist (γ m) c ≤ r)
    (hcre0 : 0 ≤ c.re) (hcreNear : c.re ≤ r)
    (hcim0 : 0 ≤ c.im) (hcim1 : c.im ≤ 1) :
    ∃ t₁ ∈ Icc m (1 : ℝ), ∃ u ∈ Icc (0 : ℝ) 1,
      γ t₁ = α u ∧
      ∀ t ∈ Icc t₁ (1 : ℝ), r ≤ dist (γ t) c := by
  let X : Set ℂ := α '' Icc (0 : ℝ) 1
  let T : Set ℝ := Icc m 1 ∩ γ ⁻¹' X
  have hαclosed : IsClosed X :=
    (isCompact_Icc.image_of_continuousOn hα).isClosed
  have hsub : Icc m (1 : ℝ) ⊆ Icc 0 1 :=
    Icc_subset_Icc hm.1 le_rfl
  have hTc : IsCompact T :=
    isCompact_Icc.of_isClosed_subset
      ((hγ.mono hsub).preimage_isClosed_of_isClosed isClosed_Icc hαclosed)
      inter_subset_left
  have hTne : T.Nonempty := by
    obtain ⟨t, ht, u, hu, heq⟩ :=
      laneC_corner_crosscut_hits_suffix hα hγ hαsq hγsq
        hαann hαleft hαtop hαbelow hγright hm hvisit
        hcre0 hcreNear hcim0 hcim1
    exact ⟨t, ht, u, hu, heq.symm⟩
  obtain ⟨t₁, ht₁, hmax⟩ := hTc.exists_isGreatest hTne
  obtain ⟨u, hu, hhit⟩ := ht₁.2
  refine ⟨t₁, ht₁.1, u, hu, hhit.symm, ?_⟩
  intro t ht
  by_contra hbad
  have hinner : dist (γ t) c ≤ r := le_of_not_ge hbad
  have htm : t ∈ Icc (0 : ℝ) 1 :=
    ⟨hm.1.trans (ht₁.1.1.trans ht.1), ht.2⟩
  obtain ⟨v, hv, w, hw, heq⟩ :=
    laneC_corner_crosscut_hits_suffix hα hγ hαsq hγsq
      hαann hαleft hαtop hαbelow hγright htm hinner
      hcre0 hcreNear hcim0 hcim1
  have hvT : v ∈ T := ⟨⟨ht₁.1.1.trans (ht.1.trans hv.1), hv.2⟩,
    ⟨w, hw, heq.symm⟩⟩
  have hstrict : t₁ < t := lt_of_le_of_ne ht.1 (by
    intro heq'
    subst t
    have hαr := hαann u hu
    rw [← hhit] at hinner
    exact (not_le_of_gt hαr) hinner)
  exact (not_le_of_gt (hstrict.trans_le hv.1)) (hmax hvT)

end SupercriticalLQGUniqueness.B2.DG20Conc
