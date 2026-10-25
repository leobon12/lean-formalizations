import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCCornerInnerConnector

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Metric
namespace SupercriticalLQGUniqueness.B2.DG20Conc
open LQGMetric LQGMetric.DDDF

 


theorem laneC_corner_crosscut_hits_suffix
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
    ∃ t ∈ Icc m 1, ∃ u ∈ Icc (0 : ℝ) 1,
      γ t = α u := by
  let β := laneCInnerConnector c γ m
  have hβ := laneC_innerConnector_continuous (c := c) hγ hm
  have hβsq := laneC_innerConnector_square (c := c) hγsq hm hcim0 hcim1
  obtain ⟨s, hs, u, hu, hmeet⟩ :=
    laneC_corner_arc_meets_crosser hα hβ hαsq hβsq
      hαleft hαtop
      (by rw [(laneC_innerConnector_ends c γ m).1]; rfl)
      (by rw [(laneC_innerConnector_ends c γ m).2]; exact hγright)
      (by rw [(laneC_innerConnector_ends c γ m).1]
          exact hαbelow)
  rcases laneC_innerConnector_trace hm hcre0 hcreNear hvisit s hs with
    hball | ⟨t, ht, htrace⟩
  · have hαr := hαann u hu
    rw [hmeet] at hball
    exact False.elim (not_lt_of_ge hball hαr)
  · exact ⟨t, ht, u, hu, htrace.symm.trans hmeet⟩

end SupercriticalLQGUniqueness.B2.DG20Conc
