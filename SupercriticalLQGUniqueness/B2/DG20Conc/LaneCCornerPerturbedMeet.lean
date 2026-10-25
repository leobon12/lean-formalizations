import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCCornerInwardPerturb

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Metric
namespace SupercriticalLQGUniqueness.B2.DG20Conc
open LQGMetric LQGMetric.DDDF

theorem laneC_corner_arc_meets_inward_perturbation
    {α β : ℝ → ℂ}
    (hα : ContinuousOn α (Icc (0 : ℝ) 1))
    (hβ : ContinuousOn β (Icc (0 : ℝ) 1))
    (hαsq : ∀ t ∈ Icc (0 : ℝ) 1, α t ∈ (rectAB 1 1).toSet)
    (hβsq : ∀ t ∈ Icc (0 : ℝ) 1, β t ∈ (rectAB 1 1).toSet)
    (hαleft : (α 0).re = 0) (hαtop : (α 1).im = 1)
    (hβleft : (β 0).re = 0) (hβright : (β 1).re = 1)
    (horder : (α 0).im < (β 0).im)
    {ε : ℝ} (hε : 0 < ε ∧ ε ≤ 1) :
    ∃ s ∈ Icc (0 : ℝ) 1, ∃ u ∈ Icc (0 : ℝ) 1,
      laneCInwardPerturb β ε s = α u := by
  have hends := laneC_inwardPerturb_ends β ε
  apply laneC_corner_arc_meets_positive_crosser hα
    (laneC_inwardPerturb_continuous hβ ε)
    hαsq (laneC_inwardPerturb_square hβsq hε)
    hαleft hαtop
    (by rw [hends.1]; exact hβleft)
    (by rw [hends.2]; exact hβright)
    (by rw [hends.1]; exact horder)
  intro t ht ht0
  by_cases ht1 : t = 1
  · subst t
    rw [hends.2, hβright]
    norm_num
  · exact laneC_inwardPerturb_positive_re hβsq hε ht ht0 ht1

end SupercriticalLQGUniqueness.B2.DG20Conc
