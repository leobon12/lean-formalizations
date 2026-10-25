import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCCornerPerturbLimit

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Metric
namespace SupercriticalLQGUniqueness.B2.DG20Conc
open LQGMetric LQGMetric.DDDF

 


theorem laneC_corner_arc_meets_crosser
    {α β : ℝ → ℂ}
    (hα : ContinuousOn α (Icc (0 : ℝ) 1))
    (hβ : ContinuousOn β (Icc (0 : ℝ) 1))
    (hαsq : ∀ t ∈ Icc (0 : ℝ) 1, α t ∈ (rectAB 1 1).toSet)
    (hβsq : ∀ t ∈ Icc (0 : ℝ) 1, β t ∈ (rectAB 1 1).toSet)
    (hαleft : (α 0).re = 0) (hαtop : (α 1).im = 1)
    (hβleft : (β 0).re = 0) (hβright : (β 1).re = 1)
    (horder : (α 0).im < (β 0).im) :
    ∃ s ∈ Icc (0 : ℝ) 1, ∃ u ∈ Icc (0 : ℝ) 1,
      β s = α u := by
  apply laneC_inwardPerturb_meet_limit hα hβ
  intro ε hε hε1
  exact laneC_corner_arc_meets_inward_perturbation hα hβ
    hαsq hβsq hαleft hαtop hβleft hβright horder ⟨hε, hε1⟩

end SupercriticalLQGUniqueness.B2.DG20Conc
