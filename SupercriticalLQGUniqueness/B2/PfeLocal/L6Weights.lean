import SupercriticalLQGUniqueness.B2.PfeLocal.L6Port

 












set_option autoImplicit false
noncomputable section

open Set Metric TopologicalSpace

namespace SupercriticalLQGUniqueness.B2.PfeLocal

 
abbrev L6K (R : ℝ) : Type := closedBall (0 : ℂ) R

 
def l6Res (R : ℝ) (f : C(ℂ, ℝ)) : C(L6K R, ℝ) := f.restrict (closedBall (0 : ℂ) R)

theorem continuous_l6Res (R : ℝ) : Continuous (l6Res R) := ContinuousMap.continuous_restrict _

theorem l6Res_apply (R : ℝ) (f : C(ℂ, ℝ)) (x : L6K R) : l6Res R f x = f x := rfl

 
def l6W (R : ℝ) (j : ℕ) : C(ℂ, ℝ) :=
  Classical.choose (ContinuousMap.exists_restrict_eq isClosed_closedBall
    (denseSeq C(L6K R, ℝ) j))

theorem l6Res_l6W (R : ℝ) (j : ℕ) : l6Res R (l6W R j) = denseSeq C(L6K R, ℝ) j :=
  Classical.choose_spec (ContinuousMap.exists_restrict_eq isClosed_closedBall
    (denseSeq C(L6K R, ℝ) j))

 
theorem l6_exists_weight (R : ℝ) (u : C(L6K R, ℝ)) {η : ℝ} (hη : 0 < η) :
    ∃ j, ‖l6Res R (l6W R j) - u‖ < η := by
  obtain ⟨j, hj⟩ := Metric.denseRange_iff.1 (denseRange_denseSeq C(L6K R, ℝ)) u η hη
  refine ⟨j, ?_⟩
  rw [l6Res_l6W, ← dist_eq_norm, dist_comm]
  exact hj

 
theorem l6_abs_le_norm_res {R : ℝ} (f : C(ℂ, ℝ)) {x : ℂ} (hx : x ∈ closedBall (0 : ℂ) R) :
    |f x| ≤ ‖l6Res R f‖ := by
  have := ContinuousMap.norm_coe_le_norm (l6Res R f) ⟨x, hx⟩
  rwa [Real.norm_eq_abs, l6Res_apply] at this

end SupercriticalLQGUniqueness.B2.PfeLocal
