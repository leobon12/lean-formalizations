import SupercriticalLQGUniqueness.Uniqueness.Objects.CorrectedEvent.EventPredicate




 





set_option autoImplicit false
noncomputable section
open Set Metric

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Network
open SupercriticalLQGUniqueness.Uniqueness.Objects.CorrectedEvent

 

theorem reg_site_of_center_margin (C : Constants) (k : ℕ) (ε : ℝ)
    (z x : ℂ)
    (hGrid : x ∈ grid (lam k * C.r / 4))
    (hProtected : closedBall z (Real.sqrt ε * C.r) ⊆
      ann 0 C.r (4*C.r))
    (hMargin : 2 * 4 ^ (regK k) * lam k * C.r + dist x z ≤
      Real.sqrt ε * C.r) :
    x ∈ regSites C k := by
  refine ⟨hGrid, ?_⟩
  intro y hy
  have hyDisk : y ∈ ball z (Real.sqrt ε * C.r) :=
    ball_subset_ball' hMargin hy
  exact hProtected (ball_subset_closedBall hyDisk)


end SupercriticalLQGUniqueness.Uniqueness.Objects.Network
