import SupercriticalLQGUniqueness.B2.DG20Lim.NonconcentricDisconnect
import SupercriticalLQGUniqueness.B2.DG20Lim.RData
import LQGMetric.Papers.GM.S3.AttainedShortcut

 


set_option autoImplicit false
noncomputable section

open Set

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem RatAnnulus.around_disconnects_opposite_sides
    (A : RatAnnulus) (O O' : RatCircle) (X : Set ℂ)
    (hOpp : A.OppositeSides O O')
    (hX : LQGMetric.Disconnects X A.inner.toSet A.outer.toSet) :
    LQGMetric.Disconnects X O.toSet O'.toSet := by
  have hnest : A.inner.closedDisk ⊆ A.outer.openDisk := A.nested.2
  have h := disconnects_nested_closedBall_compl_ball hnest hX
  rcases hOpp with ⟨hO, hO'⟩ | ⟨hO', hO⟩
  · exact h.mono Subset.rfl hO hO'
  · exact h.symm.mono Subset.rfl hO hO'

 


theorem RatAnnulus.exists_hit_around_of_opposite_sides
    (A : RatAnnulus) (O O' : RatCircle)
    (hOpp : A.OppositeSides O O')
    {P : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hP : ContinuousOn P (Icc a b))
    (ha : P a ∈ O.toSet) (hb : P b ∈ O'.toSet)
    {X : Set ℂ}
    (hX : LQGMetric.Disconnects X A.inner.toSet A.outer.toSet) :
    ∃ t ∈ Icc a b, P t ∈ X := by
  exact LQGMetric.GM.exists_hit_of_disconnects hab hP
    (A.around_disconnects_opposite_sides O O' X hOpp hX) ha hb

end SupercriticalLQGUniqueness.B2.DG20Lim
