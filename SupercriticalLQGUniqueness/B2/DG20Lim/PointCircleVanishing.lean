import SupercriticalLQGUniqueness.B2.DG20Lim.PointCircleChain
import SupercriticalLQGUniqueness.B2.DG20Lim.OffCircle

 


set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem RData.across_point_circle_tendsto_zero_of_small_points
    (R : RData) (Z : RatCircle) (hZ : Z.radius = 0)
    (hsmall : ∀ δ : ℝ≥0∞, 0 < δ →
      ∃ Q : RatCircle, Q.radius = 0 ∧ Q.center ≠ Z.center ∧
        R.across Z Q < δ)
    (O : ℕ → RatCircle)
    (hO : ∀ᶠ n in atTop, (O n).Surrounds Z.center)
    (hrad : Tendsto (fun n => ((O n).radius : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => R.across Z (O n)) atTop (𝓝 0) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    exact (not_lt_of_ge (show 0 ≤ a from zero_le) ha).elim
  · intro b hb
    obtain ⟨Q, hQ, hQne, hQsmall⟩ := hsmall b hb
    have hOpen : Z.center ∈ ({Q.center} : Set ℂ)ᶜ := by
      simpa using (Ne.symm hQne)
    have hout : ∀ᶠ n in atTop, Q.center ∉ (O n).closedDisk := by
      have hev := RatCircle.eventually_closedDisk_subset_open
        isClosed_singleton.isOpen_compl hOpen O hO hrad
      filter_upwards [hev] with n hn hQin
      exact (hn hQin) (by simp)
    filter_upwards [hO, hout] with n hnO hnOut
    exact (R.across_point_circle_le_point Z (O n) Q hZ hQ hnO hnOut).trans_lt
      hQsmall

end SupercriticalLQGUniqueness.B2.DG20Lim
