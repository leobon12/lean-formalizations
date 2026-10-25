import SupercriticalLQGUniqueness.B2.DG20Lim.LowerSemi
import Mathlib.Topology.Order.LiminfLimsup

 




set_option autoImplicit false
noncomputable section

open Filter
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

 


theorem RData.le_liminf_of_circle_bounds (R : RData)
    (F : ℕ → ℂ × ℂ → ℝ≥0∞)
    (C : ℕ → RatCircle → RatCircle → ℝ≥0∞)
    (hconv : ∀ O P : RatCircle,
      Tendsto (fun n => C n O P) atTop (nhds (R.across O P)))
    (z w : ℂ) (zn wn : ℕ → ℂ)
    (hbound : ∀ O P : RatCircle, O.Surrounds z → P.Surrounds w →
      Disjoint O.closedDisk P.closedDisk →
      ∀ᶠ n in atTop, C n O P ≤ F n (zn n, wn n)) :
    R.DfromR z w ≤ liminf (fun n => F n (zn n, wn n)) atTop := by
  by_cases hzw : z = w
  · subst w
    simp only [R.DfromR_self]
    exact bot_le
  simp only [RData.DfromR, hzw, ↓reduceIte]
  apply iSup_le; intro O
  apply iSup_le; intro hO
  apply iSup_le; intro P
  apply iSup_le; intro hP
  apply iSup_le; intro hdisj
  calc
    R.across O P = liminf (fun n => C n O P) atTop :=
      (hconv O P).liminf_eq.symm
    _ ≤ liminf (fun n => F n (zn n, wn n)) atTop :=
      Filter.liminf_le_liminf (hbound O P hO hP hdisj)

end SupercriticalLQGUniqueness.B2.DG20Lim
