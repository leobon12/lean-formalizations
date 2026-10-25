import SupercriticalLQGUniqueness.B2.DG20Lim.Geometry

 




set_option autoImplicit false
noncomputable section

open Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

 
def RatCircle.point (x y : ℚ) : RatCircle := ⟨x, y, 0, le_refl 0⟩

@[simp] theorem RatCircle.point_radius (x y : ℚ) :
    (RatCircle.point x y).radius = 0 := rfl

 
theorem RatCircle.toSet_eq_singleton_of_radius_zero
    (Z : RatCircle) (hZ : Z.radius = 0) : Z.toSet = {Z.center} := by
  simp [RatCircle.toSet, hZ]

theorem RatCircle.closedDisk_eq_singleton_of_radius_zero
    (Z : RatCircle) (hZ : Z.radius = 0) : Z.closedDisk = {Z.center} := by
  simp [RatCircle.closedDisk, hZ]

 

theorem RatCircle.surroundsCircle_zero
    (O Z : RatCircle) (hZ : Z.radius = 0) (hO : O.Surrounds Z.center) :
    O.SurroundsCircle Z := by
  refine ⟨hO.1, ?_⟩
  rw [Z.closedDisk_eq_singleton_of_radius_zero hZ]
  exact singleton_subset_iff.mpr hO.2

 

theorem RData.DfromR_le_across_zero (R : RData) (Z W : RatCircle)
    (hZ : Z.radius = 0) (hW : W.radius = 0) :
    R.DfromR Z.center W.center ≤ R.across Z W := by
  by_cases hzw : Z.center = W.center
  · rw [hzw, R.DfromR_self]
    exact zero_le
  simp only [RData.DfromR, hzw, ↓reduceIte]
  apply iSup_le; intro O
  apply iSup_le; intro hO
  apply iSup_le; intro P
  apply iSup_le; intro hP
  apply iSup_le; intro hdisj
  exact R.across_outer_le_inner_of_nested Z O P W
    (O.surroundsCircle_zero Z hZ hO)
    (P.surroundsCircle_zero W hW hP) hdisj

end SupercriticalLQGUniqueness.B2.DG20Lim
