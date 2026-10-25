import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCMaxScaleL2

 
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace SupercriticalLQGUniqueness.B2.DG20Conc

 

theorem laneC_normalize_positive_ratio
    {a l p : ℝ} (ha : 0 < a) (hl : 0 < l) (hp : 0 ≤ p) :
    (ENNReal.ofReal a ^ p)⁻¹ * (ENNReal.ofReal (a / l) ^ p) =
      ENNReal.ofReal (l⁻¹) ^ p := by
  have ha0 : ENNReal.ofReal a ^ p ≠ 0 := by
    exact ne_of_gt (ENNReal.rpow_pos_of_nonneg (ENNReal.ofReal_pos.mpr ha) hp)
  have haTop : ENNReal.ofReal a ^ p ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg hp ENNReal.ofReal_ne_top
  rw [div_eq_mul_inv, ENNReal.ofReal_mul' (inv_nonneg.mpr hl.le),
    ENNReal.mul_rpow_of_nonneg _ _ hp]
  rw [ENNReal.inv_mul_cancel_left ha0 haTop]

end SupercriticalLQGUniqueness.B2.DG20Conc
