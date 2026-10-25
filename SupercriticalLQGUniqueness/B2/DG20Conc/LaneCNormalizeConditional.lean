import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCNormalizeRatio

 
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace SupercriticalLQGUniqueness.B2.DG20Conc

 

theorem laneC_normalize_conditional_product
    {Ω : Type*} [MeasurableSpace Ω] (κ : Measure Ω)
    {a p : ℝ} (ha : 0 < a) (hp : 0 ≤ p)
    (L : Ω → ℝ) (hL : ∀ x, 0 < L x) (D : Ω → ℝ≥0∞) :
    (ENNReal.ofReal a ^ p)⁻¹ *
      (∫⁻ x, ENNReal.ofReal (a / L x) ^ p * D x ^ p ∂κ) =
        ∫⁻ x, ENNReal.ofReal ((L x)⁻¹) ^ p * D x ^ p ∂κ := by
  have hcTop : (ENNReal.ofReal a ^ p)⁻¹ ≠ ⊤ := by
    exact ENNReal.inv_ne_top.mpr
      (ne_of_gt (ENNReal.rpow_pos_of_nonneg (ENNReal.ofReal_pos.mpr ha) hp))
  rw [← lintegral_const_mul' _ _ hcTop]
  congr 1
  funext x
  rw [← mul_assoc, laneC_normalize_positive_ratio ha (hL x) hp]

end SupercriticalLQGUniqueness.B2.DG20Conc
