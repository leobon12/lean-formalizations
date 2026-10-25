import SupercriticalLQGUniqueness.Uniqueness.Objects.Shield.ShieldGeoForward
import SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.EqualNormalizer.WeylMonotone




set_option autoImplicit false
noncomputable section
open Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Shield

 
theorem internal_le_mul_of_pointwise
    (D E : LSCMetric) (C : ℝ) (hC : 0 < C)
    (h : ∀ p : ℂ × ℂ, E p ≤ ENNReal.ofReal C * D p)
    (K : Set ℂ) (u v : K) :
    E.internal K (u, v) ≤ ENNReal.ofReal C * D.internal K (u, v) := by
  have hc0 : ENNReal.ofReal C ≠ 0 := (ENNReal.ofReal_pos.mpr hC).ne'
  have hcTop : ENNReal.ofReal C ≠ ∞ := ENNReal.ofReal_ne_top
  unfold LSCMetric.internal
  simp only [ENNReal.mul_iInf_of_ne hc0 hcTop]
  refine le_iInf fun P => le_iInf fun a => le_iInf fun b =>
    le_iInf fun hP => le_iInf fun htrace => le_iInf fun hu =>
      le_iInf fun hv => ?_
  have hEP := BiLipschitz.EqualNormalizer.isCurve_of_pointwise_le D E C hC.le h P a b hP
  have hlen := BiLipschitz.EqualNormalizer.len_le_mul_of_pointwise D E C hC.le h P a b
  calc
    _ ≤ E.len P a b := by
      apply iInf_le_of_le P
      apply iInf_le_of_le a
      apply iInf_le_of_le b
      apply iInf_le_of_le hEP
      apply iInf_le_of_le htrace
      apply iInf_le_of_le hu
      exact iInf_le_of_le hv le_rfl
    _ ≤ _ := hlen

end SupercriticalLQGUniqueness.Uniqueness.Objects.Shield
