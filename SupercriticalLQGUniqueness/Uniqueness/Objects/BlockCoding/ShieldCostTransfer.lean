import SupercriticalLQGUniqueness.Uniqueness.Objects.BlockCoding.ShieldAcrPos
import SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.EqualNormalizer.WeylMonotone




 


set_option autoImplicit false
noncomputable section
open Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BlockCoding

theorem around_le_mul_of_pointwise (D E : LSCMetric) (C : ℝ) (hC : 0 < C)
    (h : ∀ p : ℂ × ℂ, E p ≤ ENNReal.ofReal C * D p)
    (z : ℂ) (a b : ℝ) :
    Objects.CorrectedEvent.around E z a b ≤ ENNReal.ofReal C * Objects.CorrectedEvent.around D z a b := by
  have hc0 : ENNReal.ofReal C ≠ 0 := (ENNReal.ofReal_pos.mpr hC).ne'
  have hcTop : ENNReal.ofReal C ≠ ∞ := ENNReal.ofReal_ne_top
  unfold Objects.CorrectedEvent.around
  simp only [ENNReal.mul_iInf_of_ne hc0 hcTop]
  refine le_iInf fun P => le_iInf fun s => le_iInf fun t =>
    le_iInf fun hP => le_iInf fun htrace => le_iInf fun hdis => ?_
  have hEP := BiLipschitz.EqualNormalizer.isCurve_of_pointwise_le D E C hC.le h P s t hP
  calc
    _ ≤ E.len P s t := by
      apply iInf_le_of_le P
      apply iInf_le_of_le s
      apply iInf_le_of_le t
      apply iInf_le_of_le hEP
      apply iInf_le_of_le htrace
      exact iInf_le_of_le hdis le_rfl
    _ ≤ _ := BiLipschitz.EqualNormalizer.len_le_mul_of_pointwise D E C hC.le h P s t

theorem acr_le_mul_of_pointwise (D E : LSCMetric) (C : ℝ) (hC : 0 < C)
    (h : ∀ p : ℂ × ℂ, E p ≤ ENNReal.ofReal C * D p)
    (z : ℂ) (a b : ℝ) :
    Objects.CorrectedEvent.acr E z a b ≤ ENNReal.ofReal C * Objects.CorrectedEvent.acr D z a b := by
  have hc0 : ENNReal.ofReal C ≠ 0 := (ENNReal.ofReal_pos.mpr hC).ne'
  have hcTop : ENNReal.ofReal C ≠ ∞ := ENNReal.ofReal_ne_top
  unfold Objects.CorrectedEvent.acr
  simp only [ENNReal.mul_iInf_of_ne hc0 hcTop]
  refine le_iInf fun P => le_iInf fun s => le_iInf fun t =>
    le_iInf fun hP => le_iInf fun htrace => le_iInf fun ha =>
      le_iInf fun hb => ?_
  have hEP := BiLipschitz.EqualNormalizer.isCurve_of_pointwise_le D E C hC.le h P s t hP
  calc
    _ ≤ E.len P s t := by
      apply iInf_le_of_le P
      apply iInf_le_of_le s
      apply iInf_le_of_le t
      apply iInf_le_of_le hEP
      apply iInf_le_of_le htrace
      apply iInf_le_of_le ha
      exact iInf_le_of_le hb le_rfl
    _ ≤ _ := BiLipschitz.EqualNormalizer.len_le_mul_of_pointwise D E C hC.le h P s t

end SupercriticalLQGUniqueness.Uniqueness.Objects.BlockCoding
